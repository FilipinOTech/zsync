
/*
 *   zsync - client side rsync over http
 *   Copyright (C) 2004,2005,2007,2009 Colin Phipps <cph@moria.org.uk>
 *
 *   This program is free software; you can redistribute it and/or modify
 *   it under the terms of the Artistic License v2 (see the accompanying 
 *   file COPYING for the full license terms), or, at your option, any later 
 *   version of the same license.
 *
 *   This program is distributed in the hope that it will be useful,
 *   but WITHOUT ANY WARRANTY; without even the implied warranty of
 *   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *   COPYING file for details.
 */

/* HTTP client code for zsync.
 * Including pipeline HTTP Range fetching code.  */

#include "zsglobal.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <unistd.h>

#include <sys/types.h>
#include <sys/stat.h>
#include <sys/socket.h>
#include <netdb.h>
#include <time.h>

#ifndef HAVE_GETADDRINFO
#include "getaddrinfo.h"
#endif

#ifdef WITH_DMALLOC
# include <dmalloc.h>
#endif

#include "http.h"
#include "url.h"
#include "progress.h"
#include "format_string.h"
#include "libzsync/zsync.h"

#include <curl/curl.h>

/* socket = connect_to(host, service/port)
 * Establishes a TCP connection to the named host and port (which can be
 * supplied as a service name from /etc/services. Returns the socket handle, or
 * -1 on error. */
int connect_to(const char *node, const char *service) {
    struct addrinfo hint;
    struct addrinfo *ai;
    int rc;

/* Settings for HTTP connections - auth details */
    memset(&hint, 0, sizeof hint);
    hint.ai_family = AF_UNSPEC;
    hint.ai_socktype = SOCK_STREAM;

    if ((rc = getaddrinfo(node, service, &hint, &ai)) != 0) {
        perror(node);
        return -1;
    }
    else {
        struct addrinfo *p;
        int sd = -1;

        for (p = ai; sd == -1 && p != NULL; p = p->ai_next) {
            if ((sd =
                 socket(p->ai_family, p->ai_socktype, p->ai_protocol)) == -1) {
                perror("socket");
            }
            else if (connect(sd, p->ai_addr, p->ai_addrlen) < 0) {
                perror(node);
                close(sd);
                sd = -1;
            }
        }
        freeaddrinfo(ai);
        return sd;
    }
}

/* url = get_location_url(stream, current_url)
 * Reads the HTTP response from the given stream and extracts the Location
 * header, making this URL absolute using the current URL. Returned as a
 * malloced string.
 * (it ought to be absolute anyway, by the RFC, but many servers send 
 * relative URIs). */
char *get_location_url(FILE * f, const char *cur_url) {
    char buf[1024];

    while (fgets(buf, sizeof(buf), f)) {
        char *p;

        /* exit if end of headers */
        if (buf[0] == '\r' || buf[0] == '\n')
            return NULL;

        /* Look for Location header */
        p = strchr(buf, ':');
        if (!p)
            return NULL;
        *p++ = 0;
        if (strcasecmp(buf, "Location"))
            continue;

        /* Skip leading whitespace */
        while (*p == ' ')
            p++;

        {   /* Remove trailing whitespace */
            char *q = p;
            while (*q != '\r' && *q != '\n' && *q != ' ' && *q)
                q++;
            *q = 0;
        }
        if (!*p)
            return NULL;

        /* Return URL after making absolute */
        return make_url_absolute(cur_url, p);
    }
    return NULL;                // TODO
}

/* Settings for HTTP connections - proxy host and port, auth details */
static char *proxy;
static char *pport;
static char **auth_details; /* This is a realloced array with 3*num_auth_details entries */
static int num_auth_details; /* The groups of 3 strings are host, user, pass */

/* Remember .zsync control file URL */
char *referer;

/* set_proxy_from_string(str)
 * Sets the proxy settings for HTTP connections to use; these can be either as
 * a host[:port] or as http://host[:port].
 * Returns non-zero if the settings were obtained successfully. */
int set_proxy_from_string(const char *s) {
    if (!memcmp(s, http_scheme, strlen(http_scheme))) {
        /* http:// style proxy string */
        proxy = malloc(256);
        if (!proxy)
            return 0;
        if (!get_http_host_port(s, proxy, 256, &pport))
            return 0;
        if (!pport) {
            pport = strdup("webcache");
        }
        return 1;
    }
    else {
        /* host:port style proxy string; have to parse this ourselves */
        char *p;
        proxy = strdup(s);
        p = strchr(proxy, ':');
        if (!p) {
            pport = strdup("webcache");
            return 1;
        }
        *p++ = 0;
        pport = strdup(p);
        return 1;
    }
}

/* Should we tell curl to use a different CA path? */
char *cacert = NULL;

/* Should we tell curl to use a particular interface (or IP or hostname)? */
char *want_interface = NULL;

/* Should we tell curl to use a particular SSL public / private cert? */
char *sslcert = NULL;
char *sslkey = NULL;

/* Should we tell curl to ignore SSL peer verification? */
int be_insecure = 0;

/* Should we tell curl to be verbose? */
int be_verbose = 0;

/* Should we tell curl to set a timeout? */
long use_timeout = 0;

/* Declare up here so we can use it in make_curl_handle */
int range_fetch_sockoptcallback( void *clientp, curl_socket_t curlfd, curlsocktype purpose );

/* add_auth(host, user, pass)
 * Specify user & password combination to use connecting to the given host.
 */
void add_auth(char *host, char *user, char *pass) {
    auth_details =
        realloc(auth_details, (num_auth_details + 1) * sizeof *auth_details);
    auth_details[num_auth_details * 3] = host;
    auth_details[num_auth_details * 3 + 1] = user;
    auth_details[num_auth_details * 3 + 2] = pass;
    num_auth_details++;
}

/* str = get_auth_hdr(host)
 * For the given host, returns the extra HTTP header(s) that should be included
 * to provide authentication information. Returned as a malloced string.
 */
const char auth_header_tmpl[] = { "Authorization: Basic %s\r\n" };

static char *get_auth_hdr(const char *hn) {
    /* Find any relevant entry in the auth table */
    int i;
    for (i = 0; i < num_auth_details * 3; i += 3) {
        if (!strcasecmp(auth_details[i], hn)) {
            char *b;
            char *header;

            /* We have found an entry in the auth details table for this
             * hostname; get the user & pass to use */
            char *u = auth_details[i + 1];
            char *p = auth_details[i + 2];

            /* Store unencoded user:pass */
            size_t l = strlen(u) + strlen(p) + 2;
            char *w = malloc(l);
            snprintf(w, l, "%s:%s", u, p);

            /* Now base64-encode that, and compose the header */
            b = base64(w);
            l = strlen(b) + strlen(auth_header_tmpl) + 1;
            header = malloc(l);
            snprintf(header, l, auth_header_tmpl, b);

            /* And clean up */
            free(w);
            free(b);
            return header;
        }
    }
    return NULL;
}


/* Get a curl easy handle based on our global options. Returns NULL on failure */
CURL *make_curl_handle() {
    CURL *curl;
    CURLcode res;

    curl = curl_easy_init();
    if( !curl ) {
        fprintf(stderr, "curl init failed miserably\n");
        return NULL;
    }

    /* Set options. Only check error codes if we care if they fail. */

    /* zsync only works with http(s), even though curl can do other things */
    res = curl_easy_setopt( curl, CURLOPT_PROTOCOLS, CURLPROTO_HTTP | CURLPROTO_HTTPS );
    if( res != CURLE_OK ) {
        fprintf(stderr, "CURLOPT_PROTOCOLS: %s\n", curl_easy_strerror(res));
        curl_easy_cleanup(curl);
        return NULL;
    }

    /* We'd like to follow redirects */
    curl_easy_setopt( curl, CURLOPT_FOLLOWLOCATION, 1 );

    /* Set a User-Agent string */
    curl_easy_setopt( curl, CURLOPT_USERAGENT, "zsync/" VERSION );

    /* Turn on SO_KEEPALIVE */
    curl_easy_setopt( curl, CURLOPT_SOCKOPTFUNCTION, range_fetch_sockoptcallback );

    /* Command line options */

    if(be_verbose) {
        /* -v */
        curl_easy_setopt( curl, CURLOPT_VERBOSE, 1 );
    }

    if(cacert) {
        /* -C */
        res = curl_easy_setopt( curl, CURLOPT_CAINFO, cacert );
        if( res != CURLE_OK ) {
            fprintf(stderr, "--cacert: %s\n", curl_easy_strerror(res));
            curl_easy_cleanup(curl);
            return NULL;
        }
    }

    if(sslcert) {
        /* -R */
        res = curl_easy_setopt( curl, CURLOPT_SSLCERT, sslcert );
        if( res != CURLE_OK ) {
            fprintf(stderr, "-R: %s\n", curl_easy_strerror(res));
            curl_easy_cleanup(curl);
            return NULL;
        }
    }

    if(sslkey) {
        /* -S */
        res = curl_easy_setopt( curl, CURLOPT_SSLKEY, sslkey );
        if( res != CURLE_OK ) {
            fprintf(stderr, "-S: %s\n", curl_easy_strerror(res));
            curl_easy_cleanup(curl);
            return NULL;
        }
    }

    if(want_interface) {
        /* -I */
        res = curl_easy_setopt( curl, CURLOPT_INTERFACE, want_interface );
        if( res != CURLE_OK ) {
            /* Warn and continue. Let's try anyway even if this setopt fails */
            fprintf(stderr, "--interface: %s\n", curl_easy_strerror(res));
        }
    }

    if(be_insecure) {
        /* -K */
        curl_easy_setopt( curl, CURLOPT_SSL_VERIFYPEER, 0 );
        curl_easy_setopt( curl, CURLOPT_SSL_VERIFYHOST, 0 );
    }

    if(use_timeout) {
        /* -T */
        curl_easy_setopt( curl, CURLOPT_TIMEOUT, use_timeout );
    }

    return curl;
}

/* Parse a Content-Range header's value, like "bytes 0-5/6"
 * Returns 0 on success, and puts parsed values into *from and *to
 * Returns nonzero on failure
 */
int parse_content_range( char *buf, size_t len, off_t *from, off_t *to ) {
    char* bufcpy;
    int ret;

    /* Copy so we can nul-terminate and use sscanf... there's probably a better way */
    bufcpy = malloc(len+1);
    memcpy(bufcpy,buf,len);
    bufcpy[len] = 0;

    ret = sscanf(bufcpy, "bytes " OFF_T_PF "-" OFF_T_PF "/", from, to);
    free(bufcpy);

    if( ret == 2 ) {
        return 0;
    } else {
        return -1;
    }
}

/* Download content from orig_url into the file tfname (or tmpfile, if tfname
 * is NULL), and return corresponding FILE*, or NULL on failure. Optionally
 * store last used URL, after redirects, into track_referer.
 *
 * XXX: When tfname is set, non-curl version downloaded into a ".part" file and
 *      then rename(1)ed
 * XXX: When tfname is set, non-curl version used If-Modified-Since, 
 *      If-Unmodified-Since, and Range to resume transfers on the .part file
 * XXX: Non-curl version had a progress meter
 */
FILE *http_get(const char *orig_url, char **track_referer, const char *tfname) {
    FILE *f;
    CURL *curl;
    CURLcode res;
    long response_code;
    char *effective_url;

    /* We're either downloading to a file on disk (-k option) or a tmpfile */
    f = tfname ? fopen(tfname, "w+") : tmpfile();
    if (!f) {
        perror(tfname);
        return NULL;
    }

    curl = make_curl_handle();
    if (!curl) {
        /* make_curl_handle already printed an error message */
        fclose(f);
        return NULL;
    }

    curl_easy_setopt( curl, CURLOPT_URL, orig_url );
    curl_easy_setopt( curl, CURLOPT_WRITEDATA, f );

    /* Try URL fetch */
    res = curl_easy_perform( curl );
    if (res) {
        fprintf(stderr, "Curl: %s\n", curl_easy_strerror(res));
        fclose(f);
        curl_easy_cleanup(curl);
        return NULL;
    }

    /* Confirm we got a 200 OK */
    res = curl_easy_getinfo( curl, CURLINFO_RESPONSE_CODE, &response_code );
    if (res != CURLE_OK) {
        fprintf(stderr, "Could not get HTTP response code!\n");
        fclose(f);
        curl_easy_cleanup(curl);
        return NULL;
    }

    if (response_code != 200) {
        fprintf(stderr, "Got HTTP %ld (expected 200)\n", response_code);
        fclose(f);
        curl_easy_cleanup(curl);
        return NULL;
    }

    /* Return effective URL if asked for it */
    if (track_referer) {
        res = curl_easy_getinfo( curl, CURLINFO_EFFECTIVE_URL, &effective_url );
        if(res != CURLE_OK) {
            fprintf(stderr, "Could not get last effective URL: %s\n", curl_easy_strerror(res));
            fclose(f);
            curl_easy_cleanup(curl);
            return NULL;
        }

        *track_referer = strdup(effective_url);
    }

    /* Done with the curl handle */
    curl_easy_cleanup( curl );

    /* The caller expects f to be at the beginning */
    rewind(f);
    return f;
}

/****************************************************************************
 *
 * HTTP Range: / 206 response interface
 *
 * The state engine here is:
 * If sd == -1, not connected;
 * else, if block_left is 0
 *     if boundary is unset, we're reading HTTP headers
 *     if boundary is set, we're reading a MIME boundary
 * else we're reading a block of actual data; block_left bytes still to read.
 *
 *
 * Procedure:
 *
 * 1) range_fetch_perform resets all the "State for HTTP response parser"
 *
 * 2) range_fetch_read_http_headers sets:
 *    - http_code, and
 *    - if multipart: boundary
 *    - if single range: block_left, offset
 *
 * 3) range_fetch_read_http_content can be in these states:
 *    - block_left set: reading data block
 *    - block_left unset, boundary set: reading MIME multipart delimiter,
 *      on line number "multipart" of the delimiter
 *    - block_left unset, boundary unset: inconsistent state. probable bad
 *      response from server.
 */

struct range_fetch {
    CURL *curl;     /* Currently open curl handle to the server, or NULL */

    /* URL we're telling curl to retrieve from, host:port, auth header
       Must be kept around after passing it to curl_easy_setopt */
    char *url;
    char hosth[256];
    char *authh;

    /* zsync_receiver struct that will receive data we get from the remote */
    struct zsync_receiver *zr;

    /* Host and port to connect to (could be the same as the URL, or proxy) */
    char *chost;
    char *cport;

    /* State for HTTP response parser */
    int http_code;      /* Most recent HTTP status code seen. Reset to 0 for every curl request. */
    int sd;         /* Currently open socket to the server, or -1 */
    char *boundary;     /* If we're expecting a mime/multipart response, this is the boundary string. */
    int multipart;      /* If we're reading a MIME multipart delimiter, the line number we're on
                           1  = "--boundary" line
                           2+ = Headers */

    /* State for block currently being read */
    size_t block_left;  /* non-zero if we're in the middle of reading a block */
    off_t offset;       /* and this is the offset of the start of the block we are reading */

    /* Buffering of data from the remote server */
    char buf[4096];
    int buf_start, buf_end; /* Bytes buf_start .. buf_end-1 in buf[] are valid */

    /* Keep count of total bytes retrieved */
    off_t bytes_down;

    int server_close; /* 0: can send more, 1: cannot send more (but one set of headers still to read), 2: cannot send more and all existing headers read */

    /* Byte ranges to fetch */
    off_t *ranges_todo; /* Contains 2*nranges ranges, consisting of start and stop offset */
    int nranges;
    int rangessent;     /* We've requested the first rangessent ranges from the remote */
    int rangesdone;     /* and received this many */
};

/* range_fetch methods */

/* Sets up the range_fetch struct to expect bytes from-to (fairly) immediately. Normally
   called when the remote sends us a Content-Range header, either on a full HTTP response
   or on a MIME multipart section.

   Returns 0 on success, nonzero on failure. Can fail if we were not expecting to
   be served this particular range. */
int range_fetch_expect( struct range_fetch *rf, off_t from, off_t to ) {

    /* If we're done, this is an error. */
    if( rf->rangesdone >= rf->nranges ) {
        fprintf( stderr, "Not expecting to see further range blocks!\n" );
        return -1;
    }

    /* If this isn't the next range in the sequence, this is an error. */
    if( rf->ranges_todo[2*rf->rangesdone] != from || rf->ranges_todo[2*rf->rangesdone+1] != to ) {
        fprintf( stderr,
                 "Expected Content-Range " OFF_T_PF "-" OFF_T_PF " but got " OFF_T_PF "-" OFF_T_PF " from server!\n",
                 rf->ranges_todo[2*rf->rangesdone], rf->ranges_todo[2*rf->rangesdone+1], from, to );
        return -1;
    }

    /* If we aren't done reading the previous range, this is an error. */
    if( rf->block_left != 0 ) {
        fprintf( stderr, "Range was truncated!\n" );
        return -1;
    }

    /* Looks good. Set up block_left and offset. */
    rf->block_left = to + 1 - from;
    rf->offset = from;

    return 0;
}

/* Curl SOCKOPTFUNCTION. Sets SO_KEEPALIVE on the socket. */
int range_fetch_sockoptcallback( void *clientp, curl_socket_t curlfd, curlsocktype purpose ) {

    /* CURLSOCKTYPE_IPCXN is the primary connection */
    if( purpose == CURLSOCKTYPE_IPCXN ) {
        int optval = 1;
        if( setsockopt(curlfd, SOL_SOCKET, SO_KEEPALIVE, (void *)&optval, sizeof(optval) ) ) {
            /* setsockopt failed. continue anyway. */
            perror("setsockopt");
        }
    }

    /* Returns 0 on success */
    return 0;
}

/* Curl HEADERFUNCTION. Gets headers one-by-one (including the HTTP status line) plus a range_fetch struct. */
size_t range_fetch_read_http_headers( void *ptr, size_t size, size_t nmemb, void *userdata ) {
    struct range_fetch *rf = (struct range_fetch *)userdata;
    char buf[512];
    char *buf = (char *)ptr;
    size_t len = size * nmemb;
    char *end = buf + len;
    int status;
    int seen_location = 0;

    /* Keep bytes_down up-to-date */
    rf->bytes_down += len;

    /* Look for HTTP status line */
    if( len >= strlen("HTTP/1.1 XXX") && memcmp(buf, "HTTP/1.1 ", strlen("HTTP/1.1 ")) == 0 ) {

        /* If previous HTTP code was 2xx, something bad is happening. We should only get
         * one 2xx (previous codes in this request chain would have been redirects, if anything) */
        if( rf->http_code >= 200 && rf->http_code < 300 ) {
            fprintf(stderr, "Not expecting to see further HTTP responses after a 2xx (last code was %d)!\n", rf->http_code);
            return 0;
        }

        /* Remember most recent HTTP code */
        rf->http_code = (int)(buf[9]-'0')*100 + (int)(buf[10]-'0')*10 + (int)(buf[11]-'0');
    }


    /* HTTP 200 + Content-Length -> Entire file */
    else if( rf->http_code == 200 && len > strlen("content-length: x") && strncasecmp(buf, "content-length: ", strlen("content-length: ")) == 0) {
        off_t to = (off_t)strtoll(buf + strlen("content-length: "), (void*)(buf + len), 10) - 1;

        /* Found to, and from = 0 */
        if( range_fetch_expect( rf, 0, to ) != 0 ) {
            /* Error. range_fetch_expect has already printed a message, so just leave */
            return 0;
        }
    }

    /* HTTP 206 + Content-Range -> Single range */
    else if( rf->http_code == 206 && len > strlen("content-range: bytes ") && strncasecmp(buf, "content-range: bytes ", strlen("content-range: bytes ")) == 0 ) {
        /* Okay, we're getting a non-MIME block from the remote. */
        off_t from, to;

        if( parse_content_range(buf + strlen("content-range: "), len - strlen("content-range: "), &from, &to) != 0 ) {
            /* This Content-Range header is bogus */
            fprintf(stderr, "Server sent us a bogus Content-Range!\n" );
            return 0;
        }

        /* Found from, to */
        if( range_fetch_expect( rf, from, to ) != 0 ) {
            /* Error. range_fetch_expect has already printed a message, so just leave */
            return 0;
        }
    }

    /* HTTP 206 + Content-Type multipart/byteranges -> Multiple ranges */
    else if( rf->http_code == 206 && len > strlen("content-type: multipart/byteranges") && strncasecmp(buf, "content-type: multipart/byteranges", strlen("content-type: multipart/byteranges")) == 0 ) {
        char *p;

        /* Goal is the multipart boundary string */

        /* We don't expect it to be set already... */
        if( rf->boundary ) {
            fprintf(stderr, "Not expecting to see more than one multipart/byteranges response!\n");
            return 0;
        }

        /* Place pointer after "multipart/byteranges" */
        p = buf + strlen("content-type: multipart/byteranges");

        /* Look for the boundary= string */
        while( p + strlen("boundary=") <= end ) {
            if( memcmp(p, "boundary=", strlen("boundary=")) == 0 )
                break;
            p++;
        }

        if( p + strlen("boundary=") < end ) {
            char *boundary;
            int quoted = 0;

            /* Found the boundary= string */
            p += strlen("boundary=");

            /* Allocate a buffer that might be a little big */
            rf->boundary = boundary = malloc(end-p+1);
            if(!boundary) {
                perror("malloc");
                return 0;
            }

            /* Possibly skip a quote mark */
            if( *p == '"' ) {
                quoted = 1;
                p++;
            }

            /* Copy until the end of the boundary */
            while( p < end ) {
                if( *p == 0 )
                    break;

                if( quoted && *p == '"' )
                    break;

                if( !quoted && ( *p == '\r' || *p == ' ' || *p == '\n' ) )
                    break;

                *boundary = *p;
                boundary++;
                p++;
            }

            /* nul-terminate the boundary */
            *boundary = 0;
        }
    }

    {                           /* read status line */
        char *p;

        if (rfgets(buf, sizeof(buf), rf) == NULL)
            return -1;
        if (buf[0] == 0)
            return 0;           /* EOF, caller decides if that's an error */
        if (memcmp(buf, "HTTP/1", 6) != 0 || (p = strchr(buf, ' ')) == NULL) {
            fprintf(stderr, "got non-HTTP response '%s'\n", buf);
            return -1;
        }
        status = atoi(p + 1);
        if (status != 206 && status != 301 && status != 302) {
            if (status >= 300 && status < 400) {
                fprintf(stderr,
                        "\nzsync received a redirect/further action required status code: %d\nzsync specifically refuses to proceed when a server requests further action. This is because zsync makes a very large number of requests per file retrieved, and so if zsync has to perform additional actions per request, it further increases the load on the target server. The person/entity who created this zsync file should change it to point directly to a URL where the target file can be retrieved without additional actions/redirects needing to be followed.\nSee http://zsync.moria.orc.uk/server-issues\n",
                        status);
            }
            else if (status == 200) {
                fprintf(stderr,
                        "\nzsync received a data response (code %d) but this is not a partial content response\nzsync can only work with servers that support returning partial content from files. The person/entity creating this .zsync has tried to use a server that is not returning partial content. zsync cannot be used with this server.\nSee http://zsync.moria.orc.uk/server-issues\n",
                        status);
            }
            else {
                /* generic error message otherwise */
                fprintf(stderr, "bad status code %d\n", status);
            }
            return -1;
        }
        if (*(p - 1) == '0') {  /* HTTP/1.0 server? */
            rf->server_close = 2;
        }
    }

    /* Read other headers */
    while (1) {
        char *p;

        /* Get next line */
        if (rfgets(buf, sizeof(buf), rf) == NULL)
            return -1;

        /* If it's the end of the headers */
        if (buf[0] == '\r' || buf[0] == '\0') {
            /* We are happy provided we got the block boundary, or an actual block is starting. */
            if (((rf->boundary || rf->block_left)
                 && !(rf->boundary && rf->block_left))
                || (status >= 300 && status < 400 && seen_location))
                return status;
            break;
        }

        /* Parse header */
        p = strstr(buf, ": ");
        if (!p)
            break;
        *p = 0;
        p += 2;
        buflwr(buf);
        {   /* Remove the trailing \r\n from the value */
            int len = strcspn(p, "\r\n");
            p[len] = 0;
        }
        /* buf is the header name (lower-cased), p the value */
        /* Switch based on header */

        /* If remote closes the connection on us, record that */
        if (!strcmp(buf, "connection") && !strcmp(p, "close")) {
            rf->server_close = 2;
        }

        if (status == 206 && !strcmp(buf, "content-range")) {
            /* Okay, we're getting a non-MIME block from the remote. Get the
             * range and set our state appropriately */
            off_t from, to;
            sscanf(p, "bytes " OFF_T_PF "-" OFF_T_PF "/", &from, &to);
            if (from <= to) {
                rf->block_left = to + 1 - from;
                rf->offset = from;
            }

            /* Can only have got one range. */
            rf->rangesdone++;
            rf->rangessent = rf->rangesdone;
        }

        /* If we're about to get a MIME multipart block set */
        if (status == 206 && !strcasecmp(buf, "content-type")
            && !strncasecmp(p, "multipart/byteranges", 20)) {

            /* Get the multipart boundary string */
            char *q = strstr(p, "boundary=");
            if (!q)
                break;
            q += 9;

            /* Gah, we could really use a regexp here. Could be quoted... */
            if (*q == '"') {
                rf->boundary = strdup(q + 1);
                q = strchr(rf->boundary, '"');
                if (q)
                    *q = 0;
            }
            else {  /* or unquoted */
                rf->boundary = strdup(q);
                q = rf->boundary + strlen(rf->boundary) - 1;

                while (*q == '\r' || *q == ' ' || *q == '\n')
                    *q-- = '\0';
            }
        }

        /* If remote is telling us to change URL */
        if ((status == 302 || status == 301)
            && !strcmp(buf, "location")) {
            if (seen_location++) {
                fprintf(stderr, "Error: multiple Location headers on redirect\n");
                break;
            }

            /* Set new target URL 
             * NOTE: we are violating the "the client SHOULD continue to use
             * the Request-URI for future requests" of RFC2616 10.3.3 for 302s.
             * It's not practical given the number of requests we are making to
             * follow the RFC here, and at least we're only remembering it for
             * the duration of this transfer. */
            if (!no_progress)
                fprintf(stderr, "followed redirect to %s\n", p);
            range_fetch_set_url(rf, p);

            /* Flag caller to reconnect; the new URL might be a new target. */
            rf->server_close = 2;
        }
        /* No other headers that we care about. In particular:
         *
         * FIXME: non-conformant to HTTP/1.1 because we ignore
         * Transfer-Encoding: chunked.
         */
    }
    status = -1;
    return len;
}

/* range_fetch_set_url(rf, url)
 * Set up a range_fetch to fetch from a given URL. Private method. 
 * C is a nightmare for memory allocation here. At least the errors should be
 * caught, but minor memory leaks may occur on some error paths. */
static int range_fetch_set_url(struct range_fetch* rf, const char* orig_url) {
    /* Get the host, port and path from the URL. */
    char hostn[sizeof(rf->hosth)];
    char* cport;
    char* p = get_http_host_port(orig_url, hostn, sizeof(hostn), &cport);
    if (!p) {
        return 0;
    }

    free(rf->url);
    if (rf->authh) free(rf->authh);

    /* Get host:port for Host: header */
    if (strcmp(cport, "http") != 0)
        snprintf(rf->hosth, sizeof(rf->hosth), "%s:%s", hostn, cport);
    else
        snprintf(rf->hosth, sizeof(rf->hosth), "%s", hostn);

    if (proxy) {
        /* URL must be absolute; don't need cport anymore, just need full URL
         * to give to proxy. */
        free(cport);
        rf->url = strdup(orig_url);
    }
    else {
        free(rf->cport);
        free(rf->chost);
        // Set url to relative part and chost, cport to the target
        if ((rf->chost = strdup(hostn)) == NULL) {
            free(cport);
            return 0;
        }
        rf->cport = cport;
        rf->url = strdup(p);
    }

    /* Get any auth header that we should use */
    rf->authh = get_auth_hdr(hostn);

    return !!rf->url;
}

/* get_more_data - this is the method which owns all reads from the remote.
 * Nothing else reads from the remote. This buffers data, so that the
 * higher-level methods below can easily read whole lines from the remote. 
 * The higher-level methods call this function when they need more data: 
 * it refills the buffer with data from the network. Returns the bytes read. */
static int get_more_data(struct range_fetch *rf) {
    /* First, garbage collect - move the 'live' data in the buffer to the start
     * of the buffer. */
    if (rf->buf_start) {
        memmove(rf->buf, &(rf->buf[rf->buf_start]),
                rf->buf_end - rf->buf_start);
        rf->buf_end -= rf->buf_start;
        rf->buf_start = 0;
    }

    {   /* Read as much as the OS wants to give us, up to a limit of filling
         * the rest of the buffer; ignore EINTR. */
        int n;
        do {
            n = read(rf->sd, &(rf->buf[rf->buf_end]),
                     sizeof(rf->buf) - rf->buf_end);
        } while (n == -1 && errno == EINTR);
        if (n < 0) {
            perror("read");
        }
        else {

            /* Add new bytes to buffer, and update total bytes count */
            rf->buf_end += n;
            rf->bytes_down += n;
        }
        return n;
    }
}

/* rfgets - get next line from the remote (terminated by LF or end-of-file)
 * (using the buffer, fetching more data if there's no full line in the buffer
 * yet) */
static char *rfgets(char *buf, size_t len, struct range_fetch *rf) {
    char *p;
    while (1) {
        /* Look for a line end in the in buffer */
        p = memchr(rf->buf + rf->buf_start, '\n', rf->buf_end - rf->buf_start);

        /* If we don't have the end of the line yet, fetch more data into the
         * buffer (and go around again) */
        if (!p) {
            int n = get_more_data(rf);
            if (n <= 0) {
                /* EOF - just return all that we have left */
                p = &(rf->buf[rf->buf_end]);
            }
        }
        else    /* We have a \n; set p to point just past it */
            p++;

        if (p) {
            register char *bufstart = &(rf->buf[rf->buf_start]);

            /* Work out how much data to return - the line, or at most 'len' bytes */
            len--;              /* leave space for trailing \0 */
            if (len > (size_t) (p - bufstart))
                len = p - bufstart;

            /* Copy from input buffer to return buffer, nul terminate, and advance
             * current position in the input buffer */
            memcpy(buf, bufstart, len);
            buf[len] = 0;
            rf->buf_start += len;
            return buf;
        }
    }
}

/* buflwr(str) - in-place convert this string to lower case */
static void buflwr(char *s) {
    char c;
    while ((c = *s) != 0) {
        if (c >= 'A' && c <= 'Z')
            *s = c - 'A' + 'a';
        s++;
    }
}

/* Curl WRITEFUNCTION. Gets response data in batches, plus a range_fetch struct. */
size_t range_fetch_read_http_content( void *ptr, size_t size, size_t nmemb, void *userdata ) {
    struct range_fetch *rf = (struct range_fetch *)userdata;
    char *buf = (char *)ptr;
    size_t len = size * nmemb;

    /* Make sure we're reading content from a 200 (ok) or 206 (partial content) */
    if( rf->http_code != 200 && rf->http_code != 206 ) {
        fprintf( stderr, "Expected HTTP 200 or 206 (partial content) but got code %d!\n", rf->http_code );
        return 0;
    }

    /* Keep bytes_down up-to-date */
    rf->bytes_down += len;

    /* Loop until nothing left to read in this chunk */
    while( len ) {

        if( rf->block_left > 0 && rf->multipart == 0 ) {
            /* In the middle of reading a block */

            /* Read the min of block_left and len */
            size_t block_todo = rf->block_left > len ? len : rf->block_left;

            if( zsync_receive_data( rf->zr, buf, rf->offset, block_todo ) != 0 )
                return 0;

            rf->offset += block_todo;
            rf->block_left -= block_todo;

            if( rf->block_left == 0 ) {
                /* One more range done */
                rf->rangesdone ++;
            }

            /* Move buf/len up past what we just read */
            buf += block_todo;
            len -= block_todo;
        }

        if( len ) {
            /* More to read, not part of a block. We should be inside a multipart delimiter */

            if( rf->multipart == -1 ) {
                /* In the middle of the MIME epilogue. Ignore */
                break;
            }

            if( !rf->boundary ) {
                /* We weren't expecting a multipart delimiter. Abort. */
                fprintf( stderr, "Not expecting more content from the server!\n" );
                return 0;
            }

            /* Copy one line at a time into rf->buf (until CRLF) or until we run out of
             * stuff to copy. The purpose of buffering is that curl might split a line. */
            while( len ) {
                /* Make sure we have enough space in rf->buf for this char and possibly a nul */
                if( rf->buf_end >= (int)sizeof(rf->buf) - 2 ) {
                    fprintf( stderr, "Overflow buffering multipart response!\n" );
                    return 0;
                }

                /* Copy one more character */
                rf->buf[rf->buf_end++] = *buf;

                buf++;
                len--;

                /* Detect possible end-of-line (CRLF) */
                if( rf->buf_end >= 2 && rf->buf[rf->buf_end-2] == '\r' && rf->buf[rf->buf_end-1] == '\n' ) {
                    /* nul-terminate rf->buf before the CRLF */
                    rf->buf[rf->buf_end-2] = '\0';
                    rf->buf_end -= 2;

                    if( rf->multipart == 0 ) {
                        /* Expecting empty line to toss. Just confirm it. */
                        if( rf->buf_end > 0 ) {
                            fprintf(stderr, "Missing CRLF before multipart boundary! [%s]\n", rf->buf);
                            return 0;
                        }

                        rf->multipart ++;
                    }
                    else if( rf->multipart == 1 ) {
                        /* Expecting --boundary */
                        size_t boundarysz = strlen(rf->boundary);

                        if(
                            (size_t)rf->buf_end < 2 + boundarysz         /* too short */
                            || rf->buf[0] != '-' || rf->buf[1] != '-'    /* no -- */
                            || memcmp(rf->buf+2,rf->boundary,boundarysz) /* no boundary string */
                        ) {
                            fprintf(stderr, "Missing multipart boundary string! [%s]\n", rf->buf);
                            return 0;
                        }

                        /* Two more dashes means that the multipart message is over */
                        if( (size_t)rf->buf_end >= 4 + boundarysz && rf->buf[2+boundarysz] == '-' && rf->buf[3+boundarysz] == '-' ) {
                            rf->multipart = -1;

                            /* Clear rf->boundary so we don't try to read another multipart delimiter */
                            free(rf->boundary);
                            rf->boundary = NULL;
                        }
                        else {
                            rf->multipart ++;
                        }
                    }
                    else if( rf->multipart > 1 ) {
                        /* Looking for content-range OR empty line */
                        if( rf->buf_end > strlen("content-range: bytes ") && strncasecmp(rf->buf, "content-range: bytes ", strlen("content-range: bytes ")) == 0 ) {
                            /* This is the content-range line */
                            off_t from, to;

                            if( parse_content_range( rf->buf + strlen("content-range: "), rf->buf_end - strlen("content-range: "), &from, &to) != 0 ) {
                                /* This Content-Range header is bogus */
                                fprintf(stderr, "Server sent us a bogus Content-Range!\n" );
                                return 0;
                            }

                            /* Found from, to */
                            if( range_fetch_expect( rf, from, to ) != 0 ) {
                                /* Error. range_fetch_expect has already printed a message, so just leave */
                                return 0;
                            }

                            rf->multipart ++;
                        }
                        else if( rf->buf_end == 0 ) {
                            /* End of multipart delimiter */
                            rf->multipart = 0;
                        }
                        else {
                            /* Uninteresting header line */
                            rf->multipart ++;
                        }
                    }

                    /* Reset rf->buf */
                    rf->buf_end = 0;

                    /* Break out of the multipart delimiter loop. We'll come back to it if we need to. */
                    break;
                }
            }
        }
    }

    return size * nmemb;
}

/* range_fetch_start(origin_url)
 * Returns a new range fetch object, for the given URL.
 */
struct range_fetch *range_fetch_start(const char *orig_url, struct zsync_receiver *zr) {
    struct range_fetch *rf;

    if (!zr || !orig_url) {
        return NULL;
    }

    rf = malloc(sizeof(struct range_fetch));
    if (!rf)
        return NULL;

    /* Copy pointer to zsync_receiver */
    rf->zr = zr;

    /* If going through a proxy, we can immediately set up the host and port to
     * connect to */
    if (proxy) {
        rf->cport = strdup(pport);
        rf->chost = strdup(proxy);
    }
    else {
        rf->cport = NULL;
        rf->chost = NULL;
    }
    /* Blank initialisation for other fields before set_url call */
    rf->url = NULL;
    rf->authh = NULL;

    /* Init curl handle */
    rf->curl = make_curl_handle();
    if (!rf->curl || !range_fetch_set_url(rf, orig_url)) {
        /* make_curl_handle already printed an error message */
        free(rf->cport);
        free(rf->chost);
        free(rf);
        return NULL;
    }

    /* Copy url into a new string */
    rf->url = strdup(orig_url);

    curl_easy_setopt( rf->curl, CURLOPT_URL, rf->url );
    curl_easy_setopt( rf->curl, CURLOPT_HEADERFUNCTION, range_fetch_read_http_headers );
    curl_easy_setopt( rf->curl, CURLOPT_HEADERDATA, (void*)rf );
    curl_easy_setopt( rf->curl, CURLOPT_WRITEFUNCTION, range_fetch_read_http_content );
    curl_easy_setopt( rf->curl, CURLOPT_WRITEDATA, (void*)rf );

    /* Initialise other state fields */
    rf->block_left = 0;
    rf->bytes_down = 0;
    rf->boundary = NULL;
    rf->multipart = 0;
    rf->buf_end = 0;    /* Buffer initially empty */
    rf->sd = -1;                        /* Socket not open */
    rf->ranges_todo = NULL;             /* And no ranges given yet */
    rf->nranges = rf->rangessent = rf->rangesdone = 0;

    return rf;
}

/* range_fetch_addranges(self, off_t[], nranges)
 * Adds ranges to fetch, supplied as an array of 2*nranges offsets (start and
 * stop for each range) */
void range_fetch_addranges(struct range_fetch *rf, off_t * ranges, int nranges) {
    int existing_ranges = rf->nranges - rf->rangesdone;

    /* Allocate new memory, enough for valid existing entries and new entries */
    off_t *nr = malloc(2 * sizeof(*ranges) * (nranges + existing_ranges));
    if (!nr)
        return;

    /* Copy only still-valid entries from the existing queue over */
    memcpy(nr, &(rf->ranges_todo[2 * rf->rangesdone]),
           2 * sizeof(*ranges) * existing_ranges);

    /* And replace existing queue with new one */
    free(rf->ranges_todo);
    rf->ranges_todo = nr;
    rf->rangessent -= rf->rangesdone;
    rf->rangesdone = 0;
    rf->nranges = existing_ranges;

    /* And append the new stuff */
    memcpy(&nr[2 * existing_ranges], ranges, 2 * sizeof(*ranges) * nranges);
    rf->nranges += nranges;
}

/* range_fetch_bytes_down
 * Simple getter method, returns the total bytes retrieved */
off_t range_fetch_bytes_down(const struct range_fetch * rf) {
    return rf->bytes_down;
}

/* Destructor */
void range_fetch_end(struct range_fetch *rf) {
    curl_easy_cleanup( rf->curl );
    if (rf->sd != -1)
        close(rf->sd);
    free(rf->ranges_todo);
    free(rf->boundary);
    free(rf->url);
    free(rf->cport);
    free(rf->chost);
    free(rf);
}

/* range_fetch_connect
 * Connect this rf to its remote server */
static void range_fetch_connect(struct range_fetch *rf) {
    rf->sd = connect_to(rf->chost, rf->cport);
    rf->server_close = 0;
    rf->rangessent = rf->rangesdone;
    rf->buf_start = rf->buf_end = 0;    /* Buffer initially empty */
}

/* range_fetch_getmore
 * On a connected range fetch, send another request to the remote */
static void range_fetch_getmore(struct range_fetch *rf) {
    char request[2048];
    int l;
    int max_range_per_request = 20;
    char request[1024] = { 0 }; /* Range like "X-Y,N-M" */

    /* Only if there's stuff queued to get */
    if (rf->rangessent == rf->nranges)
        return;

    /* Build the base request, everything up to the Range: bytes= */
    snprintf(request, sizeof(request),
             "GET %s HTTP/1.1\r\n"
             "User-Agent: zsync/" VERSION "\r\n"
             "Host: %s"
             "%s%s\r\n"
             "%s"
             "Range: bytes=",
             rf->url, rf->hosth,
             referer ? "\r\nReferer: " : "", referer ? referer : "",
             rf->authh ? rf->authh : "");

    /* The for loop here is just a sanity check, lastrange is the real loop control */
    for (; rf->rangessent < rf->nranges;) {
        int i = rf->rangessent;
        int lastrange = 0;
        int chars;
        int l;

        /* Add at least one byterange to the request; but is this the last one?
         * That's decided based on whether there are any more to add, whether
         * we've reached our self-imposed limit per request, and whether
         * there's buffer space to add more.
         */
        l = strlen(request);
        if (l > 1200 || !(--max_range_per_request) || i == rf->nranges - 1)
            lastrange = 1;

        /* Append to the request */
        snprintf(request + l, sizeof(request) - l, OFF_T_PF "-" OFF_T_PF "%s",
                 rf->ranges_todo[2 * i], rf->ranges_todo[2 * i + 1],
                 lastrange ? "" : ",");

        /* And record that we have sent this one */
        rf->rangessent++;

        /* Exit loop if that is the last to add */
        if (lastrange)
            break;
    }
    l = strlen(request);

    /* Possibly close the connection (and record the fact, so we definitely
     * don't send more stuff) if this is the last */
    snprintf(request + l, sizeof(request) - l, "\r\n%s\r\n",
             rf->rangessent == rf->nranges ? (rf->server_close =
                                              1, "Connection: close\r\n") : "");

    {   /* Send the request */
        size_t len = strlen(request);
        char *p = request;
        int r = 0;

        while (len > 0
               && ((r = send(rf->sd, p, len, 0)) != -1 || errno == EINTR)) {
            if (r >= 0) {
                p += r;
                len -= r;
            }
        }
        if (r == -1) {
            perror("send");
        }
    }
}

/* Return:
 *  1 = Please call again, more work to do
 *  0 = No more work to do
 * -1 = error
 */
int range_fetch_perform(struct range_fetch *rf) {
    CURLcode res;
    int max_range_per_request = 20;
    char request[1024] = { 0 }; /* Range like "X-Y,N-M" */

    /* Reset per-request state in range_fetch */
    rf->block_left = 0;
    rf->offset = 0;
    rf->http_code = 0;
    rf->buf_end = 0;
    rf->multipart = 0;
    free(rf->boundary);
    rf->boundary = NULL;

    /* Forget about any ranges requested last range_fetch_perform, but not received */
    rf->rangessent = rf->rangesdone;

    /* The for loop here is just a sanity check, lastrange is the real loop control */
    for (; rf->rangessent < rf->nranges;) {
        int i = rf->rangessent;
        int lastrange = 0;
        int chars;
        int l;

        /* Add at least one byterange to the request; but is this the last one?
         * That's decided based on whether there are any more to add, whether
         * we've reached our self-imposed limit per request, and whether
         * there's buffer space to add more.
         */
        if (!(--max_range_per_request) || i == rf->nranges - 1)
            lastrange = 1;

        /* Append to the request */
        l = strlen(request);
        chars = snprintf(request + l, sizeof(request) - l, OFF_T_PF "-" OFF_T_PF "%s",
                         rf->ranges_todo[2 * i], rf->ranges_todo[2 * i + 1],
                         lastrange ? "" : ",");

        if( chars >= (int)sizeof(request) - l ) {
            /* Overflow. Extremely unlikely given max_range_per_request. */
            fprintf(stderr, "Overflow setting up Range header!\n");
            return -1;
        }

        /* And record that we have sent this one */
        rf->rangessent++;

        /* Exit loop if that is the last to add */
        if (lastrange)
            break;
    }

    if( rf->rangessent <= rf->rangesdone ) {
        /* Nothing to do. Done! */
        return 0;
    }

    /* Need to ask curl to send these ranges */
    curl_easy_setopt( rf->curl, CURLOPT_RANGE, NULL );
    curl_easy_setopt( rf->curl, CURLOPT_RANGE, &request );
    res = curl_easy_perform( rf->curl );

    /* Get rid of CURLOPT_RANGE, since the pointer will be invalid shortly. */
    curl_easy_setopt( rf->curl, CURLOPT_RANGE, NULL );

    /* If we got a curl error, we need to flag that to our caller */
    if(res) {
        if( res != CURLE_WRITE_ERROR ) {
            /* CURLE_WRITE_ERROR means one of our callbacks wanted to abort
               the transfer. It would have printed its own error message */
            fprintf(stderr,
                   "Could not fetch URL: %s\n",
                   curl_easy_strerror(res));
        }

        return -1;
    }

    /* If we did not get back all the ranges we wanted, consider it an error */
    if( rf->rangessent != rf->rangesdone ) {
        fprintf( stderr, "Missing ranges in response from server!\n" );
        return -1;
    }

    /* Else, let the zsync receiver know that we're at EOF; there
     * could be data in its buffer that it can use or needs to process */
    if( zsync_receive_data( rf->zr, NULL, rf->offset, 0 ) ) {
        return -1;
    }

    /* If we got a redirect, we need to set a new target URL
     * NOTE: we are violating the "the client SHOULD continue to use
     * the Request-URI for future requests" of RFC2616 10.3.3 for 302s.
     * It's not practical given the number of requests we are making to
     * follow the RFC here, and at least we're only remembering it for
     * the duration of this transfer. */
    {
        long nredir = 0;
        char *redirurl;
        char *p;

        res = curl_easy_getinfo( rf->curl, CURLINFO_REDIRECT_COUNT, &nredir );
        if( res == CURLE_OK && nredir > 0 ) {
            /* There were redirects */

            res = curl_easy_getinfo( rf->curl, CURLINFO_EFFECTIVE_URL, &redirurl );
            if( res != CURLE_OK ) {
                fprintf(stderr,
                       "Could not get redirect target URL: %s\n",
                       curl_easy_strerror(res));
                return -1;
            }

            p = strdup(redirurl);

            /* Remember the redirected URL for the next request */
            res = curl_easy_setopt( rf->curl, CURLOPT_URL, p );
            if( res != CURLE_OK ) {
                fprintf(stderr,
                       "Could not save redirect target URL: %s\n",
                       curl_easy_strerror(res));
                return -1;
            }

            /* OK to free rf->url now, curl doesn't need it anymore */
            free(rf->url);
            rf->url = p;
        }
    }

    return 1;
}
