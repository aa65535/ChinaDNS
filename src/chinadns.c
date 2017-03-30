/*  ChinaDNS
    Copyright (C) 2014-2015 clowwindy <clowwindy42@gmail.com>
    Copyright (C) 2015-2017 Jian Chang <aa65535@live.com>

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
*/

#include <fcntl.h>
#include <netdb.h>
#include <resolv.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>
#include <signal.h>
#include <arpa/inet.h>
#include <sys/select.h>
#include <sys/socket.h>
#include <sys/types.h>
#include <sys/time.h>
#include <sys/param.h>

#include "local_ns_parser.h"

#include "config.h"

typedef struct {
  int is_chn;
  struct in_addr addrs;
} ecs_addr_t;

typedef struct {
  int entries;
  ecs_addr_t *ecs_addrs;
} ecs_list_t;

typedef struct {
  uint16_t id;
  uint16_t old_id;
  struct sockaddr *addr;
  socklen_t addrlen;
} id_addr_t;

typedef struct {
  struct in_addr net;
  uint32_t mask;
} net_mask_t;

typedef struct {
  int entries;
  net_mask_t *nets;
} net_list_t;

typedef struct {
  uint16_t id;
  struct timeval ts;
  char *buf;
  size_t buflen;
  struct sockaddr *addr;
  socklen_t addrlen;
} delay_buf_t;

// avoid malloc and free
#define BUF_SIZE 2048
static char global_buf[BUF_SIZE];
static int verbose = 0;

static const char *default_dns_server = "8.8.8.8";
static char *dns_server = NULL;
struct addrinfo *dns_server_addr;

static int parse_args(int argc, char **argv);
static int setnonblock(int sock);
static int resolve_dns_server();

static const char *default_listen_addr = "0.0.0.0";
static const char *default_listen_port = "53";

static char *listen_addr = NULL;
static char *listen_port = NULL;

#define NETMASK_MIN 0
static char *chnroute_file = NULL;
static net_list_t chnroute_list;
static int parse_chnroute();
static int test_ip_in_list(struct in_addr ip, const net_list_t *netlist);

static int dns_init_sockets();
static void dns_handle_local();
static void dns_handle_remote();

static const char *hostname_from_question(ns_msg msg);
static int should_filter_query(ns_msg msg, int is_chn);

#define ID_ADDR_QUEUE_LEN 128
// use a queue instead of hash here since it's not long
static id_addr_t id_addr_queue[ID_ADDR_QUEUE_LEN];
static int id_addr_queue_pos = 0;

static void queue_add(id_addr_t id_addr);
static id_addr_t *queue_lookup(uint16_t id);

#define DELAY_QUEUE_LEN 128
static delay_buf_t delay_queue[DELAY_QUEUE_LEN];
static void schedule_delay(uint16_t query_id, const char *buf, size_t buflen,
                           struct sockaddr *addr, socklen_t addrlen);
static void check_and_send_delay();
static void free_delay(int pos);
// next position for first, not used
static int delay_queue_first = 0;
// current position for last, used
static int delay_queue_last = 0;
static float result_delay = 0.1f;

#define ECS_DATA_LEN 23
static char *edns_client_ip = NULL;
static ecs_list_t ecs_list;
static int resolve_ecs_addrs();
static void add_ecs_data(char *buf, struct in_addr *addr, uint8_t mask);

static int check_result(char *buf, size_t buflen);

static int local_sock;
static int remote_sock;

static void usage(void);

#define __LOG(o, t, v, s...) do {                                   \
  time_t now;                                                       \
  time(&now);                                                       \
  char *time_str = ctime(&now);                                     \
  time_str[strlen(time_str) - 1] = '\0';                            \
  if (t == 0) {                                                     \
    if (stdout != o || verbose) {                                   \
      fprintf(o, "%s ", time_str);                                  \
      fprintf(o, s);                                                \
      fflush(o);                                                    \
    }                                                               \
  } else if (t == 1) {                                              \
    fprintf(o, "%s %s:%d ", time_str, __FILE__, __LINE__);          \
    perror(v);                                                      \
  }                                                                 \
} while (0)

#define LOG(s...) __LOG(stdout, 0, "_", s)
#define ERR(s) __LOG(stderr, 1, s, "_")
#define VERR(s...) __LOG(stderr, 0, "_", s)

#ifdef DEBUG
#define DLOG(s...) LOG(s)
void __gcov_flush(void);
static void gcov_handler(int signum) {
  __gcov_flush();
  exit(1);
}
#else
#define DLOG(s...)
#endif

#define BUF_PUT8(p, v) do {                                         \
  *p = v;                                                           \
  p++;                                                              \
} while (0)

#define BUF_PUT16(p, v) do {                                        \
  BUF_PUT8(p, (v & 0xff00) >> 8);                                   \
  BUF_PUT8(p, v & 0x00ff);                                          \
} while (0)

int main(int argc, char **argv) {
  fd_set readset, errorset;
  int max_fd;

#ifdef DEBUG
  signal(SIGTERM, gcov_handler);
#endif

  memset(&id_addr_queue, 0, sizeof(id_addr_queue));
  if (0 != parse_args(argc, argv))
    return EXIT_FAILURE;
  if (0 != parse_chnroute())
    return EXIT_FAILURE;
  if (0 != resolve_dns_server())
    return EXIT_FAILURE;
  if (0 != resolve_ecs_addrs())
    return EXIT_FAILURE;
  if (0 != dns_init_sockets())
    return EXIT_FAILURE;

  max_fd = MAX(local_sock, remote_sock) + 1;
  while (1) {
    FD_ZERO(&readset);
    FD_ZERO(&errorset);
    FD_SET(local_sock, &readset);
    FD_SET(local_sock, &errorset);
    FD_SET(remote_sock, &readset);
    FD_SET(remote_sock, &errorset);
    struct timeval timeout = {
      .tv_sec = 0,
      .tv_usec = 50 * 1000,
    };
    if (-1 == select(max_fd, &readset, NULL, &errorset, &timeout)) {
      ERR("select");
      return EXIT_FAILURE;
    }
    check_and_send_delay();
    if (FD_ISSET(local_sock, &errorset)) {
      // TODO getsockopt(..., SO_ERROR, ...);
      VERR("local_sock error\n");
      return EXIT_FAILURE;
    }
    if (FD_ISSET(remote_sock, &errorset)) {
      // TODO getsockopt(..., SO_ERROR, ...);
      VERR("remote_sock error\n");
      return EXIT_FAILURE;
    }
    if (FD_ISSET(local_sock, &readset))
      dns_handle_local();
    if (FD_ISSET(remote_sock, &readset))
      dns_handle_remote();
  }
  return EXIT_SUCCESS;
}

static int setnonblock(int sock) {
  int flags;
  flags = fcntl(sock, F_GETFL, 0);
  if (flags == -1) {
    ERR("fcntl");
    return -1;
  }
  if (-1 == fcntl(sock, F_SETFL, flags | O_NONBLOCK)) {
    ERR("fcntl");
    return -1;
  }
  return 0;
}

static int parse_args(int argc, char **argv) {
  int ch;
  while ((ch = getopt(argc, argv, "hb:p:s:c:y:e:vV")) != -1) {
    switch (ch) {
      case 'h':
        usage();
        exit(0);
      case 'b':
        listen_addr = strdup(optarg);
        break;
      case 'p':
        listen_port = strdup(optarg);
        break;
      case 's':
        dns_server = strdup(optarg);
        break;
      case 'c':
        chnroute_file = strdup(optarg);
        break;
      case 'y':
        result_delay = atof(optarg);
        break;
      case 'e':
        edns_client_ip = strdup(optarg);
        break;
      case 'v':
        verbose = 1;
        break;
      case 'V':
        printf("ChinaDNS %s\n", PACKAGE_VERSION);
        exit(0);
    }
  }
  if (dns_server == NULL) {
    dns_server = strdup(default_dns_server);
  }
  if (listen_addr == NULL) {
    listen_addr = strdup(default_listen_addr);
  }
  if (listen_port == NULL) {
    listen_port = strdup(default_listen_port);
  }
  if (chnroute_file == NULL) {
    VERR("chnroute file not specified.\n");
    return 1;
  }
  if (edns_client_ip == NULL) {
    VERR("EDNS Client Subnet not specified.\n");
    return 1;
  }
  return 0;
}

static int resolve_dns_server() {
  struct addrinfo hints;
  int r;
  memset(&hints, 0, sizeof(hints));
  hints.ai_family = AF_INET;
  hints.ai_socktype = SOCK_DGRAM; /* Datagram socket */
  char *port;
  if ((port = (strrchr(dns_server, '#'))) ||
      (port = (strrchr(dns_server, ':')))) {
    *port = '\0';
    port++;
  } else {
    port = "53";
  }
  if (0 != (r = getaddrinfo(dns_server, port, &hints, &dns_server_addr))) {
    VERR("%s:%s\n", gai_strerror(r), dns_server);
    return -1;
  }
  return 0;
}

static int cmp_net_mask(const void *a, const void *b) {
  net_mask_t *neta = (net_mask_t *)a;
  net_mask_t *netb = (net_mask_t *)b;
  if (neta->net.s_addr == netb->net.s_addr)
    return 0;
  if (ntohl(neta->net.s_addr) > ntohl(netb->net.s_addr))
    return 1;
  return -1;
}

static int parse_chnroute() {
  FILE *fp;
  char line_buf[32];
  char *line;
  size_t len = sizeof(line_buf);
  char net[32];
  chnroute_list.entries = 0;
  int i = 0;
  int cidr;

  fp = fopen(chnroute_file, "rb");
  if (fp == NULL) {
    ERR("fopen");
    VERR("Can't open chnroute: %s\n", chnroute_file);
    return -1;
  }
  while ((line = fgets(line_buf, len, fp))) {
    chnroute_list.entries++;
  }

  chnroute_list.nets = calloc(chnroute_list.entries, sizeof(net_mask_t));
  if (0 != fseek(fp, 0, SEEK_SET)) {
    VERR("fseek");
    return -1;
  }
  while ((line = fgets(line_buf, len, fp))) {
    char *sp_pos;
    sp_pos = strchr(line, '\r');
    if (sp_pos) *sp_pos = 0;
    sp_pos = strchr(line, '\n');
    if (sp_pos) *sp_pos = 0;
    sp_pos = strchr(line, '/');
    if (sp_pos) {
      *sp_pos = 0;
      cidr = atoi(sp_pos + 1);
      if (cidr > 0) {
        chnroute_list.nets[i].mask = (1 << (32 - cidr)) - 1;
      } else {
        chnroute_list.nets[i].mask = UINT32_MAX;
      }
    } else {
      chnroute_list.nets[i].mask = NETMASK_MIN;
    }
    if (0 == inet_aton(line, &chnroute_list.nets[i].net)) {
      VERR("invalid addr %s in %s:%d\n", line, chnroute_file, i + 1);
      return 1;
    }
    i++;
  }

  qsort(chnroute_list.nets, chnroute_list.entries, sizeof(net_mask_t),
        cmp_net_mask);

  fclose(fp);
  return 0;
}

static int test_ip_in_list(struct in_addr ip, const net_list_t *netlist) {
  // binary search
  int l = 0, r = netlist->entries - 1;
  int m, cmp;
  if (netlist->entries == 0)
    return 0;
  net_mask_t ip_net;
  ip_net.net = ip;
  while (l <= r) {
    m = (l + r) >> 1;
    cmp = cmp_net_mask(&netlist->nets[m], &ip_net);
    if (cmp < 0)
      l = m + 1;
    else if (cmp > 0)
      r = m - 1;
    else
      return 1;
#ifdef DEBUG
    DLOG("l=%d, r=%d\n", l, r);
    DLOG("%s, %d\n", inet_ntoa(netlist->nets[m].net), netlist->nets[m].mask);
#endif
  }
#ifdef DEBUG
  DLOG("nets: %x <-> %x\n", ntohl(netlist->nets[l - 1].net.s_addr),
       ntohl(ip.s_addr));
  DLOG("mask: %x\n", netlist->nets[l - 1].mask);
#endif
  if (0 == l || (ntohl(ip.s_addr) > (ntohl(netlist->nets[l - 1].net.s_addr)
                                     | netlist->nets[l - 1].mask))) {
    return 0;
  }
  return 1;
}

static int dns_init_sockets() {
  struct addrinfo hints;
  struct addrinfo *addr_ip;
  int r;

  local_sock = socket(AF_INET, SOCK_DGRAM, IPPROTO_UDP);
  if (0 != setnonblock(local_sock))
    return -1;
  memset(&hints, 0, sizeof(hints));
  hints.ai_family = AF_INET;
  hints.ai_socktype = SOCK_DGRAM;
  if (0 != (r = getaddrinfo(listen_addr, listen_port, &hints, &addr_ip))) {
    VERR("%s:%s:%s\n", gai_strerror(r), listen_addr, listen_port);
    return -1;
  }
  if (0 != bind(local_sock, addr_ip->ai_addr, addr_ip->ai_addrlen)) {
    ERR("bind");
    VERR("Can't bind address %s:%s\n", listen_addr, listen_port);
    return -1;
  }
  freeaddrinfo(addr_ip);
  remote_sock = socket(AF_INET, SOCK_DGRAM, IPPROTO_UDP);
  if (0 != setnonblock(remote_sock))
    return -1;
  return 0;
}

static void send_request(ecs_addr_t ecs, ssize_t len) {
  add_ecs_data(global_buf + len, &ecs.addrs, 32);

  if (-1 == sendto(remote_sock, global_buf, len + ECS_DATA_LEN, 0,
                   dns_server_addr->ai_addr, dns_server_addr->ai_addrlen))
    ERR("sendto");
}

static void dns_handle_local() {
  struct sockaddr *src_addr = malloc(sizeof(struct sockaddr));
  socklen_t src_addrlen = sizeof(struct sockaddr);
  uint16_t query_id;
  ssize_t len;
  int i;
  const char *question_hostname;
  ns_msg msg;
  len = recvfrom(local_sock, global_buf, BUF_SIZE, 0, src_addr, &src_addrlen);
  if (len > 0) {
    if (local_ns_initparse((const u_char *)global_buf, len, &msg) < 0) {
      ERR("local_ns_initparse");
      free(src_addr);
      return;
    }
    // parse DNS query id
    query_id = ns_msg_id(msg);
    if (verbose) {
      question_hostname = hostname_from_question(msg);
      if (question_hostname)
        LOG("query %s\n", question_hostname);
    }
    // assign a new id
    uint16_t new_id;
    do {
      struct timeval tv;
      gettimeofday(&tv, 0);
      int randombits = (tv.tv_sec << 8) ^ tv.tv_usec;
      new_id = randombits & 0xffff;
    } while (queue_lookup(new_id));

    uint16_t ns_new_id = htons(new_id);
    memcpy(global_buf, &ns_new_id, 2);

    id_addr_t id_addr;
    id_addr.id = new_id;
    id_addr.old_id = query_id;
    id_addr.addr = src_addr;
    id_addr.addrlen = src_addrlen;
    queue_add(id_addr);
    // Set Additional RRs count
    if (*(global_buf + 11) == 1) {
      if (((*(global_buf + len - 1)) | (*(global_buf + len - 2))) == 0)
        len -= 11;
    } else
      (*(global_buf + 11))++;

    for (i = 0; i < ecs_list.entries; i++)
      send_request(ecs_list.ecs_addrs[i], len);
  } else {
    ERR("recvfrom");
    free(src_addr);
  }
}

static void dns_handle_remote() {
  struct sockaddr *src_addr = malloc(sizeof(struct sockaddr));
  socklen_t src_len = sizeof(struct sockaddr);
  uint16_t query_id;
  ssize_t len;
  const char *question_hostname;
  int r, is_chn;
  ns_msg msg;
  len = recvfrom(remote_sock, global_buf, BUF_SIZE, 0, src_addr, &src_len);
  if (len > 0) {
    if (local_ns_initparse((const u_char *)global_buf, len, &msg) < 0) {
      ERR("local_ns_initparse");
      free(src_addr);
      return;
    }
    // parse DNS query id
    query_id = ns_msg_id(msg);
    if (verbose) {
      question_hostname = hostname_from_question(msg);
      if (question_hostname)
        LOG("answer %s -> ", question_hostname);
    }
    is_chn = check_result(global_buf, len);
    if (-1 == is_chn) {
      if (verbose)
        printf("Fake, drop\n");
      free(src_addr);
      return;
    }
    id_addr_t *id_addr = queue_lookup(query_id);
    if (id_addr) {
      id_addr->addr->sa_family = AF_INET;
      uint16_t ns_old_id = htons(id_addr->old_id);
      memcpy(global_buf, &ns_old_id, 2);
      r = should_filter_query(msg, is_chn);
      if (r == 0) {
        if (verbose)
          printf("pass\n");
        if (-1 == sendto(local_sock, global_buf, len, 0, id_addr->addr,
                         id_addr->addrlen))
          ERR("sendto");
      } else if (r == -1) {
        if (verbose)
          printf("delay\n");
        schedule_delay(query_id, global_buf, len, id_addr->addr,
                       id_addr->addrlen);
      } else {
        if (verbose)
          printf("filter\n");
      }
    } else {
      if (verbose)
        printf("miss\n");
    }
  }
  else
    ERR("recvfrom");
  free(src_addr);
}

static void queue_add(id_addr_t id_addr) {
  // free next hole
  id_addr_t old_id_addr = id_addr_queue[id_addr_queue_pos];
  free(old_id_addr.addr);
  id_addr_queue[id_addr_queue_pos] = id_addr;
  id_addr_queue_pos = (id_addr_queue_pos + 1) % ID_ADDR_QUEUE_LEN;
}

static id_addr_t *queue_lookup(uint16_t id) {
  int i;
  for (i = 0; i < ID_ADDR_QUEUE_LEN; i++) {
    if (id_addr_queue[i].id == id)
      return id_addr_queue + i;
  }
  return NULL;
}

static char *hostname_buf = NULL;
static size_t hostname_buflen = 0;
static const char *hostname_from_question(ns_msg msg) {
  ns_rr rr;
  int rrnum, rrmax;
  const char *result;
  int result_len;
  rrmax = ns_msg_count(msg, ns_s_qd);
  if (rrmax == 0)
    return NULL;
  for (rrnum = 0; rrnum < rrmax; rrnum++) {
    if (local_ns_parserr(&msg, ns_s_qd, rrnum, &rr)) {
      ERR("local_ns_parserr");
      return NULL;
    }
    result = ns_rr_name(rr);
    result_len = strlen(result) + 1;
    if (result_len > hostname_buflen) {
      hostname_buflen = result_len << 1;
      hostname_buf = realloc(hostname_buf, hostname_buflen);
    }
    memcpy(hostname_buf, result, result_len);
    return hostname_buf;
  }
  return NULL;
}

static int should_filter_query(ns_msg msg, int is_chn) {
  ns_rr rr;
  int rrnum, rrmax;
  rrmax = ns_msg_count(msg, ns_s_an);
  if (verbose) {
    printf("(%s) ", is_chn ? "C" : "F");
    if (rrmax == 0)
      printf("Empty, ");
  }
  for (rrnum = 0; rrnum < rrmax; rrnum++) {
    if (local_ns_parserr(&msg, ns_s_an, rrnum, &rr)) {
      ERR("local_ns_parserr");
      return 0;
    }
    u_int type;
    const u_char *rd;
    type = ns_rr_type(rr);
    rd = ns_rr_rdata(rr);
    if (type == ns_t_a) {
      if (verbose)
        printf("%s, ", inet_ntoa(*(struct in_addr *)rd));
      if (test_ip_in_list(*(struct in_addr *)rd, &chnroute_list)) {
        return is_chn ? 0 : -1;
      } else {
        return is_chn ? 1 : -1;
      }
    }
  }
  if (verbose && rrmax > 0)
    printf("Non-IPv4, ");
  return 0;
}

static void schedule_delay(uint16_t query_id, const char *buf, size_t buflen,
                           struct sockaddr *addr, socklen_t addrlen) {
  int i;
  int found = 0;
  struct timeval now;
  gettimeofday(&now, 0);

  delay_buf_t *delay_buf = &delay_queue[delay_queue_last];

  // first search for existed item with query_id and replace it
  for (i = delay_queue_first;
       i != delay_queue_last;
       i = (i + 1) % DELAY_QUEUE_LEN) {
    delay_buf_t *delay_buf2 = &delay_queue[i];
    if (delay_buf2->id == query_id) {
      free_delay(i);
      delay_buf = &delay_queue[i];
      found = 1;
    }
  }

  delay_buf->id = query_id;
  delay_buf->ts = now;
  delay_buf->buf = malloc(buflen);
  memcpy(delay_buf->buf, buf, buflen);
  delay_buf->buflen = buflen;
  delay_buf->addr = malloc(addrlen);
  memcpy(delay_buf->addr, addr, addrlen);
  delay_buf->addrlen = addrlen;

  // then append to queue
  if (!found) {
    delay_queue_last = (delay_queue_last + 1) % DELAY_QUEUE_LEN;
    if (delay_queue_last == delay_queue_first) {
      free_delay(delay_queue_first);
      delay_queue_first = (delay_queue_first + 1) % DELAY_QUEUE_LEN;
    }
  }
}

float time_diff(struct timeval t0, struct timeval t1) {
  return (t1.tv_sec - t0.tv_sec) +
      (t1.tv_usec - t0.tv_usec) / 1000000.0f;
}

static void check_and_send_delay() {
  struct timeval now;
  int i;
  gettimeofday(&now, 0);
  for (i = delay_queue_first;
       i != delay_queue_last;
       i = (i + 1) % DELAY_QUEUE_LEN) {
    delay_buf_t *delay_buf = &delay_queue[i];
    if (time_diff(delay_buf->ts, now) > result_delay) {
      if (-1 == sendto(local_sock, delay_buf->buf, delay_buf->buflen, 0,
                       delay_buf->addr, delay_buf->addrlen))
        ERR("sendto");
      free_delay(i);
      delay_queue_first = (delay_queue_first + 1) % DELAY_QUEUE_LEN;
    } else {
      break;
    }
  }
}

static void free_delay(int pos) {
  free(delay_queue[pos].buf);
  free(delay_queue[pos].addr);
}

static int resolve_ecs_addrs() {
  char* token;
  char *pch = strchr(edns_client_ip, ',');
  int i = 0, has_chn = 0, has_foreign = 0;
  ecs_list.entries = 1;
  while (pch != NULL) {
    ecs_list.entries++;
    pch = strchr(pch + 1, ',');
  }
  ecs_list.ecs_addrs = calloc(ecs_list.entries, sizeof(ecs_addr_t));
  token = strtok(edns_client_ip, ",");
  while (token) {
    inet_aton(token, &ecs_list.ecs_addrs[i].addrs);
    ecs_list.ecs_addrs[i].is_chn = test_ip_in_list(ecs_list.ecs_addrs[i].addrs,
                                                   &chnroute_list);
    if (ecs_list.ecs_addrs[i].is_chn) {
      has_chn = 1;
    } else {
      has_foreign = 1;
    }
    token = strtok(NULL, ",");
    i++;
  }
  if (!(has_chn && has_foreign)) {
    VERR("You should have at least one Chinese Client Subnet and"
         " one foreign Client Subnet\n");
    return 1;
  }
  return 0;
}

static void add_ecs_data(char *buf_ptr, struct in_addr *addr, uint8_t mask) {
  // Set Name: <Root>
  BUF_PUT8(buf_ptr, 0);
  // Set Type: OPT (41)
  BUF_PUT16(buf_ptr, 41);
  // Set UDP payload size: 4096
  BUF_PUT16(buf_ptr, 4096);
  // Set Higher bits in extended RCODE: 0x00
  BUF_PUT8(buf_ptr, 0);
  // Set EDNS0 version: 0
  BUF_PUT8(buf_ptr, 0);
  // Set Z: 0x0000
  BUF_PUT16(buf_ptr, 0);
  // Set Data length: 12
  BUF_PUT16(buf_ptr, 12);
  // Set RData
  // The after things are in the example of <Client Subnet in DNS Requests>
  size_t addrl = (mask + 7) / 8;
  // Set Option Code: CSUBNET - Client subnet (8)
  BUF_PUT16(buf_ptr, 8);
  // Set Option Length
  BUF_PUT16(buf_ptr, 4 + addrl);
  // Set Family: IPv4 (1)
  BUF_PUT16(buf_ptr, 1);
  // Set Source Netmask
  BUF_PUT8(buf_ptr, mask);
  // Set Scope Netmask: 0
  BUF_PUT8(buf_ptr, 0);
  // Set Client Subnet Information
  memcpy(buf_ptr, addr, addrl);
}

static int check_result(char *buf, size_t buflen) {
  int i;
  size_t addrl = sizeof(struct in_addr);
  struct in_addr *addr = malloc(addrl);
  memcpy(addr, buf + buflen - addrl, addrl);
  for (i = 0; i < ecs_list.entries; i++) {
    if (addr->s_addr == ecs_list.ecs_addrs[i].addrs.s_addr) {
      free(addr);
      return ecs_list.ecs_addrs[i].is_chn;
    }
  }
  free(addr);
  return -1;
}

static void usage() {
  printf("%s\n", "\
usage: chinadns [-c CHNROUTE_FILE] [-e CLIENT_SUBNET]\n\
       [-b BIND_ADDR] [-p BIND_PORT] [-s DNS] [-h] [-v] [-V]\n\
Forward DNS requests.\n\
\n\
  -c CHNROUTE_FILE      path to china route file\n\
  -y DELAY_TIME         delay time for foreign result, default: 0.3\n\
  -b BIND_ADDR          address that listens, default: 0.0.0.0\n\
  -p BIND_PORT          port that listens, default: 53\n\
  -s DNS                DNS server to use, default: 8.8.8.8\n\
  -e ADDRs              set edns-client-subnet\n\
  -v                    verbose logging\n\
  -h                    show this help message and exit\n\
  -V                    print version and exit\n\
\n\
Online help: <https://github.com/shadowsocks/ChinaDNS>\n");
}
