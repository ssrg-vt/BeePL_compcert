struct bytes_t;
struct xdp_md;
struct xdp_md_bee;
struct eth_hdr;
struct bytes_t {
  unsigned char *bytes_start;
  unsigned char *bytes_end;
};

struct xdp_md {
  unsigned int data;
  unsigned int data_end;
  unsigned int data_meta;
  unsigned int ingress_ifindex;
  unsigned int rx_queue_index;
  unsigned int egress_ifindex;
};

struct xdp_md_bee {
  struct bytes_t data_bee;
  unsigned int data_meta;
  unsigned int ingress_ifindex;
  unsigned int rx_queue_index;
  unsigned int egress_ifindex;
};

struct eth_hdr {
  unsigned char h_dest[6];
  unsigned char h_source[6];
  unsigned short h_proto;
};

extern int xdp_drop_prog(struct xdp_md *);

extern unsigned int __compcert_va_int32(void *);

extern unsigned long long __compcert_va_int64(void *);

extern double __compcert_va_float64(void *);

extern void *__compcert_va_composite(void *, unsigned long long);

extern long long __compcert_i64_dtos(double);

extern unsigned long long __compcert_i64_dtou(double);

extern double __compcert_i64_stod(long long);

extern double __compcert_i64_utod(unsigned long long);

extern float __compcert_i64_stof(long long);

extern float __compcert_i64_utof(unsigned long long);

extern long long __compcert_i64_sdiv(long long, long long);

extern unsigned long long __compcert_i64_udiv(unsigned long long, unsigned long long);

extern long long __compcert_i64_smod(long long, long long);

extern unsigned long long __compcert_i64_umod(unsigned long long, unsigned long long);

extern long long __compcert_i64_shl(long long, int);

extern unsigned long long __compcert_i64_shr(unsigned long long, int);

extern long long __compcert_i64_sar(long long, int);

extern long long __compcert_i64_smulh(long long, long long);

extern unsigned long long __compcert_i64_umulh(unsigned long long, unsigned long long);

extern unsigned short htons(unsigned short);

int xdp_drop_prog(struct xdp_md *ctx)
{
  struct eth_hdr *__fresh__999;
  struct xdp_md_bee __fresh__1000;
  struct eth_hdr eth;
  struct bytes_t data;
  unsigned short hproto;
  __fresh__1000.data_bee.bytes_start = (unsigned char *) ((*ctx)).data;
  __fresh__1000.data_bee.bytes_end = (unsigned char *) ((*ctx)).data_end;
  if (__fresh__1000.data_bee.bytes_start + sizeof(struct eth_hdr)
        > __fresh__1000.data_bee.bytes_end) {
    return 1;
  } else {
    __fresh__999 = (struct eth_hdr *) __fresh__1000.data_bee.bytes_start;
    eth.h_proto = ((*__fresh__999)).h_proto;
    /*skip*/;
    __fresh__1000.data_bee.bytes_start =
      __fresh__1000.data_bee.bytes_start + sizeof(struct eth_hdr);
    hproto = eth.h_proto;
    if (hproto == htons(34525)) {
      return 1;
    } else {
      return 2;
    }
  }
}


