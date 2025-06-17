struct xdp_md;
struct xdp_md {
  unsigned int data;
  unsigned int data_end;
  unsigned int data_meta;
  unsigned int ingress_ifindex;
  unsigned int rx_queue_index;
  unsigned int egress_ifindex;
};

extern signed char const ___license[4];

extern signed char const __stringlit_1[6];

extern int xdp_packet_count(struct xdp_md *);

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

signed char const ___license[4] = { 71, 80, 76, 0, };

signed char const __stringlit_1[6] = "Hello";

extern int bpf_printk(signed char *, ...);

int xdp_packet_count(struct xdp_md *ctx)
{
  int r;
  r = bpf_printk(__stringlit_1);
  return 2;
}


