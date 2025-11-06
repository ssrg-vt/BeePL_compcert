struct xdp_md;
struct xdp_md {
  unsigned int _data;
  unsigned int _data_end;
  unsigned int _data_meta;
  unsigned int _ingress_ifindex;
  unsigned int _rx_queue_index;
  unsigned int _egress_ifindex;
};

extern signed char _license[4];

extern int xdp_prog(struct xdp_md *);

extern signed char const __stringlit_0[7];

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

extern unsigned long long bpf_get_current_pid_tgid(void);

extern unsigned int bpf_get_prandom_u32(void);

extern unsigned long long bpf_ktime_get_ns(void);

extern int bpf_printk(signed char *, int, ...);

extern int printf(signed char *, ...);

signed char _license[4] = { 71, 80, 76, 92, 48, 0, };

int xdp_prog(struct xdp_md *p)
{
  int d;
  d = bpf_printk(__stringlit_0, 6);
  return 2;
}

signed char const __stringlit_0[7] = "Hello!";


