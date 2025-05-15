struct xdp_md;
struct xdp_md {
  unsigned int data;
  unsigned int data_end;
  unsigned int data_meta;
  unsigned int ingress_ifindex;
  unsigned int rx_queue_index;
  unsigned int egress_ifindex;
};

extern unsigned int val;

extern unsigned int *counter;

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

unsigned int val = 0;

unsigned int *counter = &val;

int xdp_packet_count(struct xdp_md *ctx)
{
  int r;
  *counter = *counter + 1;
  return 2;
}
