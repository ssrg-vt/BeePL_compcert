struct $6127156262475;
struct pt_regs;
struct $6127156262475 {
  int (*$20551837)[1];
  int (*$-4354297124645891434)[5000000];
  unsigned long long *$402324;
  unsigned long long *$1316573855;
};

struct pt_regs {
  unsigned long long r15;
  unsigned long long r14;
  unsigned long long r13;
  unsigned long long r12;
  unsigned long long bp;
  unsigned long long bx;
  unsigned long long r11;
  unsigned long long r10;
  unsigned long long r9;
  unsigned long long r8;
  unsigned long long ax;
  unsigned long long cx;
  unsigned long long dx;
  unsigned long long si;
  unsigned long long di;
  unsigned long long orig_ax;
  unsigned long long ip;
  unsigned long long flags;
  unsigned long long sp;
};

extern struct $6127156262475 *counter_table;

extern struct $6127156262475 val;

extern int hash_map_example(struct pt_regs *);

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

struct $6127156262475 *counter_table = &val;

struct $6127156262475 val = { 0, };

extern unsigned long long bpf_get_current_uid_gid(void);

extern void *bpf_map_lookup_elem(struct $6127156262475 *, void *);

extern unsigned long long bpf_map_update_elem(struct $6127156262475 *, void *, void *, unsigned long long);

int hash_map_example(struct pt_regs *ctx)
{
  unsigned long long __fresh__999;
  unsigned long long __fresh__1000;
  unsigned long long *uid;
  unsigned long long *counter;
  void *p;
  uid = (__fresh__999 = 0LLU, &__fresh__999);
  counter = (__fresh__1000 = 0LLU, &__fresh__1000);
  *uid = bpf_get_current_uid_gid() & 4294967295LLU;
  p = bpf_map_lookup_elem(counter_table, uid);
  if (p == (int *) 0) {
    return -1;
  } else {
    *counter = *p;
    *counter = *counter + 1LLU;
    bpf_map_update_elem(counter_table, uid, counter, 0LLU);
    return 0;
  }
}
