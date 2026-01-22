struct trace_entry;
struct trace_event_raw_sys_enter;
struct trace_entry {
  unsigned short type;
  unsigned char flags;
  unsigned char preempt_count;
  int pid;
};

struct trace_event_raw_sys_enter {
  struct trace_entry ent;
  long long id;
  unsigned long long args[6];
  unsigned char __data[0];
};

extern unsigned long long const pid_filter;

extern signed char const __stringlit_1[4];

extern int handle_tp(struct trace_event_raw_sys_enter *);

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

unsigned long long const pid_filter = 0LL;

signed char const __stringlit_1[4] = "%ld";

extern unsigned long long bpf_get_current_pid_tgid(void);

extern int bpf_printk(signed char *, ...);

int handle_tp(struct trace_event_raw_sys_enter *ctx)
{
  unsigned long long pid;
  unsigned long long t;
  pid = 32LLU < 64LLU ? 0LLU : bpf_get_current_pid_tgid() >> 32LLU;
  if (pid_filter) {
    if (pid_filter != pid) {
      return 0;
    } else {
      t = bpf_printk(__stringlit_1, pid);
      return 0;
    }
  } else {
    return 0;
  }
}


