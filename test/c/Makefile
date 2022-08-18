include ../../Makefile.config

CCOMP=../../ccomp
CCOMPFLAGS=$(CCOMPOPTS) -fno-jump-tables -stdlib ../../runtime -dall

CFLAGS=-O1 -Wall

LIBS=$(LIBMATH)

TIME=ocaml unix.cma ../../tools/xtime.ml -o /dev/null -mintime 2.0 -minruns 4

PROGS=fib integr qsort sha1 sha3 fletcher32 \
  lists binarytrees fannkuch knucleotide mandelbrot \
  nsieve nsievebits  vmach \
  chomp perlin aes siphash24
# Use float 
# fft fftsp fftw almabench  nbody spectral bisect 

all: $(PROGS:%=%.compcert)

all_s: $(PROGS:%=%.s)

all_gcc: $(PROGS:%=%.gcc)

%.compcert: %.c
	$(CCOMP) $(CCOMPFLAGS) -o $*.compcert $*.c $(LIBS)

%.s: %.c
	$(CCOMP) $(CCOMPFLAGS) -S $*.c

%.gcc: %.c
	$(CC) $(CFLAGS) -o $*.gcc $*.c $(LIBS)

test:
	@for i in $(PROGS); do \
	   if $(SIMU) ./$$i.compcert | cmp -s - Results/$$i; \
           then echo "$$i: passed"; \
           else echo "$$i: FAILED"; exit 2; \
	   fi; \
         done

test_gcc:
	@for i in $(PROGS); do \
	   if ./$$i.gcc | cmp -s - Results/$$i; \
           then echo "$$i: passed"; \
           else echo "$$i: FAILED"; \
	   fi; \
         done

bench_gcc:
	@for i in $(PROGS); do \
	   $(TIME) -name $$i -- ./$$i.gcc; \
         done

bench:
	@for i in $(PROGS); do \
	   $(TIME) -name $$i -- ./$$i.compcert; \
         done

clean:
	rm -f *.compcert *.gcc
	rm -f *.compcert.c *.light.c *.parsed.c *.s *.o *.sdump *~ 
