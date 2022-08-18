include ../../Makefile.config

CC=../../ccomp 
CFLAGS=$(CCOMPOPTS) -stdlib ../../runtime -dparse -dclight -dasm -fstruct-return -dall -fno-jump-tables
LIBS=$(LIBMATH)
TIME=ocaml unix.cma ../../tools/xtime.ml -mintime 2.0 -minruns 4

OBJS=memory.o    \
  arrays.o       \
 main.o

# Use float
# gmllexer.o vector.o matrix.o object.o intersect.o surface.o   simplify.o  render.o
# Use memcpy
# gmlparser.o light.o
# Ill-formed LTL?
# eval.o

all: render

render: $(OBJS)
	$(CC) $(CFLAGS) -o render $(OBJS) $(LIBS)

clean:
	rm -f *.o *.parsed.c *.light.c *.s *.sdump *.ppm render

include .depend

depend:
	gcc -MM *.c > .depend

test:
	$(SIMU) ./render < kal.gml
	@if cmp kal.ppm Results/kal.ppm; \
        then echo "raytracer: passed"; \
        else echo "raytracer: FAILED"; exit 2; \
        fi

bench:
	@$(TIME) -name raytracer -- sh -c './render < kal.gml'
