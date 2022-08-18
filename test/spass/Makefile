include ../../Makefile.config

CC=../../ccomp 
CFLAGS=$(CCOMPOPTS) -stdlib ../../runtime -dall -fstruct-return -fno-jump-tables -Os

SRCS=analyze.c component.c                 \
  condensing.c context.c dfgscanner.c doc-proof.c        \
  flags.c graph.c hasharray.c iascanner.c        \
  memory.c misc.c options.c  \
  proofcheck.c renaming.c resolution.c rpos.c        \
  rules-split.c  search.c sharing.c        \
  stack.c  subst.c  symbol.c table.c tableau.c        \
  unify.c closure.c  cnf.c partition.c sort.c  \
  defs.c  foldfg.c   kbo.c order.c rules-inf.c    rules-sort.c rules-ur.c \
  subsumption.c   terminator.c 

all: spass

# use indirect calls
# clause.c  hash.c list.c st.c term.c vector.c
# use float
# clock.c strings.c top.c rules-red.c 
# use mulhs
# 
# use more than 5 args
# defs.c  foldfg.c   kbo.c order.c rules-inf.c  rules-red.c   rules-sort.c rules-ur.c
# 
# use memcpy
# dfgparser.c  iaparser.c

spass: $(SRCS:.c=.o)
	$(CC) $(CFLAGS) -o spass $(SRCS:.c=.o) $(LIBMATH)

clean:
	rm -f spass
	rm -f *.o *.s *.parsed.c *.light.c *.sdump

test:
	$(SIMU) ./spass small_problem.dfg | grep 'Proof found'

TIME=ocaml unix.cma ../../tools/xtime.ml -o /dev/null -mintime 5.0

bench:
	@$(TIME) -name spass -- ./spass problem.dfg

depend:
	gcc -MM $(SRCS) > .depend

include .depend
