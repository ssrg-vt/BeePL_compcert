# CompCert
The formally-verified C compiler.

## Overview
The CompCert C verified compiler is a compiler for a large subset of the
C programming language that generates code for the PowerPC, ARM, x86 and
RISC-V processors.

The distinguishing feature of CompCert is that it has been formally
verified using the Coq proof assistant: the generated assembly code is
formally guaranteed to behave as prescribed by the semantics of the
source C code.

For more information on CompCert (supported platforms, supported C
features, installation instructions, using the compiler, etc), please
refer to the [Web site](https://compcert.org/) and especially
the [user's manual](https://compcert.org/man/).

## License
CompCert is not free software.  This non-commercial release can only
be used for evaluation, research, educational and personal purposes.
A commercial version of CompCert, without this restriction and with
professional support and extra features, can be purchased from
[AbsInt](https://www.absint.com).  See the file `LICENSE` for more
information.

## Copyright
The CompCert verified compiler is Copyright Institut National de
Recherche en Informatique et en Automatique (INRIA) and 
AbsInt Angewandte Informatik GmbH.


## Contact
General discussions on CompCert take place on the
[compcert-users@inria.fr](https://sympa.inria.fr/sympa/info/compcert-users)
mailing list.

For inquiries on the commercial version of CompCert, please contact
info@absint.com


## BeePL
To compile a BeePL program run CompCert with a file that ends in `.bpl`.
```
./ccomp test.bpl
```

To compile a BeePL (AST) program run CompCert with a file that ends in `.b`. 
```
./ccomp ~/test.b
```
The contents of the file do not matter. The `.b` suffix tells the driver to call 
`process_b_file` which in turn calls `compile_b_file`. The program compiled is
hard coded in `compile_b_file` and passed to `transf_beepl_program_csyntax`. The 
hard coded program in `compile_b_file` is defined in `BeePL_progs.v`.

To pretty print csyntax: `./ccomp ~/test.b -dc`

#### Add a new test file

1) Add a Coq file to `compiler_test/beepl_test`
2) In `Makefile` add the file to the list of `BEEPL_TESTS`
3) In `BeePL_progs.v` `Require Import` the file
4) Define the BeePL AST in the newly created Coq file
5) Modify the required lines in `BeePL_progs.v` so the correct program gets extracted

# eBPF helper mapping (`-bpfmap`)

When compiling **for the `ebpf64` target**, add the `-bpfmap` flag to `ccomp` (e.g. `./ccomp test.bpl -bpfmap`). With `-bpfmap` the driver automatically replaces explicit eBPF helper function names with their numeric helper IDs as defined in `linux/bpf.h`, producing an object file ready for loading. If you omit `-bpfmap`, you must manually replace helper calls with their numeric codes in the generated eBPF bytecode and recompile to produce a correct object file.

#### Running the typechecker

Add `-typecheck` to your command line to run the typechecker.

Full example: `./ccomp ../test.b -o test -typecheck`
