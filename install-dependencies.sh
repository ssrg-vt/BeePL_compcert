sudo apt update
sudo apt install opam
opam init --compiler=4.12.1
eval $(opam env)
opam install coq=9.0.0
opam install menhir
opam repo add coq-released https://coq.inria.fr/opam/released 
opam install coq-mathcomp-ssreflect
sudo apt install llvm
export LIBRARY_PATH="$PWD/runtime/:$LIBRARY_PATH"
