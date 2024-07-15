int simple() {
    return 0;
}

// ./ccomp -D __bpf_helper_as_extern__ -S -o ebpf/test/simple/simple.s ebpf/test/simple/simple.c 