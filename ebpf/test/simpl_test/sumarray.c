#include <stdio.h>
#include <stdint.h>

unsigned sumarray (unsigned a[], int n) {
    int i;
    unsigned s;
    i = 0; 
    s = 0;
    while (i < n) {
        s += a[i];
        i++;
    }
    return s;
}

unsigned four[4] = {1,2,3,4};

int main() {
    unsigned s;
    s = sumarray(four,4);
    return s;
}

// ./ccomp -D __bpf_helper_as_extern__ -S -o ebpf/test/simpl_test/sumarray.s ebpf/test/simpl_test/sumarray.c 
// ./clightgen -normalize ebpf/test/simpl_test/sumarray.c 