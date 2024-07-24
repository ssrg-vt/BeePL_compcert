#include <stdio.h>
#include<stdint.h>

/*
int main() {
    int val1 = 0xbeef;
    int val2 = 5;
    int result = val1 >> val2;
    printf("The result is %x", result);
    return 0;
}*/

int64_t main() {
    int64_t val1 = 64;
    int64_t val2 = 32;
    int64_t result = val1 >> val2;
    printf("The result is %lld", result);
    return 0;
}

// 1527
// hex(1527) '0x5f7'
// ./ccomp -D __bpf_helper_as_extern__ -S -o ebpf/test/simpl_test/test_shr.s ebpf/test/simpl_test/test_shr.c 