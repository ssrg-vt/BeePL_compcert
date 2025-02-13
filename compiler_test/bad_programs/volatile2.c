#include <stdio.h>

volatile int shared_var = 10;  // Volatile global variable

void read_from_volatile() {
    volatile int *ptr = &shared_var;  // Pointer to volatile int

    int value = *ptr;  // Dereference on RHS, ensures fresh read from memory

    printf("Read value: %d\n", value);
}

int main() {
    read_from_volatile();
    return 0;
}

