#include <stdio.h>

// Same function as before
int add(int x, int y) {
    return x + y;
}

int main() {
    // Declare a function pointer
    int (*fp)(int, int) = add;

    // Call through the pointer
    int result = fp(3, 4);  // same as (*fp)(3, 4)
    printf("Result: %d\n", result);
    return 0;
}

