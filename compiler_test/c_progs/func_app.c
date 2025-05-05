#include <stdio.h>

// Define a function
int add(int x, int y) {
    return x + y;
}

int main() {
    int result = add(3, 4);  // direct call
    printf("Result: %d\n", result);
    return 0;
}

