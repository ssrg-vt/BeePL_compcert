#include <stdio.h>

int main() {
    int arr[5] = {1, 2, 3, 4, 5};
    int *ptr = arr;

    // Out-of-bounds write
    *(ptr + 10) = 100;
    printf("Out-of-bounds write successful\n");

    // Out-of-bounds read from the same location
    printf("Out-of-bounds read: %d\n", *(ptr + 10));

    return 0;
}
