#include <stdio.h>
#include <memory.h>

int main() {
    int src = 4;
    int dst = 5;
    int kind = 3;

    char char_array[20];

    memcpy(char_array, &src, sizeof(int));
    memcpy(char_array + sizeof(int), &dst, sizeof(int)) ;
    memcpy(char_array + sizeof(int) * 2, &kind, sizeof(int));

    char *ptr = char_array;
    char *ptr_end = char_array + sizeof(char_array);

    if (ptr + sizeof(int) > ptr_end)
        return -1;
    printf("src: %d\n", *(int *)ptr);

    if (ptr + sizeof(int) * 2 > ptr_end)
        return -2;
    printf("dst: %d\n", *((int *)ptr + 1));

    if (ptr + sizeof(int) * 3 > ptr_end)
        return -3;
    printf("kind: %d\n", *((int *)ptr + 2));


    printf("src: %p and char_array base:%p\n", (int *)ptr, char_array);;
    printf("dst: %p\n", ((int *)ptr + 1));
    printf("kind: %p\n", ((int *)ptr + 2));

    return 0;
}
