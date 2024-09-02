// C program to illustrate Pointers
#include <stdio.h>
#include<stdio.h>

void lptr()
{
    int var = 10;

    // declare pointer variable
    int* ptr;

    // note that data type of ptr and var must be same
    ptr = &var;

    // assign the address of a variable to a pointer
    //printf("Value at ptr = %p \n", ptr);
    //printf("Value at var = %d \n", var);
    //printf("Value at *ptr = %d \n", *ptr);
}

// Driver program
int main()
{
    lptr();
    return 0;
}

/* Time 26: program terminated (exit code = 0) */
