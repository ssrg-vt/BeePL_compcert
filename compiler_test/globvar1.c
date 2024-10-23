// C program to update global variables
#include <stdio.h>
 
int a, b; // global variables
 
void add()
{ // we are adding values of global a and b i.e. 10+15
    printf("%d", a + b);
}
 
int main()
{
    // we are now updating the values of global variables
    // as you can see we dont need to redeclare a and b
    // again
    a = 10;
    b = 15;
    add();
    return 0;
}
