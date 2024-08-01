#include<stdio.h> 

#include <stdlib.h>

volatile int gb = 5; 

int main(int argc, char *argv[]) {
    int x = gb + 1;
    gb = gb + argc;
    printf("This is will trigger an event %d and %d\n", x, gb);
    return 0;
}

/* 
Time 6: observable event: volatile load int32[&gb+0] -> 5
Time 14: observable event: volatile load int32[&gb+0] -> 5
Time 16: observable event: volatile store int32[&gb+0] <- 6
Time 27: observable event: volatile load int32[&gb+0] -> 6
This is will trigger an event 6 and 6

Time 28: observable event: extcall printf(& __stringlit_1, 6, 6) -> 38
Time 33: program terminated (exit code = 0)
*/

// int main() { 
//     int* ptr; 
//     int* gbptr = &gb;
//     //Declaring malloc() function to dynamically allocate memory 
//     ptr = (int*) malloc (10 * sizeof(int)); 
//     if(ptr==NULL) 
//     { printf("Sorry....No Space. \n"); } 
//     else { printf("Successful Memory Allocation \n"); 
//            //Assigning value to the pointer ptr 
//            for(int i=1;i<=5;i++) { 
//             ptr[i] = i; } 
//     //Printing the array elements 
//     printf("The array elements are: \n"); 
//     for(int i=1;i<=5;i++) { 
//         printf("%d\n", ptr[i]); } 
//     } 
//     //printf("The local pointer is %p", ptr);
//     printf("The global pointer is %p", gbptr);
// }