#include<stdio.h> 

#include <stdlib.h>

int gb = 5; 

int main() { 
    int* ptr; 
    int* gbptr = &gb;
    //Declaring malloc() function to dynamically allocate memory 
    ptr = (int*) malloc (10 * sizeof(int)); 
    if(ptr==NULL) 
    { printf("Sorry....No Space. \n"); } 
    else { printf("Successful Memory Allocation \n"); 
           //Assigning value to the pointer ptr 
           for(int i=1;i<=5;i++) { 
            ptr[i] = i; } 
    //Printing the array elements 
    printf("The array elements are: \n"); 
    for(int i=1;i<=5;i++) { 
        printf("%d\n", ptr[i]); } 
    } 
    //printf("The local pointer is %p", ptr);
    printf("The global pointer is %p", gbptr);
}