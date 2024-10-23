#include<stdio.h>
struct BankAccount
{
   int    accNum;
   double balance;
};

struct BankAccount a;

int main(int argc, char *argv[])
{
   a.accNum  = 123;
   a.balance = 1000.0;

   printf("The balance is %d", a.balance);
   return 0;   
}
