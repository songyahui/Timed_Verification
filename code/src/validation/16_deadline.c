#include "primitives.c"

// Should Succeed 
void callee () 
/*
req: TRUE∧(_^*)
ens: TRUE∧(A . B)
*/
{
    event["A"];
    event["B"];
}

// Should Succeed 
void test_deadline6(int n) 
/*
req: TRUE∧(_^*)
ens: (t≤n)∧ ((A.B) # t)
*/
{
    deadline (callee ()  ,n);
}