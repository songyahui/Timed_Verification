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
void test_deadline_delay(int n) 
/*
req: TRUE∧(_^*)
ens: (t≤n)∧(t1>3)∧ ((A.B) # t) .Gap. (ε # t1)
*/
{
    deadline (callee ()  ,n);
    event["Gap"]; 
    delay (5)
}