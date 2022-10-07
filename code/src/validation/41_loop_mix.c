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
void test_loop1() 
/*
req: TRUE∧(_^*)
ens: TRUE∧ ((A . B)^*)
*/
{
    callee ();
    test_loop1();
}

