#include "primitives.c"


void callee () 
/*
req: TRUE∧(_^*)
ens: TRUE∧(A . B .C .D)
*/
{
    event["A"];
    event["B"];
    event["C"];
    event["D"];
}

// Should Succeed 
void test_timeout1() 
/*
req: TRUE∧(_^*)
ens: (f0≥0∧f0<1 ∧ (A#f0) . B .C .D) ∨ (f1≥0∧f1=1 ∧ (ε#f1) . Done)
*/
{
    timeout (callee ()  , event["Done"], 1);
}
