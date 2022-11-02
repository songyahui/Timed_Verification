#include "primitives.c"


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
void test_interrupt1() 
/*
req: TRUE∧(_^*)
ens: (f0≥0∧f0<1 ∧ (ε#f0) . Done) ∨ (f1≥0∧f1<1 ∧ (A#f1) . Done)
*/
{
    interrupt (callee ()  , event["Done"], 1);
}
