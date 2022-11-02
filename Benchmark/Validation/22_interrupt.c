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

// Should Fail 
void test_interrupt2() 
/*
req: TRUE∧(_^*)
ens: (f0≥0∧f0<1 ∧ (ε#f0) . Done) ∨ (f1≥0∧f1<1 ∧ (A#f1) . Done)
*/
{
    interrupt (callee ()  , event["Done"], 1);
}
