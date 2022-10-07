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

// Should Fail 
void test_loop4() 
/*
req: TRUE∧(_^*)
ens: (f0≥0∧f0<1∧t≤5 ∧ (ε#f0) . Done . ((Cup#t) . Done^*)) 
    ∨ (f1≥0∧f1<1∧t≤5 ∧ (A#f1) . Done . ((Cup#t) . Done^*))
*/
{
    test_interrupt1();
    test_loop4();
}

