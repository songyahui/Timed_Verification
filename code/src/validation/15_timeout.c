#include "primitives.c"

// Should Succeed 
void test_timeout1() 
/*
req: TRUE∧(_^*)
ens: (f0≥0∧f0<1 ∧ (A#f0)) ∨ (f1≥0∧f1=1 ∧ (ε#f1) . B)
*/
{
    timeout (() , event["B"], 1);
}
