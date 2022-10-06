#include "primitives.c"

// Should Succeed 
void test_timeout2() 
/*
req: TRUE∧(_^*)
ens: (f0≥0∧f0<1 ∧ (A#f0)) ∨ (f1≥0∧f1=1 ∧ (ε#f1) . B)
*/
{
    timeout (event["A"] , event["B"], 1);
}
