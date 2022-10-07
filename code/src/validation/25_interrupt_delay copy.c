#include "primitives.c"

// Should Succeed 
void test_delay1() 
/*
req: TRUE∧(_^*)
ens: (t=2)∧ Cup.(ε # t).Done
*/
{
    event["Cup"];
    delay (2);
    event["Done"];
}



// Should Succeed 
void test_interrupt4() 
/*
req: TRUE∧(_^*)
ens: (t=2∧f1≥0∧f1<1 ∧ (ε#f1) . Done) ∨ ((t=2∧f2≥0∧f2<1 ∧ (Cup#f2) . Done) ∨ (t=2∧f3≥0∧f3<1 ∧ (Cup . (ε#t)#f3) . Done))
*/
{
    interrupt (test_delay1 ()  , event["Done"], 1);
}
