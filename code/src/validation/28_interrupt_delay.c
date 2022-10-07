#include "primitives.c"

// Should Succeed 
void test_delay5(int n) 
/*
req: TRUE∧(_^*)
ens: (t=n)∧ Cup.(ε # t).Done
*/
{
    event["Cup"];
    delay (n);
    event["Done"];

}


// Should Succeed 
void test_interrupt7() 
/*
req: TRUE∧(_^*)
ens: (t=10∧f1≥0∧f1<100 ∧ (ε#f1) . Done) ∨ ((t=10∧f2≥0∧f2<100 ∧ (Cup#f2) . Done) ∨ (t=10∧f3≥0∧f3<100 ∧ (Cup . (ε#t)#f3) . Done))
*/
{
    interrupt (test_delay5 (10)  , event["Done"], 100);
}
