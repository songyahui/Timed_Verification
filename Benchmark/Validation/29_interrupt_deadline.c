#include "primitives.c"

// Should Succeed 
void test_deadline4(int n) 
/*
req: TRUE∧(_^*)
ens: (t≤n)∧ (Cup # t).Done
*/
{
    deadline (event["Cup"] ,n);
    event["Done"];

}


// Should Succeed 
void test_interrupt6() 
/*
req: TRUE∧(_^*)
ens: (t≤5∧f1≥0∧f1<100 ∧ (ε#f1) . Done) ∨ 
((t≤5∧f2≥0∧f2<100 ∧ ((Cup#t)#f2) . Done) ∨ 
((t≤5∧f1≥0∧f1<100 ∧ (ε#f1) . Done) ∨ 
((t≤5∧f3≥0∧f3<100 ∧ (ε#f3) . Done) ∨ 
(t≤5∧f3≥0∧f3<100 ∧ (ε#f3) . Done))))
*/
{
    interrupt (test_deadline4 (5)  , event["Done"], 100);
}
