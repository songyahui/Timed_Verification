#include "primitives.c"

// Should Succeed 
void test_delay_deadline1(int n, int m) 
/*
req: TRUE∧(_^*)
ens: (t1=3) ∧(t≤2)∧ (ε # t1).(Cup # t).Done
*/
{
    delay (3);
    deadline (event["Cup"] ,2);
    event["Done"];

}


// Should Succeed 
void test_interrupt6() 
/*
req: TRUE∧(_^*)
ens: (t1=3∧t≤2∧f2≥0∧f2<7 ∧ (ε#f2) . Done) ∨ 
((t1=3∧t≤2∧f3≥0∧f3<7 ∧ ((ε#t1)#f3) . Done) ∨ 
((t1=3∧t≤2∧f4≥0∧f4<7 ∧ ((ε#t1) . (Cup#t)#f4) . Done) ∨ 
((t1=3∧t≤2∧f3≥0∧f3<7 ∧ ((ε#t1)#f3) . Done) ∨ 
((t1=3∧t≤2∧f5≥0∧f5<7 ∧ ((ε#t1)#f5) . Done) ∨ 
(t1=3∧t≤2∧f5≥0∧f5<7 ∧ ((ε#t1)#f5) . Done)))))
*/
{
    interrupt (test_delay_deadline1 (5, 9)  , event["Done"], 7);
}
