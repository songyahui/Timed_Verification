#include "primitives.c"

// Should Succeed 
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
void test_deadline_delay(int n) 
/*
req: TRUE∧(_^*)
ens: (t≤n)∧(t1>3)∧ ((A.B) # t) .Gap. (ε # t1)
*/
{
    deadline (callee ()  ,n);
    event["Gap"]; 
    delay (5)
}

// Should Fail 
void test_loop5() 
/*
req: TRUE∧(_^*)
ens: (t≤1∧t1>3∧f0≥0∧f0<1∧t≤5 ∧ (A . B#t) . Gap . (ε#t1) . (ε#f0) . Done . ((Cup#t) . Done^*)) ∨ 
(t≤1∧t1>3∧f1≥0∧f1<1∧t≤5 ∧ (A . B#t) . Gap . (ε#t1) . (A#f1) . Done . ((Cup#t) . Done^*))
*/
{
    test_deadline_delay(1);
    test_loop5();
}

