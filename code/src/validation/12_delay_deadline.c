#include "primitives.c"

// Should Succeed 
void test_delay_deadline1(int n, int m) 
/*
req: TRUE∧(_^*)
ens: (t1=m) ∧(t≤n)∧ (ε # t1).(Cup # t).Done
*/
{
    delay (m);
    deadline (event["Cup"] ,n);
    event["Done"];

}