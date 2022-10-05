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