#include "primitives.c"

// Should Succeed 
void test_delay3() 
/*
req: TRUE∧(_^*)
ens: (t=2)∧(t1=3)∧ Cup.(ε # t).(ε # t1).Done
*/
{
    event["Cup"];
    delay (2);
    delay (3);
    event["Done"];

}