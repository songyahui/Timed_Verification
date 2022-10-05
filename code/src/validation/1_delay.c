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
