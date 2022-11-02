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
