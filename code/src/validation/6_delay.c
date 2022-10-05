#include "primitives.c"

// Should Fail 
void test_delay6(int n) 
/*
req: TRUE∧(_^*)
ens: (t>n)∧ Cup.(ε # t).Done
*/
{
    event["Cup"];
    delay (n);
    event["Done"];

}