#include "primitives.c"

// Should Fail 
void test_delay2() 
/*
req: TRUE∧(_^*)
ens: (t=2)∧(t1=3)∧ Cup.(ε # t).Done.(ε # t1)
*/
{
    event["Cup"];
    delay (2);
    event["Done"];
    delay (3);

}