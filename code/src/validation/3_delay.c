#include "primitives.c"

// Should Fail 
void test_delay3() 
/*
req: TRUE∧(_^*)
ens: (t<2)∧ Cup.(ε # t).Done
*/
{
    event["Cup"];
    delay (2);
    event["Done"];

}