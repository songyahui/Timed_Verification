#include "primitives.c"

// Should Succeed 
void test_deadline1() 
/*
req: TRUE∧(_^*)
ens: (t≤5)∧ (Cup # t).Done
*/
{
    deadline (event["Cup"] ,5);
    event["Done"];

}