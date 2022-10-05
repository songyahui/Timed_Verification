#include "primitives.c"

// Should Fail 
void test_deadline3() 
/*
req: TRUE∧(_^*)
ens: (t>4)∧ (Cup # t).Done
*/
{
    deadline (event["Cup"] ,5);
    event["Done"];

}