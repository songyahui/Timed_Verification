#include "primitives.c"

// Should Fail 
void test_deadline5(int n) 
/*
req: TRUE∧(_^*)
ens: (t>n)∧ (Cup # t).Done
*/
{
    deadline (event["Cup"] ,n);
    event["Done"];

}