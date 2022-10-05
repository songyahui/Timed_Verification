#include "primitives.c"

// Should Succeed 
void test_delay6(int n, int m) 
/*
req: TRUE∧(_^*)
ens: (t=n)∧(t1=m)∧ Cup.(ε # t).Done.(ε # t1)
*/
{
    event["Cup"];
    delay (n);
    event["Done"];
    delay (m);


}