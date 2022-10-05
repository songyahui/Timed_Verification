#include "primitives.c"

// Should Succeed 
void test_timeout1() 
/*
req: TRUE∧(_^*)
ens: (t≥1)∧ (ε # t)
*/
{
    timeout (() , (), 1);
}
