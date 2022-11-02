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

// Should Succeed 
void par_mix5 () 
/*
req: TRUE∧(_^*)
ens: t=2∧t≤5 ∧ ((Cup . (ε#t) . Done) || ((Cup#t) . Done))
*/
{
    test_delay1 () || test_deadline1()

}
