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
void callee2 () 
/*
req: TRUE∧(_^*)
ens: TRUE∧(X . Y .Z .W)
*/
{
    event["X"];
    event["Y"];
    event["Z"];
    event["W"];
}

// Should Succeed 
void par_mix3 () 
/*
req: TRUE∧(_^*)
ens: t=2 ∧ ((Cup . (ε#t) . Done) ||( X . Y . Z . W))
*/
{
    test_delay1 () || callee2()

}
