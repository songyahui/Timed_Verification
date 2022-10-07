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
ens: (x=0 ∧ X . Y) ∨ ((~(x=0)) ∧ Z . W)
*/
{
    if (x==0) {

        event["X"];
        event["Y"];
    }
    else{
        event["Z"];
        event["W"];
    }
}

// Should Succeed 
void par_mix4 () 
/*
req: TRUE∧(_^*)
ens: (t=2∧x=0 ∧ ((Cup . (ε#t) . Done) || (X . Y))) ∨ (t=2∧(~(x=0)) ∧ ((Cup . (ε#t) . Done) || (Z . W)))
*/
{
    test_delay1 () || callee2()

}
