#include "primitives.c"

// Should Succeed 
void callee () 
/*
req: TRUE∧(_^*)
ens: TRUE∧(A . B .C .D)
*/
{
    event["A"];
    event["B"];
    event["C"];
    event["D"];
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
void par_test1 () 
/*
req: TRUE∧(_^*)
ens: TRUE ∧ ((A . B . C . D) || (X . Y . Z . W))
*/
{
    callee () || callee2()

}
