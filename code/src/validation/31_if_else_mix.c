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
void if_else_test1 () 
/*
req: TRUE∧(_^*)
ens: (x=1 ∧ A . B . C . D) ∨ 
(((~(x=1))∧x=2 ∧ X . Y . Z . W) ∨ 
((~(x=1))∧(~(x=2)) ∧ A . B . C . D . A . B . C . D))
*/
{
    if (x==1) {
        callee () }
    else {
        if (x==2) {callee2 ()}
        else {
            callee (); 
            callee ()}
        }

}
