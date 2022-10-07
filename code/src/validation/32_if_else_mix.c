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
void test_deadline4(int n) 
/*
req: TRUE∧(_^*)
ens: (t≤n)∧ (Cup # t).Done
*/
{
    deadline (event["Cup"] ,n);
    event["Done"];

}

// Should Succeed 
void if_else_test2 () 
/*
req: TRUE∧(_^*)
ens:(x=1 ∧ A . B . C . D) ∨ (((~(x=1))∧x=2 ∧ X . Y . Z . W) ∨ ((~(x=1))∧(~(x=2))∧t≤100 ∧ (Cup#t) . Done))
*/
{
    if (x==1) {
        callee () }
    else {
        if (x==2) {callee2 ()}
        else {
            test_deadline4(100);
            }
        }

}
