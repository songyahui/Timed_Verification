#include "primitives.c"

// Should Succeed 
void callee () 
/*
req: TRUE∧(_^*)
ens: TRUE∧(A . B)
*/
{
    event["A"];
    event["B"];
}

// Should Succeed 
void test_deadline_delay(int n) 
/*
req: TRUE∧(_^*)
ens: (t≤n)∧(t1>3)∧ ((A.B) # t) .Gap. (ε # t1)
*/
{
    deadline (callee ()  ,n);
    event["Gap"]; 
    delay (5)
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
void if_else_test1 () 
/*
req: TRUE∧(_^*)
ens:(x=1 ∧ A . B) ∨ (((~(x=1))∧x=2∧t≤9∧t1>3 ∧ (A . B#t) . Gap . (ε#t1)) ∨ ((~(x=1))∧(~(x=2))∧t≤100 ∧ (Cup#t) . Done))
*/
{
    if (x==1) {
        callee () }
    else {
        if (x==2) {test_deadline_delay (9)}
        else {
            test_deadline4(100);
            }
        }

}
