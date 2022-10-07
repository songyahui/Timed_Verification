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
void callee3 () 
/*
req: TRUE∧(_^*)
ens: (x=1 ∧ A . B . C . D) ∨ ((~(x=1)) ∧ X . Y . Z . W)
*/
{
    if (x==1) {callee () }
    else {callee2 () }
}


// Should Succeed 
void test_interrupt4() 
/*
req: TRUE∧(_^*)
ens: (x=1∧f0≥0∧f0<1 ∧ (ε#f0) . Done) ∨ 
((x=1∧f1≥0∧f1<1 ∧ (A#f1) . Done) ∨ 
((x=1∧f2≥0∧f2<1 ∧ (A . B#f2) . Done) ∨ 
((x=1∧f3≥0∧f3<1 ∧ (A . B . C#f3) . Done) ∨ 
(((~(x=1))∧f4≥0∧f4<1 ∧ (ε#f4) . Done) ∨ 
(((~(x=1))∧f5≥0∧f5<1 ∧ (X#f5) . Done) ∨ 
(((~(x=1))∧f6≥0∧f6<1 ∧ (X . Y#f6) . Done) ∨ 
((~(x=1))∧f7≥0∧f7<1 ∧ (X . Y . Z#f7) . Done)))))))
*/
{
    interrupt (callee3 ()  , event["Done"], 1);
}
