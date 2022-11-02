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

// Should Succeed 
void test_delay_deadline1(int n, int m) 
/*
req: TRUE∧(_^*)
ens: (t1=3) ∧(t≤2)∧ (ε # t1).(Cup # t).Done
*/
{
    delay (3);
    deadline (event["Cup"] ,2);
    event["Done"];

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


// Should Succeed 
void stress() 
/*
req: TRUE∧(_^*)
ens: (t1=3∧t≤2∧f2≥0∧f2<7∧x=1 ∧ ((ε)#f2) . Done . A . B . C . D . ((A . B . C . D) || (X . Y . Z . W))) ∨ 
((t1=f3∧t1=3∧t≤2∧f3≥0∧f3<7∧x=1 ∧ ((ε)#t1) . Done . A . B . C . D . ((A . B . C . D) || (X . Y . Z . W))) ∨ 
((t1=3∧t≤2∧f4≥0∧f4<7∧x=1 ∧ ((((ε)#t1) . ((Cup)#t))#f4) . Done . A . B . C . D . ((A . B . C . D) || (X . Y . Z . W))) ∨ 
((t1=3∧t≤2∧f2≥0∧f2<7∧(~(x=1))∧x=2 ∧ ((ε)#f2) . Done . X . Y . Z . W . ((A . B . C . D) || (X . Y . Z . W))) ∨ 
((t1=f3∧t1=3∧t≤2∧f3≥0∧f3<7∧(~(x=1))∧x=2 ∧ ((ε)#t1) . Done . X . Y . Z . W . ((A . B . C . D) || (X . Y . Z . W))) ∨ 
((t1=3∧t≤2∧f4≥0∧f4<7∧(~(x=1))∧x=2 ∧ ((((ε)#t1) . ((Cup)#t))#f4) . Done . X . Y . Z . W . ((A . B . C . D) || (X . Y . Z . W))) ∨ 
((t1=3∧t≤2∧f2≥0∧f2<7∧(~(x=1))∧(~(x=2)) ∧ ((ε)#f2) . Done . A . B . C . D . A . B . C . D . ((A . B . C . D) || (X . Y . Z . W))) ∨ 
((t1=f3∧t1=3∧t≤2∧f3≥0∧f3<7∧(~(x=1))∧(~(x=2)) ∧ ((ε)#t1) . Done . A . B . C . D . A . B . C . D . ((A . B . C . D) || (X . Y . Z . W))) ∨ 
(t1=3∧t≤2∧f4≥0∧f4<7∧(~(x=1))∧(~(x=2)) ∧ ((((ε)#t1) . ((Cup)#t))#f4) . Done . A . B . C . D . A . B . C . D . ((A . B . C . D) || (X . Y . Z . W))))))))))
*/
{
    interrupt (
        test_delay_deadline1 (5, 9)  , 
        event["Done"], 
        7);
    if_else_test1();
    par_test1 () 
}
