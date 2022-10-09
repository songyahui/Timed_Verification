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
void test_interrupt1() 
/*
req: TRUE∧(_^*)
ens: (f0≥0∧f0<1 ∧ (ε#f0) . Done) ∨

 (f1≥0∧f1<1 ∧ (A#f1) . Done)
*/
{
    interrupt (callee ()  , event["Done"], 1);
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
ens: (t1=3∧t≤2∧f9≥0∧f9<7∧x=1∧f0≥0∧f0<1∧t≤1000∧t1>3 ∧ ((ε)#f9) . Done . A . B . C . D . ((ε)#f0) . Done . ((A . B)#t) . Gap . ((ε)#t1)) ∨
 ((t1=f10∧t1=3∧t≤2∧f10≥0∧f10<7∧x=1∧f0≥0∧f0<1∧t≤1000∧t1>3 ∧ ((ε)#t1) . Done . A . B . C . D . ((ε)#f0) . Done . ((A . B)#t) . Gap . ((ε)#t1)) ∨
 ((t1=3∧t≤2∧f11≥0∧f11<7∧x=1∧f0≥0∧f0<1∧t≤1000∧t1>3 ∧ ((((ε)#t1) . ((Cup)#t))#f11) . Done . A . B . C . D . ((ε)#f0) . Done . ((A . B)#t) . Gap . ((ε)#t1)) ∨
 ((t1=3∧t≤2∧f9≥0∧f9<7∧(~(x=1))∧x=2∧f0≥0∧f0<1∧t≤1000∧t1>3 ∧ ((ε)#f9) . Done . X . Y . Z . W . ((ε)#f0) . Done . ((A . B)#t) . Gap . ((ε)#t1)) ∨
 ((t1=f10∧t1=3∧t≤2∧f10≥0∧f10<7∧(~(x=1))∧x=2∧f0≥0∧f0<1∧t≤1000∧t1>3 ∧ ((ε)#t1) . Done . X . Y . Z . W . ((ε)#f0) . Done . ((A . B)#t) . Gap . ((ε)#t1)) ∨
 ((t1=3∧t≤2∧f11≥0∧f11<7∧(~(x=1))∧x=2∧f0≥0∧f0<1∧t≤1000∧t1>3 ∧ ((((ε)#t1) . ((Cup)#t))#f11) . Done . X . Y . Z . W . ((ε)#f0) . Done . ((A . B)#t) . Gap . ((ε)#t1)) ∨
 ((t1=3∧t≤2∧f9≥0∧f9<7∧(~(x=1))∧(~(x=2))∧f0≥0∧f0<1∧t≤1000∧t1>3 ∧ ((ε)#f9) . Done . A . B . C . D . A . B . C . D . ((ε)#f0) . Done . ((A . B)#t) . Gap . ((ε)#t1)) ∨
 ((t1=f10∧t1=3∧t≤2∧f10≥0∧f10<7∧(~(x=1))∧(~(x=2))∧f0≥0∧f0<1∧t≤1000∧t1>3 ∧ ((ε)#t1) . Done . A . B . C . D . A . B . C . D . ((ε)#f0) . Done . ((A . B)#t) . Gap . ((ε)#t1)) ∨
 ((t1=3∧t≤2∧f11≥0∧f11<7∧(~(x=1))∧(~(x=2))∧f0≥0∧f0<1∧t≤1000∧t1>3 ∧ ((((ε)#t1) . ((Cup)#t))#f11) . Done . A . B . C . D . A . B . C . D . ((ε)#f0) . Done . ((A . B)#t) . Gap . ((ε)#t1)) ∨
 ((t1=3∧t≤2∧f9≥0∧f9<7∧x=1∧f1≥0∧f1<1∧t≤1000∧t1>3 ∧ ((ε)#f9) . Done . A . B . C . D . ((A)#f1) . Done . ((A . B)#t) . Gap . ((ε)#t1)) ∨
 ((t1=f10∧t1=3∧t≤2∧f10≥0∧f10<7∧x=1∧f1≥0∧f1<1∧t≤1000∧t1>3 ∧ ((ε)#t1) . Done . A . B . C . D . ((A)#f1) . Done . ((A . B)#t) . Gap . ((ε)#t1)) ∨
 ((t1=3∧t≤2∧f11≥0∧f11<7∧x=1∧f1≥0∧f1<1∧t≤1000∧t1>3 ∧ ((((ε)#t1) . ((Cup)#t))#f11) . Done . A . B . C . D . ((A)#f1) . Done . ((A . B)#t) . Gap . ((ε)#t1)) ∨
 ((t1=3∧t≤2∧f9≥0∧f9<7∧(~(x=1))∧x=2∧f1≥0∧f1<1∧t≤1000∧t1>3 ∧ ((ε)#f9) . Done . X . Y . Z . W . ((A)#f1) . Done . ((A . B)#t) . Gap . ((ε)#t1)) ∨
 ((t1=f10∧t1=3∧t≤2∧f10≥0∧f10<7∧(~(x=1))∧x=2∧f1≥0∧f1<1∧t≤1000∧t1>3 ∧ ((ε)#t1) . Done . X . Y . Z . W . ((A)#f1) . Done . ((A . B)#t) . Gap . ((ε)#t1)) ∨
 ((t1=3∧t≤2∧f11≥0∧f11<7∧(~(x=1))∧x=2∧f1≥0∧f1<1∧t≤1000∧t1>3 ∧ ((((ε)#t1) . ((Cup)#t))#f11) . Done . X . Y . Z . W . ((A)#f1) . Done . ((A . B)#t) . Gap . ((ε)#t1)) ∨
 ((t1=3∧t≤2∧f9≥0∧f9<7∧(~(x=1))∧(~(x=2))∧f1≥0∧f1<1∧t≤1000∧t1>3 ∧ ((ε)#f9) . Done . A . B . C . D . A . B . C . D . ((A)#f1) . Done . ((A . B)#t) . Gap . ((ε)#t1)) ∨
 ((t1=f10∧t1=3∧t≤2∧f10≥0∧f10<7∧(~(x=1))∧(~(x=2))∧f1≥0∧f1<1∧t≤1000∧t1>3 ∧ ((ε)#t1) . Done . A . B . C . D . A . B . C . D . ((A)#f1) . Done . ((A . B)#t) . Gap . ((ε)#t1)) ∨
 (t1=3∧t≤2∧f11≥0∧f11<7∧(~(x=1))∧(~(x=2))∧f1≥0∧f1<1∧t≤1000∧t1>3 ∧ ((((ε)#t1) . ((Cup)#t))#f11) . Done . A . B . C . D . A . B . C . D . ((A)#f1) . Done . ((A . B)#t) . Gap . ((ε)#t1))))))))))))))))))
*/
{
    interrupt (
        test_delay_deadline1 (5, 9)  , 
        event["Done"], 
        7);
    if_else_test1();
    test_interrupt1();
    test_deadline_delay(1000)
   
}


//[Inferring Time] 2375.345 ms
//[Succeed  Cases] 1 case(s) with avg time 10746.597 ms
//[Failure  Cases] 0 case(s) with avg time nan ms


//Time for inference    :2377.929
//[AskZ3 Count] 3531