#include "primitives.c"


// Should Succeed 
void oneSugar() 
/*
req: TRUE∧(_^*)
ens: (t≥1)∧ (ε # t)
*/
{
    timeout ((), () , 1);
}

// Should Succeed 
void addSugar (int n) 
/*
req: TRUE ∧(_^*)
ens: t≥n ∧ (Sugar #t)
*/
{

    if (n == 0) { 
        event ["Sugar"];
    }
    else {
        oneSugar();
        addSugar (n - 1);
    }
} 

// Should Succeed 
void makeCoffee (int n)
/*
req: n≥0 ∧(_^*) . Cup
ens: (t≤5∧t≥n∧t1≤3)∧(Sugar#t).(Coffee#t1)
*/
{
    deadline (addSugar(n), 5);
    deadline (event["Coffee"], 3);
}

// Should Succeed 
int coffeeMachine ()
/*
    req: TRUE∧(_^*)
    ens: (t≤9)∧ ((((~Done)^*))#t).Done 
    */
{
    event["Cup"];
    makeCoffee (3);
    event["Done"];

}

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
ens: (t1=3∧t≤2∧f5≥0∧f5<7∧x=1∧t≤9 ∧ ((ε)#f5) . Done . A . B . C . D . ((A . B . C . D) || (X . Y . Z . W)) . (((~Done^*))#t) . Done) ∨ 
((t1=f6∧t1=3∧t≤2∧f6≥0∧f6<7∧x=1∧t≤9 ∧ ((ε)#t1) . Done . A . B . C . D . ((A . B . C . D) || (X . Y . Z . W)) . (((~Done^*))#t) . Done) ∨ 
((t1=3∧t≤2∧f7≥0∧f7<7∧x=1∧t≤9 ∧ ((((ε)#t1) . ((Cup)#t))#f7) . Done . A . B . C . D . ((A . B . C . D) || (X . Y . Z . W)) . (((~Done^*))#t) . Done) ∨ 
((t1=3∧t≤2∧f5≥0∧f5<7∧(~(x=1))∧x=2∧t≤9 ∧ ((ε)#f5) . Done . X . Y . Z . W . ((A . B . C . D) || (X . Y . Z . W)) . (((~Done^*))#t) . Done) ∨ 
((t1=f6∧t1=3∧t≤2∧f6≥0∧f6<7∧(~(x=1))∧x=2∧t≤9 ∧ ((ε)#t1) . Done . X . Y . Z . W . ((A . B . C . D) || (X . Y . Z . W)) . (((~Done^*))#t) . Done) ∨ 
((t1=3∧t≤2∧f7≥0∧f7<7∧(~(x=1))∧x=2∧t≤9 ∧ ((((ε)#t1) . ((Cup)#t))#f7) . Done . X . Y . Z . W . ((A . B . C . D) || (X . Y . Z . W)) . (((~Done^*))#t) . Done) ∨ 
((t1=3∧t≤2∧f5≥0∧f5<7∧(~(x=1))∧(~(x=2))∧t≤9 ∧ ((ε)#f5) . Done . A . B . C . D . A . B . C . D . ((A . B . C . D) || (X . Y . Z . W)) . (((~Done^*))#t) . Done) ∨ 
((t1=f6∧t1=3∧t≤2∧f6≥0∧f6<7∧(~(x=1))∧(~(x=2))∧t≤9 ∧ ((ε)#t1) . Done . A . B . C . D . A . B . C . D . ((A . B . C . D) || (X . Y . Z . W)) . (((~Done^*))#t) . Done) ∨ 
(t1=3∧t≤2∧f7≥0∧f7<7∧(~(x=1))∧(~(x=2))∧t≤9 ∧ ((((ε)#t1) . ((Cup)#t))#f7) . Done . A . B . C . D . A . B . C . D . ((A . B . C . D) || (X . Y . Z . W)) . (((~Done^*))#t) . Done))))))))
*/
{
    interrupt (
        test_delay_deadline1 (5, 9)  , 
        event["Done"], 
        7);
    if_else_test1();
    par_test1 () ;
    coffeeMachine ()
}


//[Inferring Time] 3704.65 ms
//[Succeed  Cases] 1 case(s) with avg time 215887.264 ms
//[Failure  Cases] 0 case(s) with avg time nan ms


//Time for inference    :3743.914
//[AskZ3 Count] 34885
