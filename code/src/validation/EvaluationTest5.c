#include "primitives.c"

void callee () 
/*
req: TRUE∧(_^*)
ens: TRUE∧(A . B)
*/
{
    event["A"];
    event["B"];
}

void callee1 () 
/*
req: TRUE∧(_^*)
ens: TRUE∧(C . D)
*/
{
    event["C"];
    event["D"];
}

void callee2 () 
/*
req: TRUE∧(_^*)
ens: TRUE∧(C . D)
*/
{
    event["C"];
    event["D"];
}


void callee3 () 
/*
req: TRUE∧(_^*)
ens: TRUE∧(C . D)
*/
{
    event["C"];
    event["D"];
}


void callee4 () 
/*
req: TRUE∧(_^*)
ens: TRUE∧(C . D)
*/
{
    event["C"];
    event["D"];
}

void process() 
/*
req: TRUE∧(_^*)
ens: (x=1 ∧ C . D . C . D . C . D . C . D) ∨
 ((~(x=1))∧f0≥0∧f0≤20∧f1=30∧(~(x=1))∧f0≥0∧f0≤20 ∧ ((A . B)#f0) . ((A . B)#f0) . ((ε)#f1) . C . D)
ens: (x=1 ∧ ((C . D)^*)) ∨
 ((~(x=1))∧f0≥0∧f0≤20∧f1=30∧(~(x=1))∧f0≥0∧f0≤20 ∧ ((A . B)#f0) . ((A . B)#f0) . ((ε)#f1) . C . D)
ens: (x=1 ∧ ((C . D)^*)) ∨
 ((~(x=1))∧f0≥0∧f0≤20∧f1=30∧(~(x=1))∧f0≥0∧f0≤20 ∧ ((A . _)#f0) . ((A . B)#f0) . ((ε)#f1) . C . D)
ens: (x=1 ∧ ((C . D)^*)) ∨
 ((~(x=1))∧f0≥0∧f0≤20∧f1=30∧(~(x=1))∧f0≥0∧f0≤20 ∧ ((A . B)#f0) . ((~B . B)#f0) . ((ε)#f1) . C . D)
ens: (x=1 ∧ C . _ . C . D . C . D . C . D) ∨
 ((~(x=1))∧f0≥0∧f0≤20∧f1=30∧(~(x=1))∧f0≥0∧f0≤20 ∧ ((A . B)#f0) . ((A . B)#f0) . ((ε)#f1) . C . D)
ens: (x=1 ∧ C . D . C . D . C . D . C . D) ∨
 ((~(x=1))∧f0≥0∧f0≤20∧f1=30∧(~(x=1))∧f0≥0∧f0≤20 ∧ ((A . B)#f0) . ((A . B)#f0) . ((ε)#f1) . ((_)^*))
ens: (x=1 ∧ ((C . D)^*) . C . D . C . D . C . D) ∨
 ((~(x=1))∧f0≥0∧f0≤20∧f1=30∧(~(x=1))∧f0≥0∧f0≤20 ∧ ((A . B)#f0) . ((A . B)#f0) . ((ε)#f1) . C . D)


ens: (t <20)∧ ((A.B) # t)
ens: (t <21)∧ ((~A.B) # t)
ens: ((t1+t2) <21)∧ (~A#t1). (B # t2)
ens: ((t1+t2) <21)∧ (A#t1). (~B # t2)
ens: (t <21)∧ ((A.~B) # t)
ens:  ((x=1))∧(C . (D . (C . (D . (C . (D . (C . D)))))))
ens: (x=1)∧(C . (D . (C . (D . (C . (D . (C . D))))))) 
*/
{
   if (x==1) {
        callee1 ();
    callee2 ();

    callee3 ();
    callee4 ();
   }
   else {
       deadline (callee ()  , 
    20);
    timeout ((), callee1 () , 
    30);
   }
    
}
