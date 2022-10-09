#include "primitives.c"

void callee () 
/*
req: TRUE∧(_^*)
ens: TRUE∧(A . B)
ens: TRUE∧(A )
*/
{
    event["A"];
    event["B"];
}

void callee1 () 
/*
req: TRUE∧(_^*)
ens: TRUE∧(C . D)
ens: TRUE∧(A )
*/
{
    event["C"];
    event["D"];
}


void callee3 () 
/*
req: TRUE∧(_^*)
ens: TRUE∧(C . D)
ens: TRUE∧(A )
*/
{
    event["C"];
    event["D"];
}


void callee4 () 
/*
req: TRUE∧(_^*)
ens: TRUE∧(C . D)
ens: TRUE∧(A )
*/
{
    event["C"];
    event["D"];
}

void process() 
/*
req: TRUE∧(_^*)
ens: f0≥0∧f0≤20∧f1=30∧f0≥0∧f0≤20 ∧ ((A . B)#f0) . ((A . B)#f0) . (ε#f1) . C . D . C . D . C . D
ens: f0≥0∧f0≤20∧f1=30∧f0≥0∧f0≤20 ∧ ((_ . B)#f0) . ((A . B)#f0) . (ε#f1) . C . D . C . D . C . D
ens: f0≥0∧f0≤20∧f1=30∧f0≥0∧f0≤20 ∧ ((A . B)#f0) . ((A . B)#f0) . (ε#f1) . ((C . D)^*) 
ens: f0≥0∧f0≤20∧f1=30∧f0≥0∧f0≤20 ∧ ((A . _)#f0) . ((A . B)#f0) . (ε#f1) . C . D . C . D . C . D
ens: f0≥0∧f0≤20∧f1=30∧f0≥0∧f0≤20 ∧ ((A . B)#f0) . ((A . B)#f0) . (ε#f1) . ((C . _)^*) 

ens: (t <20)∧ ((A.B) # t)
ens: (t <21)∧ ((~A.B) # t)
ens: ((t1+t2) <21)∧ (~A#t1). (B # t2)
ens: ((t1+t2) <21)∧ (A#t1). (~B # t2)
ens: (t <21)∧ ((A.~B) # t)
*/
{
    deadline (callee ()  , 
    20);
    timeout ((), callee1 () , 
    30);
    callee3 ();
    callee4 ();
}
