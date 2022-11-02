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

void process() 
/*
req: TRUE∧(_^*)
ens: f0≥0∧f0≤20∧f1≥0∧f1≤30 ∧ ((A . B)#f0) . ((C . D)#f1)
ens: f0≥0∧f0≤20∧f1≥0∧f1≤30 ∧ ((_ . B)#f0) . ((C . D)#f1)
ens: f0≥0∧f0≤20∧f1≥0∧f1≤30 ∧ ((A . ~A)#f0) . ((C . D)#f1)
ens: f0≥0∧f0≤20∧f1≥0∧f1≤30 ∧ ((A . B)#f0) . ((_ . D)#f1)
ens: f0≥0∧f0≤20∧f1≥0∧f1≤30 ∧ ((A . B)#f0) . ((C . ~A)#f1)

ens: (t <20)∧ ((A.B) # t)
ens: (t <21)∧ ((~A.B) # t)
ens: ((t1+t2) <21)∧ (~A#t1). (B # t2)
ens: ((t1+t2) <21)∧ (A#t1). (~B # t2)
ens: (t <21)∧ ((A.~B) # t)
*/
{
    deadline (callee ()  , 20);
    deadline (callee1 () , 30);
}
