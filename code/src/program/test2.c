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


void process() 
/*
req: TRUE∧(_^*)
ens: (f0>0∧f0<=20∧f1>30)∧(((A . B)#f0) . ((A . B)#f1))
ens: (f0>0∧f0<=20∧f1>30)∧(((_ . B)#f0) . ((A . B)#f1))
ens: (f0>0∧f0<=20∧f1>30)∧(((~B . B)#f0) . ((A . B)#f1))
ens: (f0>0∧f0<=20∧f1>30)∧(((A . _)#f0) . ((~C . B)#f1))
ens: (f0>0∧f0<=20∧f1>30)∧(((_ . _)#f0) . ((A . _)#f1))

ens: (t <20)∧ ((A.B) # t)
ens: (t <21)∧ ((~A.B) # t)
ens: ((t1+t2) <21)∧ (~A#t1). (B # t2)
ens: ((t1+t2) <21)∧ (A#t1). (~B # t2)
ens: (t <21)∧ ((A.~B) # t)
*/
{
    deadline (callee ()  , 
        20);
    timeout  (callee () , 
        30);
}
