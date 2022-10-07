#include "primitives.c"

void callee () 
/*
req: TRUE∧(_^*)
ens: TRUE∧(A . B)
ens: TRUE∧(A )
*/
{
    event["A"];
    event["B"]
}

void process() 
/*
req: TRUE∧(_^*)
ens: (t <21)∧ ((A.B) # t)
ens: (t <21)∧ ((_.B) # t)
ens: (t <21)∧ ((_._) # t)
ens: (t <21)∧ ((A._) # t)
ens: ((t1+t2) <21)∧ (A#t1). (B # t2)
ens: (t <20)∧ ((A.B) # t)
ens: (t <21)∧ ((~A.B) # t)
ens: ((t1+t2) <21)∧ (~A#t1). (B # t2)
ens: ((t1+t2) <21)∧ (A#t1). (~B # t2)
ens: (t <21)∧ ((A.~B) # t)
*/
{
    deadline (callee ()  , 20);
}
