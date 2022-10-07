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
ens: (f0>0∧f0≤20∧f1>30)∧(((A . B)#f0) . ((A . B)#f1))

*/
{
    deadline (callee ()  , 
        20);
    timeout  ((), callee () , 
        30);
}
