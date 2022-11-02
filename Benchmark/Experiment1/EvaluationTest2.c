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


void process() 
/*

req: TRUE∧(_^*)
ens: f0≥0∧f0≤20∧f1=30∧f0≥0∧f0≤20 ∧ (A . B#f0) . (A . B#f0) . (ε#f1) . A . B
ens: f0≥0∧f0≤200∧f1=30∧f0≥0∧f0≤20 ∧ (A . B#f0) . (A . B#f0) . (ε#f1) . A . B
ens: f0≥0∧f0≤20∧f1<40∧f0≥0∧f0≤20 ∧ (A . B#f0) . (A . B#f0) . (ε#f1) . A . B
ens: f0≥0∧f0≤20∧f1=30∧f0≥0∧f0≤200 ∧ (A . B#f0) . (A . B#f0) . (ε#f1) . A . B
ens: f0≤20∧f1<31∧f0≥0∧f0≤20 ∧ (A . B#f0) . (A . B#f0) . (ε#f1) . A . B

ens: (t <20)∧ ((A.B) # t)
ens: (t <21)∧ ((~A.B) # t)
ens: ((t1+t2) <21)∧ (~A#t1). (B # t2)
ens: ((t1+t2) <21)∧ (A#t1). (~B # t2)
ens: (t <21)∧ ((A.~B) # t)

*/
{
    deadline (callee ()  , 
        20);
    timeout  ((), callee () , 
        30);
}
