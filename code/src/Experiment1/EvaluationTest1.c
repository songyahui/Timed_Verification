#include "primitives.c"

// Should Succeed 
void process(int n, int m) 
/*
req: TRUE∧(_^*)

ens: (t1=3) ∧(t≤2)∧ (ε # t1).(Cup # t).Done
ens: (t1=3) ∧(t≤20)∧ (ε # t1).(Cup # t).Done
ens: (t1≥3) ∧(t≤2)∧ (ε # t1).(Cup # t).Done
ens: (t1=3) ∧(t≤2)∧ (ε # t1).(Cup # t).Done
ens: (t1≤30) ∧(t≤2)∧ (ε # t1).(Cup # t).Done

ens: (t1=3) ∧(t≤2)∧ (ε # t1).(Cup # t)
ens: (t1=3) ∧(t≤2)∧ (ε # t1)
ens: (t1>3) ∧(t≤2)∧ (ε # t1)
ens: (t1>3) ∧(t≤1)∧ (ε # t1)
ens: (t1>3) ∧(t≤1)∧ Done 

*/
{
    delay (3);
    deadline (
        event["Cup"] ,2);
    event["Done"];
}