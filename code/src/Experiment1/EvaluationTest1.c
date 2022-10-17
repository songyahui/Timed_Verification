#include "primitives.c"

// Should Succeed 
void process(int n, int m) 
/*
req: TRUE∧(_^*)
ens: (t1=3) ∧(t≤2)∧(t2=0)∧ (ε # t1).(Cup # t).(Done# t2)
*/
{

    delay (3);
    deadline (
        event["Cup"] ,2);
    event["Done"];
}
// Should Succeed 
void fun(int n) 
/*
req: (0≤n)∧(_^*)
ens: (t1=-1) ∧ (ε # t1). Cup 
*/
{
    delay (-2);
    event["Cup"];
}

// Should Succeed 
void process2(int n, int m) 
/*
req: TRUE∧(_^*)
ens: (t1=3) ∧(t≤2)∧(t2=0)∧ (ε # t1).(Cup # t).(Done# t2)
*/
{

    deadline (
        fun(5)  ,2);
    event["Done"];
}

// Should Succeed 
void delay2(int n) 
/*
req: (0≤n)∧(_^*)
ens: (t1=n) ∧ (ε # t1)
*/
{

    delay (n);
   
}

// Should Succeed 
void ddl2(int n) 
/*
req: (0≤n)∧(_^*)
ens: (t1≤n) ∧ (Cup # t1)
*/
{

    deadline (event["Cup"], (n+1));
   
}

