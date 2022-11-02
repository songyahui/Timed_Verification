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
req: n≥0 ∧(_^*)
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

// Should Fail while calling makeCoffee
int coffeeMachine ()
/*
    req: TRUE ∧ ε
    ens: (t≤9)∧ ((((~Done)^*))#t).Done 
    */
{
    // event["Cup"];
    makeCoffee (3);
    event["Done"];

}