#include "primitives.c"

void oneSugar() 
/*
req: TRUE∧(_^*).ε
ens: (t>1)∧ (ε # t)
*/
{
    timeout (() , 1);
}

void addSugar (int n) 
/*
req: TRUE∧(_^*)
ens:  (t≥n)∧ (Sugar #t)
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

void makeCoffee (int n)
/*
req: TRUE∧(_^*) . Cup
ens: (t≤5∧t≥n∧t1≤3)∧(Sugar#t).(Coffee#t1)
*/
{
    deadline (addSugar(n), 5);
    deadline (event["Coffee"], 3);
}

int main ()
/*
    req: TRUE ∧ ε
    ens: (t≤8)∧ ((((!Done)^*))#t).Done 
    */
{
    event["Cup"];
    makeCoffee (3);
    event["Done"];

}