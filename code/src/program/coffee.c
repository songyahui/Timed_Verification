#include "primitives.c"

void oneSugar() 
    /*
    req: TRUE/\(_^*).emp
    ens: TRUE/\emp
    */
{
    1
}

void addSugar (int n) 
    /*
    req: TRUE/\(_^*)
    ens:  (t>=n)/\ (Sugar #t)
    */
{

    if (n == 0) { 
        event ["Sugar"];
    }
    else {
        timeout (oneSugar() , 1);
        addSugar (n - 1);
    }
} 

void makeCoffee (int n)
    /*
    req: TRUE/\emp
    ens: (t<=5/\t>=n/\t1<=3)/\Cup.(Sugar#t).(Coffee#t1).Done
    */
{
    event["Cup"];
    deadline (addSugar(n), 5);
    deadline (event["Coffee"], 3);
    event["Done"];
}


int main ()
/*
    req: TRUE /\emp
    ens: (t<8)/\ (((_^*).Done)#t)
    */
{
    makeCoffee (3);
}