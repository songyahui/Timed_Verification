# Timed_Verification

1. expressiveness =\= timed automata: timed modelchecker. 
2. build the primitive language. 
3. application: motivation exampale.  


void addSugar(int n)
// requires n>0 /\ Cup 
// ensures  t>=n /\ Sugar # t
{
    if n == 0 then event[Sugar] 
    else {
        timeout (oneSugar(), 1);
        addSugar (n-1);
    }
}

void makeCoffee (int n)
// requires n>0 /\ emp 
// ensures  5>t>=n/\ t1<3 /\ Cup.(Sugar # t).(Coffee # t1).Done
{
    event[Cup];
    deadline (getSugar(n), 5);
    deadline (event[Coffee], 3);
    event[Done];
}

void main () 
// requires true /\ emp 
// ensures  t < 8 /\ (_^*.Done) # t
{
    makeCoffee(3);
}



send (d:int[0, 5000]) = 
    ....


t<3 /\ (A) [0-3] |- t<4 /\ (A) #t

t<1 /\ t <2 /\ t<3 /\ (A#t) |- t<3 /\ (A) #t

t<5000  <== d \in [0, 5000] /\ (t < d)

A -> B <-> (not A \/ B)

x < 1 |- x < 3

x<1 \/ x<4 |- x < 3

1. language: 
abort d p -> t<d /\ A#t
timeout d p -> t>d /\ A#t
p1;p2    A.B
if b then p1 else p2  A\/B
loop p  ....

2. comparison with TA
case studies;
formal proof: TRS;


forward_verifier (program -> timed effect) 

trs (t1, t2 : timed_effect) : bool 
t1 |- t2 