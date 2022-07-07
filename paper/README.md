# Timed_Verification

1. expressiveness =\= timed automata: timed modelchecker. 
2. build the primitive language. 
3. application: motivation exampale.  


void addSugar(int n)
// requires n>0 ∧ Cup 
// ensures  t>=n ∧ Sugar # t
{
    if n == 0 then event[Sugar] 
    else {
        timeout (oneSugar(), 1);
        addSugar (n-1);
    }
}

void makeCoffee (int n)
// requires n>0 ∧ ε 
// ensures  5>t>=n∧ t1<3 ∧ Cup.(Sugar # t).(Coffee # t1).Done
{
    event[Cup];
    deadline (getSugar(n), 5);
    deadline (event[Coffee], 3);
    event[Done];
}

void main () 
// requires true ∧ ε 
// ensures  t < 8 ∧ (_^*.Done) # t
{
    makeCoffee(3);
}



send (d:int[0, 5000]) = 
    ....


t<3 ∧ (A) [0-3] |- t<4 ∧ (A) #t

t<1 ∧ t <2 ∧ t<3 ∧ (A#t) |- t<3 ∧ (A) #t

t<5000  <== d \in [0, 5000] ∧ (t < d)

A -> B <-> (not A ∨ B)

x < 1 |- x < 3

x<1 ∨ x<4 |- x < 3

1. language: 
abort d p -> t<d ∧ A#t
timeout d p -> t>d ∧ A#t
p1;p2    A.B
if b then p1 else p2  A∨B
loop p  ....

2. comparison with TA
case studies;
formal proof: TRS;


forward_verifier (program -> timed effect) 

trs (t1, t2 : timed_effect) : bool 
t1 |- t2 





Fischer's mutual exclusion algorithm. 
d1<d2

Update(0){x:=0}#d1. ε#d2. ([x=0]Critical(0) .Exit(0){x:=-1} ∨ [x!=0]ε)
||
Update(1){x:=1}#d1. ε#d2. ([x=1]Critical(1) .Exit(1){x:=-1} ∨ [x!=1]ε)

--->

Update(0){x:=0}#d1. Update(1){x:=1}#d1. ε#(d2-d1). ε#d2. [x!=0]ε

otherwise if d1 > d2 

Update(0){x:=0}#d1. [x=0]Critical(0). Update(1){x:=1}#d1.  ε#d2. [x=1]Critical(1)




