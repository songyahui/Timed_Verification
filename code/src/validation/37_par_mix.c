#include "primitives.c"

// Should Succeed 
void callee () 
/*
req: TRUE∧(_^*)
ens: (x=0 ∧ A . B) ∨ ((~(x=0)) ∧ C . D)
*/
{
    if (x==0) {
        event["A"];
        event["B"];}
    else {
        event["C"];
        event["D"];
    }
}

// Should Succeed 
void callee2 () 
/*
req: TRUE∧(_^*)
ens: (x=0 ∧ X . Y) ∨ ((~(x=0)) ∧ Z . W)
*/
{
    if (x==0) {

        event["X"];
        event["Y"];
    }
    else{
        event["Z"];
        event["W"];
    }
}

// Should Succeed 
void par_mix2 () 
/*
req: TRUE∧(_^*)
ens: (x=0∧x=0 ∧ ((A . B) || (X . Y))) ∨ 
((x=0∧(~(x=0)) ∧ ((A . B) || (Z . W))) ∨ 
(((~(x=0))∧x=0 ∧ ((C . D) || (X . Y))) ∨ 
((~(x=0))∧(~(x=0)) ∧ ((C . D) || (Z . W)))))
*/
{
    callee () || callee2()

}
