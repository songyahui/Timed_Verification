#include "primitives.c"

void callee () 
/*
req: TRUE/\(_^*)
ens: TRUE/\(A . B)
ens: TRUE/\(A )
*/
{
    event["A"];
    event["B"];
}

void callee1 () 
/*
req: TRUE/\(_^*)
ens: TRUE/\(C . D)
ens: TRUE/\(A )
*/
{
    event["C"];
    event["D"];
}

void callee2 () 
/*
req: TRUE/\(_^*)
ens: TRUE/\(C . D)
ens: TRUE/\(A )
*/
{
    event["C"];
    event["D"];
}


void callee3 () 
/*
req: TRUE/\(_^*)
ens: TRUE/\(C . D)
ens: TRUE/\(A )
*/
{
    event["C"];
    event["D"];
}


void callee4 () 
/*
req: TRUE/\(_^*)
ens: TRUE/\(C . D)
ens: TRUE/\(A )
*/
{
    event["C"];
    event["D"];
}

void process() 
/*
req: TRUE/\(_^*)
ens: (f0>0/\f0<=20/\x=1)/\(((A . B)#f0) . (C . (D . (C . (D . (C . D)))))) \/ (f0>0/\f0<=20/\(~(x=1))/\y=1)/\(((A . B)#f0) . (C . (D . (C . (D . (C . (D . (C . D)))))))) \/ (f0>0/\f0<=20/\(~(x=1))/\(~(y=1)))/\(((A . B)#f0) . (C . (D . (C . (D . (C . (D . (C . D))))))))
ens: (f0>0/\f0<=20/\x=1)/\(((A . B)#f0) . (C . (D . (C . (D . (C . D)))))) \/ (f0>0/\f0<=20/\(~(x=1))/\y=1)/\(((A . B)#f0) . (C . (D . (C . (D . (C . (D . (C . D)))))))) \/ (f0>0/\f0<=20/\(~(x=1))/\(~(y=1)))/\(((A . B)#f0) . (C . (D . (C . (D . (C . (D . (C . D))))))))
ens: (f0>0/\f0<=20/\x=1)/\(((A . B)#f0) . (C . (D . (C . (D . (C . D)))))) \/ (f0>0/\f0<=20/\(~(x=1))/\y=1)/\(((A . B)#f0) . (C . (D . (C . (D . (C . (D . (C . D)))))))) \/ (f0>0/\f0<=20/\(~(x=1))/\(~(y=1)))/\(((A . B)#f0) . (C . (D . (C . (D . (C . (D . (C . D))))))))
ens: (f0>0/\f0<=20/\x=1)/\(((A . B)#f0) . (C . (D . (C . (D . (C . D)))))) \/ (f0>0/\f0<=20/\(~(x=1))/\y=1)/\(((A . B)#f0) . (C . (D . (C . (D . (C . (D . (C . D)))))))) \/ (f0>0/\f0<=20/\(~(x=1))/\(~(y=1)))/\(((A . B)#f0) . (C . (D . (C . (D . (C . (D . (C . D))))))))
ens: (f0>0/\f0<=20/\x=1)/\(((A . B)#f0) . (C . (D . (C . (D . (C . D)))))) \/ (f0>0/\f0<=20/\(~(x=1))/\y=1)/\(((A . B)#f0) . (C . (D . (C . (D . (C . (D . (C . D)))))))) \/ (f0>0/\f0<=20/\(~(x=1))/\(~(y=1)))/\(((A . B)#f0) . (C . (D . (C . (D . (C . (D . (C . D))))))))
ens: (f0>0/\f0<=20/\x=1)/\(((A . B)#f0) . (C . (D . (C . (D . (C . D)))))) \/ (f0>0/\f0<=20/\(~(x=1))/\y=1)/\(((A . B)#f0) . (C . (D . (C . (D . (C . (D . (C . D)))))))) \/ (f0>0/\f0<=20/\(~(x=1))/\(~(y=1)))/\(((A . B)#f0) . (C . (D . (C . (D . (C . (D . (C . D))))))))
ens: (f0>0/\f0<=20/\x=1)/\(((A . B)#f0) . (C . (D . (C . (D . (C . D)))))) \/ (f0>0/\f0<=20/\(~(x=1))/\y=1)/\(((A . B)#f0) . (C . (D . (C . (D . (C . (D . (C . D)))))))) \/ (f0>0/\f0<=20/\(~(x=1))/\(~(y=1)))/\(((A . B)#f0) . (C . (D . (C . (D . (C . (D . (C . D))))))))

ens: (t <20)/\ ((A.B) # t)
ens: (t <21)/\ ((~A.B) # t)
ens: ((t1+t2) <21)/\ (~A#t1). (B # t2)
ens: ((t1+t2) <21)/\ (A#t1). (~B # t2)
ens: (t <21)/\ ((A.~B) # t)
ens:  ((x=1))/\(C . (D . (C . (D . (C . (D . (C . D)))))))
ens: (x=1)/\(C . (D . (C . (D . (C . (D . (C . D))))))) 
*/
{

    deadline (callee ()  , 20);

   if (x==1) {
    callee2 ();

    callee3 ();
    callee4 ();
   }
   else {
        if (y==1) {
        callee1 ();
    callee2 ();

    callee3 ();
    callee4 ();
   }
   else {
       callee1 ();
    callee2 ();

    callee3 ();
    callee4 ();
   }
   }


    
}
