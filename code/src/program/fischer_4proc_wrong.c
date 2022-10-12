x := -1; 
cs:= 0;

void proc (int i) 
/* req: (e>0∧d>e) ∧ ((_)^*)
   ens:  e>0∧d>e∧f0≥0∧f0≤d∧f1=e ∧ ([x=-1]? ((Update(i){x:=i})#f0) . ((ε)#f1) . ([x=i] . Critical(i){cs:=(cs+1)} . Exit(i){cs:=cs-1;x:=-1} + [(~(x=i))] )  )
*/
{()}

//


void main ()
/* req: (e>0∧d>e) ∧ ε
ens: (d>e) ∧ ([cs≤1]^*)
  */
{
  proc(0) ||
    proc(1) ||
    proc(2)
    ||
    proc(3)

}
