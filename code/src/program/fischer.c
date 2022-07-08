
void process (int i, int d1, int d2)
/* req: (d1>0∧d2>d1∧0≤t) ∧ ((_#t)^*)
   ens: (t1≤d1∧t2=d2) ∧ (([x=-1]? . (Update(i){x := i}#t1) . (ε#t2) . (([x=i] . Critical(i){ct := (ct + 1); pc:=i} . Exit(i){ct := (ct-1); x := -1; pc:= -1} ) + [(!(x=i))])) ^*) */
{
  delay (d2);
  process (i, d1, d2);

}
