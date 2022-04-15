x := -1; 
ct := 0;
pc := -1;

void process (int i)
/* req: (d1>0/\d2>d1) /\ (_^*) 
   ens: (t0<=d1/\t1=d2) /\ (([x=-1]? . (Update(i){x := i}#t0) . (emp#t1) . (([x=i] . Critical(i){ct := (ct + 1); pc:=i} . Exit(i){ct := (ct-1); x := -1; pc:= -1} ) + [(~(x=i))])) ^*) */
{
  [x=-1] 
  deadline (event["Update"(i)]{x := i}, d1);
  delay (d2);
  if (x==i) {
    event["Critical"(i)]{ct := (ct + 1)};
    event["Exit"(i)]{ct := (ct-1); x := -1};
    process (i);
  } else {
    process (i);
  }
}

void main () 
/* req: (d1>0/\d2>d1) /\ emp 
   ens: TRUE /\ (([pc=-1] + [pc=x])^*)  */
{ process(0) || process(1); }

