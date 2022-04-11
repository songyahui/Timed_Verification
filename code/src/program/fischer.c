x := -1; 
ct := 0;

void process (int i)
/* req: TRUE /\ (_^*) 
   ens: (t0<=d1/\t1=d2) /\ ([x=-1]? . (Update(i)#t0) . (emp#t1) . (([x=i] . Critical(i) . Exit(i) ) + [(~(x=i))]) ^*) */

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
/* req: TRUE /\ emp 
   ens: TRUE /\ (_^*)  */
{ process(0) || process(1); }

