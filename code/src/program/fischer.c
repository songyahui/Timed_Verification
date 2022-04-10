x := -1; 
ct := 0;

void process (int i)
/* req: TRUE /\ (_^*) 
   ens: TRUE /\ (_^*) */
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

