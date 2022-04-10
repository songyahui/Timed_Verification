x := -1; 
ct := 0;

void process (int i)
/* req: TRUE /\ (_^*) 
   ens: TRUE /\ (_^*) */
{
  [x=-1] 
  deadline (event["Update"(i)]{x := i}, d1);
  delay (d2);

}

void main () 
/* req: TRUE /\ emp 
   ens: TRUE /\ (_^*)  */
{ process(0) || process(1); }

