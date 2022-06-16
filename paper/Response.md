# OVERVIEW: 

Many thanks to our reviewers for their interest 
and appreciation of certain aspects of our work. 

We acknowledge our weaknesses upon related work and evaluations. 
Thanks again for the time and effort in pointing out our typos 
and giving out constructive suggestions. 

We took all the valuable comments into account and made the 
following change list. 


# CHANGE LIST: 


| | Changes     | Description | Timeline (Working days)    |
| ---  | ----------- | ----------- | ----------- |
|1 | Typos       | Mentioned in the reviews  | Already Done| 
|2 | Related work | [Song & Chin 2020]  | 5 days (Partly done in by responding to our Reviewers) |
|3 | Evaluation data | Have a table detailing summary statistics | 5-10 days |
|4 | Writing polishing | Find a buddy to check the writings | 5 days | 
|  | In total  | | 15 - 20 days

Other minor adjustments below can be done within a couple of days :

- Drop the organization paragraph; 


In total, we plan to finish all the changes within one month.  



# RESPONSE: 

## To Reviewer A

### Q1. Was there any actual comparison with another tool (e.g. PAT)?

### Q2. Where do the models come from? Do the authors plan to make their tool and experiments publicly available? (e.g. as part as an artifact)


### Q3. Does this mean that the time is discrete, or does this mean that the time bounds are integer-valued (while time can still be continuous)?
Time is continuous. The current implementation makes use of SMT in 
integer numbers domain.
It is not hard to adapt it into real numbers given the suitable SMT solver. 

### Q4. I find the event name Sugar slightly misleading: if this denotes the completion of the sugar addition phase, perhaps EndSugar would be more appropriate? 
`Sugar` denotes the completion of the sugar addition phase, we will change it to `EndSugar`. Thanks!

### Q5. "our effects provide more detailed information than traditional timed verification, and in fact, it cannot be fully captured by any prior works " This requires some discussion, and does not seem obvious to me, especially when compared with Uppaal.

Using the example $\Phi_{addNSuggar(n)} = n{<}3 \wedge n{=}t \wedge Sugar\# t $, 
there are two main advantages shown comparing the proposed Effects with timed-automata based modelling:
1. The time-bounds can be depended on the function inputs. The specifications are dynamically instantiated 
during the execution. 
2. the time-bounds can be a range of values (possibly an infinite set). In this example, Sugar\# t is an integration of Sugar\# 0 or Sugar\# 1 or Sugar\# 2. 

### Q6. why isn't there any rule that "gets rid of" deadline? 

Yes there is, we omitted it for a better presentation. 

### Q7. Section 3.4: is the notation [[\pi]]_s defined? 

$\llbracket {\pi} \rrbracket_s {=}  
{True}$ stands that: with the current stack state $s$,
the arithmetic constraint ${\pi}$ holds. 

### Q8. "We validate the front-end forward verifier against the state-of-the-art PAT" This does not seem to appear in the experiments. 

Sorry about the confusion. The validation here refers 
to the correctness of our forward verifier. The 
experiments is about the efficiency of our implementation. 



## To Reviewer B

### Q1. The significant overlap with the work in [Song & Chin 2020].

The major overlapping parts are:
1. they both integrate arithmetic constraints with 
extended regular expressions. 
2. they both support dependent values.
3. they both deploy term rewriting systems (TRS) as the back-end solvers. 

However, we argue that the differences are MORE THAN  `just applied to different programming languages`. 

(I) First of all, the detailed designs and the 
purposes of the designs are rather different: 

In [Song & Chin 2020], $\Phi_{send(n)} = n{<}5 \wedge Send^n$ stands 
for the specification of function $send(n)$, which emits the event 
$Send$ $n$ times.
As in $\Phi_{send(1)} = 1{<}5 \wedge Send$, or 
$\Phi_{send(3)} = 3{<}5 \wedge Send{\cdot}Send{\cdot}Send$. 
However, in current work: $\Phi_{send(n)} = n{<}5 \wedge Send \# n$
stands for the function $send(n)$ emits the event 
$Send$ ONCE, but the time of emitting $Send$ has a upper 
bound 5. This difference can be spotted in the specification semantics models of each paper  
(Fig. 7 in current paper vs. Fig. 4 in [Song & Chin 2020]). 

(II) Secondly, apart from the dependent values, 
in current work, the specification supports $\pi?$ (stands for a blocking waiting for a certain 
constraint to be satisfied) and the concurrency constructor || 
(cf Fig. 6). These are generally essential 
in timed verification (or more generally, for asynchronous programming), 
which are simply not supported in [Song & Chin 2020]. 

(III) Thirdly, if the TRS in [Song & Chin 2020] wished to 
support the inclusion checking 
of $TimEffs$ in this work, it needs to deal 
with the different semantics of the logic and extra operators. 
These achievements are considered to be the contributions 
of the TRS in the current paper. The detailed technical differences 
can be spotted in the rewriting rules in each paper (Sec. 5 in current paper vs. Sec. 5 in [Song & Chin 2020]). 

Lastly, we acknowledge that our current work is an extensions 
of [Song & Chin 2020], and we sincerely thank our reviews of pointing 
it out, which should have explained better in the submission. 

### +P1: The code in Fig. 1 says (I think) that addNSugar will emit the event Sugar after at least n time units. But the text (lines 63-68) seems to indicate that n portions of Sugar will be added, ie Sugar will be emitted n times.




## To Reviewer C

### Q1. Which aspects of 