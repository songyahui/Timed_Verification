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

It should have. We will need to add a rule where 
e reduced to a value within the deadline. Then we can "gets rid of" the deadline. 

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

### +P1: The code in Fig. 1 says that addNSugar will emit the event Sugar after at least n time units. But the text (lines 63-68) seems to indicate that n portions of Sugar will be added, ie Sugar will be emitted n times.

Event `Sugar` denotes the completion of the whole sugar addition phase (which adds n portions of Sugar in total). 
We will change `Sugar` to `EndSugar` (as suggested by our review A) and revise the explanations. 

### +P2: line 90 “valid traces \Phi' … why “valid”? I thought that \Phi' is the specification of the program. Are some traces invalid? If so, where is the term "invalid trace" defined?

$\Phi^\prime$ indeed is the specification of the program. In another word, 
it is an over-approximation (or superset per se) of all the desired/expected behaviours. 
We consider any unexpected traces  are `invalid`. 

### P4 line 312, you are talking of assignments \alpha^*, but you do not define them anywhere.

$\alpha$ is defined in Fig. 5 (assignment), and $\alpha^*$ is a list of $\alpha$. 

### +P5 line 318. What happens if e does not terminate on time? Does the program abort?

Like other modeling languages, the timed constructs 
are used in a abstract modeling way, where e must terminate 
before the deadline. If e is possibly go beyond the deadline, it should 
be modelled using conditionals where the other possibilities are explicitly modeled. 

### +P6 line 320 “potentially allows efficient clock manipulation”. I am not clear what you mean. Where does this clock manipulation happen? 

This comes from the context of how people usually make uses of the timed automata. 
For example, to use the model checker Uppaal, uses need to draw the automata 
themselves, including the clock naming, clock constrains annotation, 
transition constrains annotation. And this process most likely is not the most 
efficient way of manipulating the clocks, which leads to redundant clocks/constrains or bugs. 

### +P7 line 346, rule $[tot_1]$ should the conclusion say $(V, e_1’)$ rather than $(V, e’)$?

That's right, sorry about the confusion and thanks for pointing it out. Already fixed. 

### +P8 line 360. Are we missing a rule to eliminate $\textbf{deadline}$ when the execution of $e$ hs terminated and the deadline has not been reached.

That's right. We will need to add a rule where e reduced to a value within the deadline. 

### +P9 How do you express, eg the behaviour of two consecutive delays? 

As you mentioned, it should be the case of: 
$(V,\textbf{delay}\ t_1; \textbf{delay}\ t_2)  \rightarrow^{t_1+t_2} (V, ())$

This is achieved by applying the sequence rules $[seq_1]$ and $[seq_2]$ and delay
rules $[delay_1]$ and $[delay_2]$ in a certain order. 

### +P10 Make sure that the definitions of $d$, $s$, $\phi$ appear before Fig. 7. The page break make mw wonder whether these were defined anywhere. Moreover, I think you should replace $\triangleq$ in line 444, with $:$. Namely $d$ is one natural number, not the set of natural numbers.

Thanks! Already fixed accordingly. 


### +P11 I think the definition on line 430 is badly formed when $\pi$ is not satisfied -- ie non terminating recursion.

I am not sure if I understood the question correctly. 
Line 430 is $d, s, \varphi \models {\pi} \wedge \pi_1 ? es$,
and when $\pi_1$ is not satisfied at time $d$, it will continue
to block the execution till $\pi_1$ is satisfied. 
If $\pi_1$ is never satisfied,  $es$ will be eventually abandoned. 


### +P12 Fig. 7 I think some cases are missing: How is the judgement defined for $\textbf{A}(\nu, \alpha^*)$, or for $\tau (\pi)$. Also, what is $es$? Does it stand for $\theta$. I wonder whether the RHS on Lines 431-433 belong to the LHS on line 430.

$\textbf{A}(\nu, \alpha^*)$, $\tau (\pi)$, $\overline{A}$ and  $\_$ are possible constructors 
of $ev$ (cf Fig. 6). So the corresponding case is in line 423 for $\pi \wedge ev$. 

And es is for  $\theta$, it supposed to be `\es` in our latex writing. Sorry! Fixed already. 

To define the LHS of 431, it includes all the RHS from lines 431 - 434. 

### +P14 line 470, I think you also need to say that $\{\pi_i,\theta_i\}\in\{\Pi,\Theta\}$

Fixed, thanks!

### +P15 Lines 505-509. I think the definition does not take into consideration that it is possible for $e_1$ to execute and apply some side-effects to the $V$, then for $d$ to be exceeded before $e_1$ terminates, and then we continue with $e_2$. I think the rule needs to consider the side-effects of the incomplete $e_1$ too.

There is no possible incompletion of $e_1$ in timeout. 
Informally, in process $e_1$ timeout[𝑑] $e_2$, the first 
observable event of
$e_1$ shall occur before d time units elapse 
(since the process starts). Otherwise, $e_2$ takes over control
after exactly 𝑑 time units elapse. 

So it's either $e_1$ or $e_2$ to be executed. The formal semantics can 
be found in $[to_1]$ to $[to_4]$ (on top of the page 8).

### +P16

### +P18 Is there a definition of when $\Phi \sqsubseteq \Phi’$ is valid? 

Definition 2.2 (TimEffs Inclusion), at line 211. 

### +P19 Can you describe the 16 $C^t$ programs used in the benchmark in section 6?



## To Reviewer C

### Q1. Which aspects of 