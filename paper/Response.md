# OVERVIEW: 

Many thanks to our reviewers for their interest 
and appreciation of certain aspects of our work. 

We acknowledge our weaknesses in related work and evaluations. 
Thanks again for the time and effort in pointing out our typos 
and giving constructive suggestions. 

We considered all the valuable comments and made the 
following change list. 


# CHANGE LIST: 


| | Changes     | Description | Timeline (Working days)    |
| ---  | ----------- | ----------- | ----------- |
|1 | Typos       | Mentioned in the reviews  | Already Done| 
|2 | Related work | Further compare our work with i) other rewriting systems for timed verification; ii) dynamic clock manipulations for timed automata, and iii) [Song & Chin 2020].   | 5 days (Partly done in the response) |
|3 | Evaluation data | Add more detailed explanations for the evaluation and make the benchmark and documentation public | 5-10 days |
|4 | Paper polishing | Find a buddy to check the writings | 5 days | 
|  | In total  | | 15 - 20 days


In total, we plan to finish all the changes within one month.  



# RESPONSE: 

###  Common Questions Upon the Evaluation

#### Q1. Where do the models come from?  

The evaluation benchmark (16 selected programs) was created by ourselves. 
We developed a set of testing programs (~70) during the development process.
The testing programs were designed functionality-oriented, where each 
forward rule in Sec. 4.1 has 3-8 testing programs. The rest ~20 programs 
are mixed combinations of different constructs and some stress tests.  

Our selected programs were from the last ~20 programs varying from lines of code. 

#### Q2. We like to explain why not to choose existing benchmarks:

Model checkers like Uppaal take timed automata directly as their inputs, 
which is not feasible for our tool. 

Model checkers like PAT take timed process algebras as their inputs are more 
feasible. We indeed included some tests from their examples in our tests, 
such as the Fischer’s Mutual Exclusion Protocol (cf Fig. 4).
But they do not support value-dependent bounds in their timed behavioral patterns.
However, we take the `value-dependent bounds` as one of our main novelties. Therefore 
most programs in our benchmark are created ourselves and 
have value-dependent time bounds. 

#### Q3. What kinds of specifications do you check and any comparisons with PAT?  

All the specifications are with value-depended constructors. 
For each program, the very first specification is its strongest postcondition 
(which should be valid). Then we derived the rest specifications by 
adding various mutations (or a mixture of the mutations) into the strongest postcondition, such as: 
disjunctions, the negation of certain events, modification of the clock constraints, 
inserting parallel traces etc. 

For the programs we included from the PAT benchmark, we validate the verification 
results against PAT implementation (as in given the same logic model and the same 
specification, our tool and PAT return the same verification results). 
For the rest specifications, we manually label the expected verification results. 
And all the results are presented in Table. 3 were as expected. 


#### Q4. Do the authors plan to make their tools and experiments publicly available? 

Yes. The source code is open-sourced now. We 
plan to release the benchmark after further documentation. 


---

###  To Reviewer A

Many thanks for pointing out the related works. We will be checking them 
out and add comparisons accordingly. 

#### Q1. Does this mean that the time is discrete, or does this mean that the time bounds are integer-valued (while time can still be continuous)?
Time is continuous. The current implementation makes use of SMT in 
integer numbers domain.
Given the suitable SMT solver, it is not hard to adapt it to real numbers. 

#### Q2. I find the event name Sugar slightly misleading: if this denotes the completion of the sugar addition phase, perhaps EndSugar would be more appropriate? 
`Sugar` denotes the completion of the sugar addition phase; we will change it to `EndSugar`. Thanks!

#### Q3. "our effects provide more detailed information than traditional timed verification, and in fact, it cannot be fully captured by any prior works " This requires some discussion and does not seem obvious to me, especially when compared with Uppaal.

Using the example $\Phi_{addNSuggar(n)} = n{<}3 \wedge n{=}t \wedge Sugar\# t $, 
there are two main advantages shown comparing the proposed Effects with timed-automata based modelling:
1. The time bounds can be depended on the function inputs. The specifications are dynamically instantiated 
during the execution. 
2. the time-bounds can be a range of values (possibly an infinite set). In this example, Sugar\# t is an integration of Sugar\# 0 or Sugar\# 1 or Sugar\# 2. 

#### Q4. why isn't there any rule that "gets rid of" deadline? 

It should have. We need to add a rule where 
e is reduced to a value within the deadline. Then we can "get rid of" the deadline. 

#### Q5. Section 3.4: is the notation [[\pi]]_s defined? 

$\llbracket {\pi} \rrbracket_s {=}  
{True}$ stands that: with the current stack state $s$,
the arithmetic constraint ${\pi}$ holds. 

#### Q6. "We validate the front-end forward verifier against the state-of-the-art PAT" This does not seem to appear in the experiments. 

Sorry about the confusion. The validation here refers 
to the correctness of our forward verifier. The 
experiment is about the performance of our implementation. 



---

###  To Reviewer B

#### Q1. The a significant overlap with the work in [Song & Chin 2020].

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
in timed verification (or, more generally, for asynchronous programming), 
which are not supported in [Song & Chin 2020]. 

(III) Thirdly, if the TRS in [Song & Chin 2020] wished to 
support the inclusion checking 
of $TimEffs$ in this work, it needs to deal 
with the different semantics of the logic and extra operators. 
These achievements are considered to be the contributions 
of the TRS in the current paper. The detailed technical differences 
can be spotted in the rewriting rules in each paper (Sec. 5 in the current paper vs. Sec. 5 in [Song & Chin 2020]). 

Lastly, we acknowledge that our current work is an extension 
of [Song & Chin 2020], and we sincerely thank our reviews for pointing 
it out, which should have been explained better in the submission. 

#### +P1: The code in Fig. 1 says that addNSugar will emit the event Sugar after at least n time units. But the text (lines 63-68) indicates that n portions of Sugar will be added, i.e., Sugar will be emitted n times.

Event `Sugar` denotes the completion of the whole sugar addition phase (which adds n portions of Sugar in total). 
We will change `Sugar` to `EndSugar` (as suggested by our review A) and revise the explanations. 

#### +P2: line 90 “valid traces \Phi' … why “valid”? I thought that \Phi' is the specification of the program. Are some traces invalid? If so, where is the term "invalid trace" defined?

$\Phi^\prime$ indeed is the specification of the program. In other words, 
it is an over-approximation (or superset per se) of all the desired/expected behaviors. 
We consider any unexpected traces are `invalid`. 

#### P4 line 312, you are talking of assignments \alpha^*, but you do not define them anywhere.

$\alpha$ is defined in Fig. 5 (assignment), and $\alpha^*$ is a list of $\alpha$. 

#### +P5 line 318. What happens if e does not terminate on time? Does the program abort?

Like other modeling languages, the timed constructs 
are used in an abstract modeling way, where e must terminate 
before the deadline. If e possibly goes beyond the deadline, it should 
be modeled using conditionals where the other possibilities are explicitly modeled. 

#### +P6 line 320 “potentially allows efficient clock manipulation”. I am not clear what you mean. Where does this clock manipulation happen? 

This comes from the context of how people usually make use of the timed automata. 
For example, to use the model checker Uppaal, users need to draw the automata 
themselves, including the clock naming, clock constrains annotation, 
transition constrains annotation. And this process most likely is not the most 
efficient way of manipulating the clocks, which leads to redundant clocks/constraints or bugs. 

#### +P7 line 346, rule $[tot_1]$ should the conclusion say $(V, e_1’)$ rather than $(V, e’)$?

That's right; sorry about the confusion, and thanks for pointing it out. It is already fixed. 

#### +P8 line 360. Are we missing a rule to eliminate $\textbf{deadline}$ when the execution of $e$ is terminated, and the deadline has not been reached?

That's right. We will need to add a rule where e reduced to a value within the deadline. 

#### +P9 How do you express, eg the behaviour of two consecutive delays? 

As you mentioned, it should be the case of: 
$(V,\textbf{delay}\ t_1; \textbf{delay}\ t_2)  \rightarrow^{t_1+t_2} (V, ())$

This is achieved by applying the sequence rules $[seq_1]$ and $[seq_2]$ and delay
rules $[delay_1]$ and $[delay_2]$ in a certain order. 

#### +P10 Make sure that the definitions of $d$, $s$, $\phi$ appear before Fig. 7. The page break make mw wonder whether these were defined anywhere. Moreover, I think you should replace $\triangleq$ in line 444, with $:$. Namely $d$ is one natural number, not the set of natural numbers.

Thanks! Already fixed accordingly. 


#### +P11 I think the definition on line 430 is badly formed when $\pi$ is not satisfied -- ie non terminating recursion.

I am not sure if I understood the question correctly. 
Line 430 is $d, s, \varphi \models {\pi} \wedge \pi_1 ? es$,
and when $\pi_1$ is not satisfied at time $d$, it will continue
to block the execution till $\pi_1$ is satisfied. 
If $\pi_1$ is never satisfied,  $es$ will be eventually abandoned. 


#### +P12 Fig. 7 I think some cases are missing: How is the judgement defined for $\textbf{A}(\nu, \alpha^*)$, or for $\tau (\pi)$. Also, what is $es$? Does it stand for $\theta$. I wonder whether the RHS on Lines 431-433 belong to the LHS on line 430.

$\textbf{A}(\nu, \alpha^*)$, $\tau (\pi)$, $\overline{A}$ and  $\_$ are possible constructors 
of $ev$ (cf Fig. 6). So the corresponding case is in line 423 for $\pi \wedge ev$. 

And es is for  $\theta$, it supposed to be `\es` in our latex writing. Sorry! Fixed already. 

To define the LHS of 431, it includes all the RHS from lines 431 - 434. 

#### +P14 line 470, I think you also need to say that $\{\pi_i,\theta_i\}\in\{\Pi,\Theta\}$

Fixed, thanks!

#### +P15 Lines 505-509. I think the definition does not take into consideration that it is possible for $e_1$ to execute and apply some side-effects to the $V$, then for $d$ to be exceeded before $e_1$ terminates, and then we continue with $e_2$. I think the rule needs to consider the side-effects of the incomplete $e_1$ too.

There is no possible incompletion of $e_1$ in timeout. 
Informally, in process $e_1$ timeout[𝑑] $e_2$, the first 
observable event of
$e_1$ shall occur before d time units elapse 
(since the process starts). Otherwise, $e_2$ takes over control
after exactly 𝑑 time units elapse. 

So it's either $e_1$ or $e_2$ to be executed. The formal semantics can 
be found in $[to_1]$ to $[to_4]$ (on top of the page 8).


#### +P18 Is there a definition of when $\Phi \sqsubseteq \Phi’$ is valid? 

Definition 2.2 (TimEffs Inclusion), at line 211. 



---

###  To Reviewer C

#### Q1. Please comment on the related work I cite.


[1] Deductive Verification of Real-Time Systems Using STEP, by Bjorner, Manna, Sipma, Uribe proposes
[2] Specification of real-time and hybrid systems in rewriting logic, by Olveczky and Meseguer.
[3] Specification and Analysis of Real-Time and Hybrid Systems in Rewriting Logic - Olveczky (PhD thesis) 
[4] Verification of clocked and hybrid systems - Kesten, Manna, Pnueli

Thanks for pointing out the very related works, which used rewriting strategies to 
solve difference problems upon different format of the logics. 
[1,4] mention rewriting linear temporal logic formula; 
[2,3] mention rewriting timed automata, or timed extensions of Petri net;
and our work is rewriting extended regular expressions. 

We think the main differences get back to the expressiveness of the logics.
As we presented in the paper, we aim at studying more practical and expressive 
logics, therefore it leads to the creation/rewriting of our TimEffs. 
The dependent values and putting timed traces into the precondition are novel 
comparing to prior works. 
Together with the cited papers, we certainly show the applicability of 
rewriting systems.  



#### Q2. Please comment on some of the technical questions I raised 

1. I find it strange that you don't have iterative loops. Why is that?

The language allows each iterative
loop to be optimized to an equivalent tail-recursive method, where mutation
on parameters is made visible to the caller. The technique of translating away
iterative loops is standard and is helpful in further minimising our core language. 

2. Why talk about trace leading to a method in preconditions? 

We politely disagree upon the opinion mentioned in the review: 
`While verification of a method does depend on the values of variables at the time it's called, the events that happened earlier seem irrelevant.` 

Just like particular requirements of the input values, there are possible 
requirements upon the history traces. 
For example, before reading a file, we wish to make sure the file was actually opened 
(and not yet closed) is the history. This can be written in precondition as:
$\Phi_{pre} = \_^\star {\cdot} Open {\cdot} ({\overline{Close}})^\star $. 
Such examples extend to the timed processes in different contexts. 


3. Are quantified Presburger conditions used in your benchmarks?

We do not have quantified Presburger conditions in current benchmarks. 
Indeed 'Purely universal quantification' better describes our implementation. 
(Although having TRS solving quantified Presburger conditions with traces seems 
useful and challenging.)





#### Q3. Do you capture the strongest post? 

To be precise, it only captures the 'strongest over-approximation'. 

The forward verifier creates over-approximation when there are conditionals 
(cf [FV-If-Else-Local] on top of page 11). 

For example, $\Phi_{post}{=} (n {>} 0 \wedge A{\cdot}B)  \vee (n {\leq} 0 \wedge C{\cdot}D)$ 

Therefore in theorem 4.1,
if we have $\{P\}\ e\ \{Q\}$ 
 we can only say there exists a post in Q which captures the 
actual execution. 


#### Q4. Are there any relative completeness results that you can show that narrow the space where your reasoning is incomplete?
#### Q5. Can you give some (simple) examples where your technique does not work?

We like to answer Q4 and Q5 together.

For example, while proving this following (expected to be valid) inclusion: 
$ t_1 {<}3 {\wedge} t_2 {<}4 {\wedge}  (\epsilon \# t_1) {\cdot} (\epsilon \# t_2) 
\sqsubseteq  t {<}7 {\wedge} (\epsilon \# t)$ 

The current rewriting would simple unify $t_1$ and $t$ leaving $t_2$ behind, which 
leads to the next step:

$ t_2 {<}4 {\wedge}  (\epsilon \# t_2) 
\sqsubseteq   \epsilon $, then eliminate $(\epsilon \# t_2) $ from the both side, 
leads to the next step:

$True {\wedge} \epsilon \sqsubseteq   \bot$, then disproves this inclusion. 

This can be solved by adding an axiom: $(\epsilon \# t_1) {\cdot} (\epsilon \# t_2) = 
(\epsilon \# (t_1{+}t_2))$. 
However, we did not include it because it seems to be leading to other incomplete situations. 




#### Q6. Am I reading it correctly that your system is able to prove all valid properties and disprove all invalid ones?
Yes. cf  Q3 in `Common Questions Upon the Evaluation`. 


#### +P16 Theorem 4.1: You are saying “produces a concrete execution time d, and event sequence" …. But the operational semantics does not produce one execution time. Perhaps it produces a sequence of execution times and event, and then you obtain d through the sum of all execution times, and π by distilling all the events? I could not find the definition in the paper, but even som such a definition would allow me to distinguish important cases (eg delay(2).Sugar.delay(1).Sugar from delay(3).Sugar.Sugar).

-> `Perhaps it produces a sequence of execution times and event, and then you 
obtain d through the sum of all execution times`

That' right. If we use `|-|` to denote one time unit, and `S` denotes the emission of Sugar, then

delay(2).Sugar.delay(1).Sugar is 
```
0 1 2 3 4
|-|-|-|-|--> d
    S S
```

and delay(3).Sugar.Sugar is 
```
0 1 2 3 4
|-|-|-|-|--> d
      S 
      S
```

In the semantic of effects, Fig.7 line 423, we defined the emission of a single event takes 0 time. 

#### +P16 Proof of Theorem 4.1. I had a look in the appendix, and have several questions

a. It is not clear whether the proof is by induction on the number of steps 
  or the shape of the expression. Looking at the proof it seems that it is by 
  the latter, but if so the proof would not go through, because method call 
  increases the expression.

c. Proof is missing method call, and the proof of this requires, 

Answer for a and c:
It is induction on the shape of the expression. 

Informally, the operation semantics rule for method call is:
```
mn(x^*)[P, Q]{e} {\in} P    
the history traces should entail P
e[v*/x*] ==> e'
------------------------------- [op-call]
(V, mn(v*)) --> (V, e')
```
The promise of [op-call] assumes mn(x^*) is verified, i.e., |- {P} e {Q} is valid. 
(P, Q are the pre/post-condition of mn) 

The forward rule of call [FV-Call] is defined at line 520. 

Based on Theorem 4.1:
Given configuration (V, mn(v*)), it equals to (V, e[v*/x*]). 

There are two cases: 

i) $\{V, \epsilon \} \in P$, by [FV-Call], 
|- {$\{V, \epsilon \}$} e[v*/x*] {$\{V, \epsilon \} \cdot$  Q[v*/x*]}, 
prove by induction;

ii) $\{V, \epsilon \} \notin P$, both execution and forward rule got stuck. 


---

b. The proof for timeout does not cover the case where e1​
  started but times out, and we continue with e2

This is a similar question to +P15. 
As we have answered, the semantics of $e_1$ timeout[𝑑] $e_2$ is, 
if the initial events (written as $hd(\Theta_1)$ in the rule $[FV\text{-}Timeout]$ at line 508) 
of $e_1$ happened before time d, then $e_1$ continues to take the control; 
otherwise, i.e., $e_1$ never started within time d, $e_2$ takes the control. 

Therefore `the case where e1​
  started but times out, and we continue with e2` should never happen. 


---

d. I think Theorem 5.7 Proof is missing the inductive step
 In line 1046, the proof for the unfold is the inductive step. 
 The rule adds the current inclusion into the hypostasis, then proves the inclusion 
 of its derivatives. 

