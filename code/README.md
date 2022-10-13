# Automated Timed Temporal Verification

In this work, we study temporal verification of compositional real-time systems, modeled using mutable variables and timed processes. Instead of explicitly manipulating clock variables, several compositional timed behavioral patterns, such as delay, timeout, deadline, are introduced to capture quantitative timing constraints. The idea is to dynamically create clocks and solve constraints on the clocks.
We propose a novel solution for timed verification via a compositional Hoare-style forward verifier and a term rewriting system (TRS) on Timed Effects (TimEffs). We formally define a core language 𝜆t , generalizing the timed processes. Secondly, to capture real-time specifications, we introduce TimEffs, a new effects logic, that extends Kleene Algebra with dependent values and arithmetic constraints. Thirdly, the forward verifier infers temporal behaviors of given 𝜆t programs, expressed in TimEffs. Lastly, we present a purely algebraic TRS, to efficiently prove language inclusions between TimEffs. To demonstrate the feasibility of our proposals, we prototype the verification system; prove its correctness; report on case studies and the experimental results.



## Online demo


### To Compile:

```
git clone https://github.com/songyahui/EFFECTS.git
git checkout timed_effects
cd EFFECTS
chmod 755 clean 
chmod 755 compile 
./compile
```

### Dependencies:

```
opam switch create 4.10.2
eval $(opam env)
opam install menhir.20211128
# sudo apt-get install menhir
# sudo apt-get install z3
```

### Examples:

Entailments Checking 

```
./trs src/effect/ex1.ee src/effect/output.txt 
```

Program Verification

```
./verify src/program/coffee.c
```

### To Clean:

``` 
./clean
```

### Benchmark:


# 


ocamlc -c Checker.cmo EE/Checker.ml 



yahuis@r-116-102-25-172 code % dune exec ./Forward.exe src/program/fischer_5proc.c      
                                    
========== Module: proc ==========
[Pre  Condition] e>0∧d<e ∧ (_^*)
[Post Condition] e>0∧d<e∧f0≥0∧f0≤d∧f1=e ∧ [x=-1]?((U(i))#f0) . ((ε)#f1) . (([x=i] . C(i) . E(i)) + ([(~(x=i))]))
[Final  Effects] e>0∧d<e ∧ ε
[Inferring Time] 0.00499999999999 ms
[Succeed  Cases] 0 case(s) with avg time nan ms
[Failure  Cases] 1 case(s) with avg time 0.024 ms

* le>0∧ld<le ∧ ε |- re>0∧rd<re∧rf0≥0∧rf0≤rd∧rf1=re ∧ [x=-1]?((U(i))#rf0) . ((ε)#rf1) . (([x=i] . C(i) . E(i)) + ([(~(x=i))]))  ***> ⊤ [DISPROVE] 


========== Module: main ==========
[Pre  Condition] e>0∧d<e ∧ ε
[Post Condition] d<e ∧ ([cs≤1]^*)
[Final  Effects] d<e∧f0≥0∧f0≤d∧f1=e∧e>0 ∧ (([x=-1]?((U(0))#f0) . ((ε)#f1) . (([x=0] . C(0) . E(0)) + ([(~(x=0))]))) || ((([x=-1]?((U(1))#f0) . ((ε)#f1) . (([x=1] . C(1) . E(1)) + ([(~(x=1))]))) || ((([x=-1]?((U(2))#f0) . ((ε)#f1) . (([x=2] . C(2) . E(2)) + ([(~(x=2))]))) || ((([x=-1]?((U(3))#f0) . ((ε)#f1) . (([x=3] . C(3) . E(3)) + ([(~(x=3))]))) || ([x=-1]?((U(4))#f0) . ((ε)#f1) . (([x=4] . C(4) . E(4)) + ([(~(x=4))]))))))))))
[Inferring Time] 41.702 ms]
====================================
[Result] Succeed
[Verification Time: 10338301.077 ms]
 


Time for inference    :0.00499999999999
[AskZ3 Count] 1152310
yahuis@r-116-102-25-172 code % 