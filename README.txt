This is the artifact for paper "Automated Verification for Real-Time Systems
via Implicit Clocks and an Extended Antimirov Algorithm"


# Automated Timed Temporal Verification

The correctness of real-time systems depends both on the correct functionalities and the realtime constraints. To go beyond the existing Timed Automata based techniques, we propose a novel solution that integrates a modular Hoare-style forward verifier with a term rewriting system (TRS) on Timed Effects (TimEffs). The main purposes are to increase the expressiveness, dynamically create clocks, and efficiently solve constraints on the clocks. We formally define a core language Ct, generalizing the real-time systems, modeled using mutable variables and timed behavioral patterns, such as delay, timeout, interrupt, deadline. Secondly, to capture real-time specifications, we introduce TimEffs, a new effects logic, that extends regular expressions with dependent values and arithmetic constraints. Thirdly, the forward verifier reasons tempo- ral behaviors – expressed in TimEffs – of target C^t programs. Lastly, we present a purely algebraic TRS, i.e., an extended Antimirov algorithm, to efficiently prove language inclusions between TimEffs. To demonstrate the feasibility of our proposals, we prototype the verification system; prove its soundness; report on case studies and experimental results.


## Build from source (tested on Ubuntu 18)

- Dependencies:

Install opam: (cf. https://opam.ocaml.org/doc/Install.html)
```
sudo apt install git
sudo apt install curl
bash -c "sh <(curl -fsSL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh)"
opam init
sudo apt install make 
sudo apt install gcc
```
Install ocaml and libraries:
```
opam switch create 4.13.1
eval $(opam env)
opam install menhir
```
Install z3 and dune:
```
opam init
eval `opam config env`
opam update
opam switch create 4.13.1
eval `opam config env`
opam install z3
sudo apt-get install whitedune
```

- Get the source code and build 
```
https://github.com/songyahui/AlgebraicEffect
cd AlgebraicEffect 
eval $(opam env)
```



### Examples:

Program Verification

```
cd code 
dune exec ./Forward.exe src/Validation/1_delay.c
```

### To Clean:

``` 
dune clean
```

# Benchmark:

Our benchmark contains three folders:
- Validation: We manually annotate TimEffs specifications for a set of synthetic examples (for about 54 programs), to test the main contributions, including: computing effects from symbolic timed programs written in C t ; and the inclusion checking for TimEffs with the parallel composition, blok waiting operator and shared global variables.

- Experiment1: For 16 C^t programs, and the annotated temporal specifications are in a 1:1 ratio for succeeded/failed cases. We record the evaluation 
results in Table 3 in the paper 

- Experiment12: comparison with the PAT [16] model checker using real-life Fischer’s mutual exclusion algorithm. 

