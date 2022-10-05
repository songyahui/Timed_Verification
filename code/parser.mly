%{ open Ast %}
%{ open List %}

%token <string> EVENT
%token <string> VAR
%token <int> INTE
%token <string> STRING
%token <bool> TRUEE  
%token <bool> FALSEE
%token EMPTY ASSERTKEY EVENTKEY CHOICE LPAR RPAR CONCAT  POWER MINUS TRUE FALSE DISJ CONJ   ENTIL INTT BOOLT VOIDT  (* OMEGA *)
%token LBRACK RBRACK COMMA SIMI  IF ELSE REQUIRE ENSURE LSPEC RSPEC  LBrackets  RBrackets 
%token EOF GT LT EQ GTEQ LTEQ INCLUDE SHARP EQEQ UNDERLINE KLEENE NEGATION 
%token LILOR COLON GUARD 
%token TimeoutKEY DeadlineKEY DelayKEY InterruptKEY

%left CHOICE
%left CONCAT
%left DISJ
%left CONJ

%start prog ee es_p 
%type <(Ast.entilment) list > ee
%type <Ast.program> prog
%type <Ast.es> es_p
%%

ee: 
| EOF {[]}
| a = entailment SIMI r = ee { append [a] r }


es_p: r = es EOF { r }


type_: 
| INTT {INT}
| BOOLT {BOOL}
| VOIDT {VOID}

singleP: t = type_   var = VAR {[(t, var)]}

param:
| {[]}
| p = singleP {p}
| p1 = singleP  COMMA  p2 = param {append p1 p2 }

real_singleP: e = expres {[e]}

real_param:
| p = real_singleP {p}
| p1 = real_singleP  COMMA  p2 = real_param {append p1 p2 }

value:  
| {Unit}
| LPAR RPAR {UnitPAR}
| t = INTE {Integer t}
| b =  TRUEE {Bool b }
| b =  FALSEE {Bool b }
| v = VAR {Variable v}
| s = STRING {String s}

assign:
| s = VAR COLON EQ v = term { (s, v)} 

parm:
| {None}
| LPAR i=value RPAR {Some i}

assign_list:
| {[]}
| a = assign {[a]}
| a= assign SIMI rest=assign_list {a :: rest}

maybe_assign_list:
| {[]}
|LBRACK op=assign_list RBRACK {op}


expres_help : 
| v= value {Value v }
| t = type_ name = VAR EQ e = expres_help {LocalDel (t, name, e)}
| name = VAR LPAR vlist = real_param RPAR {Call (name, vlist)}
| EVENTKEY LBrackets ev = STRING p=parm RBrackets ops = maybe_assign_list {EventRaise (ev,  p,  ops)}
| TimeoutKEY LPAR e1 = expres_help COMMA e2 = expres_help COMMA t = term  RPAR  {Timeout(e1, e2, t)}
| InterruptKEY LPAR e1 = expres_help COMMA e2 = expres_help COMMA t = term  RPAR  {Interrupt(e1, e2, t)}

| DeadlineKEY LPAR e = expres_help COMMA t = term  RPAR {Deadline(e, t)}
| DelayKEY LPAR t = term RPAR {Delay t}
| LBrackets p=pure RBrackets  e = expres_help {GuardE(p, e)}
| ASSERTKEY LPAR eff = effect RPAR {Assertion eff}
| a = assign {Assign a}
cond:
| e1 = value  EQEQ e2 = value { (e1, e2 ,"==")}
| e1 = value  LTEQ e2 = value { (e1, e2 ,"≤")}
| e1 = value  GTEQ e2 = value { (e1, e2 ,"≥")}
| e1 = value  GT e2 = value { (e1, e2 ,">")}
| e1 = value  LT e2 = value { (e1, e2 ,"<")}


expres:
| e = expres_help {e } 
| e1 = expres_help SIMI e2 = expres {Seq (e1, e2)}
| e1 = expres_help LILOR e2 = expres {Parallel (e1, e2)}

| IF LPAR e1 = cond RPAR LBRACK e2 = expres RBRACK ELSE LBRACK e3 = expres RBRACK {IfElse (e1, e2, e3)}
| e1 = value CHOICE e2 = value {BinOp(e1, e2,"+" )}
| e1 = value MINUS e2 = value {BinOp(e1, e2,"-" )}

(*PrePost([(TRUE, Emp)], [(TRUE, Emp)])*)
meth : t = type_   name = VAR   LPAR p = param RPAR s = spec LBRACK e = expres RBRACK {Method (Meth (t , name, p, s, e))}
head : SHARP INCLUDE str= STRING {Include str} 


prog_rest:
| EOF {[]}
| tl = prog hd = prog_rest  {append tl hd}

prog:
| me =  meth p = prog_rest {append [me] p}
| hd = head  p = prog_rest {append [hd] p}
| assign = assign SIMI  p = prog_rest {append [Global(assign)] p}

morePostcondition:
| {[]}
| ENSURE e2 = effect rest=morePostcondition {e2::rest}

spec: LSPEC REQUIRE e1 = effect pos =morePostcondition  RSPEC {PrePost(e1, pos)}

term:
| str = VAR { Var str }
| n = INTE {Number n}
| LPAR r = term RPAR { r }
| a = term b = INTE {Minus (a, Number (0 -  b))}

| LPAR a = term MINUS b = term RPAR {Minus (a, b )}

| LPAR a = term CHOICE b = term RPAR {Plus (a, b)}




pure:
| TRUE {TRUE}
| FALSE {FALSE}
| NEGATION LPAR a = pure RPAR {Neg a}
| LPAR r = pure RPAR { r }
| a = term GT b = term {Gt (a, b)}
| a = term LT b = term {Lt (a, b)}
| a = term GTEQ b = term {GtEq (a, b)}
| a = term LTEQ b = term {LtEq (a, b)}
| a = term EQ b = term {Eq (a, b)}
| a = pure CONJ b = pure {PureAnd (a, b)}
| a = pure DISJ b = pure {PureOr (a, b)}


maybeGuard :
| {None}
| GUARD {Some "a"}

es:
| EMPTY { Emp }
| LBrackets op=pure RBrackets m = maybeGuard {
  match m with 
  | None -> Event (Tau op)
  | Some _ -> Guard(op)
}
| str = EVENT p=parm ops= maybe_assign_list { Event (Present (str, p, ops)) }
| NEGATION str = EVENT {Event (Absent str)}
| LPAR r = es RPAR { r }
| a = es CHOICE b = es { ESOr(a, b) }
| a = es LILOR b = es { Par(a, b) }

| LPAR r = es SHARP t = term RPAR { Ttimes(r, t )}
| UNDERLINE {Event (Any)}
| a = es CONCAT b = es { Cons(a, b) } 
| LPAR a = es POWER KLEENE RPAR{Kleene a}


(*
singleVAR: var = VAR {[var]}

existVar:
| {[]}
| p = singleVAR {p}
| p1 = singleVAR  COMMA  p2 = existVar {append p1 p2 }
*)

effect:
| LPAR r = effect RPAR { r }
| a = pure  CONJ  b= es  { [(a, b)]}
| a = effect  DISJ  b=effect  {List.append a b}




entailment:
| lhs = effect   ENTIL   rhs = effect {EE (lhs, rhs)}


