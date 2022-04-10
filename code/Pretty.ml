(*----------------------------------------------------
----------------------PRINTING------------------------
----------------------------------------------------*)

open String
open List
open Ast
open Printf
open Askz3
open Int32


exception Foo of string



(*used to generate the free veriables, for subsititution*)
let freeVar = ["t1"; "t2"; "t3"; "t4";"t5";"t6";"t7";"t8";"t9";"t10"
              ;"t11"; "t12"; "t13"; "t14";"t15";"t16";"t17";"t18";"t19";"t20"
              ;"t21"; "t22"; "t23"; "t24";"t25";"t26";"t27";"t28";"t29";"t30"];;



let rec getAfreeVar (varList:string list):string  =
  let rec findOne li = 
    match li with 
        [] -> raise ( Foo "freeVar list too small exception!")
      | x :: xs -> if (exists (fun a -> String.compare a x == 0) varList) == true then findOne xs else x
  in
  findOne freeVar
;;


let rec input_lines file =
  match try [input_line file] with End_of_file -> [] with
   [] -> []
  | [line] -> (String.trim line) :: input_lines file
  | _ -> failwith "Weird input_line return value"

  ;;

let get_0 (a,_) = a ;;

let get_1 (_, a,_) = a ;;


(*To pretty print terms*)
let rec showTerms (t:terms):string = 
  match t with
    Var name -> name
  | Number n -> string_of_int n
  | Plus (t1, t2) -> (showTerms t1) ^ ("+") ^ (showTerms t2)
  | Minus (t1, t2) -> (showTerms t1) ^ ("-") ^ (showTerms t2)

  ;;

let string_of_value v : string = 
  match v with 
  | Unit  -> "unit"
  | Integer num -> string_of_int num
  | Bool b -> string_of_bool b 
  | Float f -> string_of_float f
  | Variable v -> v 
  | String str -> str
;;

let rec string_of_assigns li : string =
  match li with 
  | [] -> ""
  | (str, v):: rest -> str ^ " := " ^ showTerms v ^ ";" ^ string_of_assigns rest 
;;



(*To pretty print pure formulea*)
let rec showPure (p:pure):string =   
  match p with
    TRUE -> "true"
  | FALSE -> "false"
  | Gt (t1, t2) -> (showTerms t1) ^ ">" ^ (showTerms t2)
  | Lt (t1, t2) -> (showTerms t1) ^ "<" ^ (showTerms t2)
  | GtEq (t1, t2) -> (showTerms t1) ^ ">=" ^ (showTerms t2)
  | LtEq (t1, t2) -> (showTerms t1) ^ "<=" ^ (showTerms t2)
  | Eq (t1, t2) -> (showTerms t1) ^ "=" ^ (showTerms t2)
  | PureOr (p1, p2) -> "("^showPure p1 ^ "\\/" ^ showPure p2^")"
  | PureAnd (p1, p2) -> "("^showPure p1 ^ "/\\" ^ showPure p2^")"
  | Neg p -> "(!" ^ "(" ^ showPure p^"))"
  ;; 


(*To pretty print event sequences*)
let rec showES (es:es):string = 
  let string_of_event ev : string = 
    match ev with 
    | Present (str, param, ops) -> 
      let print_param = (
        match param with 
        | None -> ""
        | Some v -> "(" ^ string_of_value v ^ ")"
      )in 
      let print_ops = if List.length (ops) == 0 then "" else "{" ^ string_of_assigns ops ^ "}" in 
      str ^ print_param ^ print_ops
    | Absent str -> "!" ^ str
    | Any -> "_"
  in 
  match es with
    Bot -> "_|_"
  | Emp -> "emp"
  | Event (ev) -> string_of_event ev 
  | Guard (pi, es1) ->  "[" ^ showPure pi ^ "]" ^(showES es1)
  | Cons (es1, es2) -> "("^(showES es1) ^ " . " ^ (showES es2)^")"
  | ESOr (None, es1, es2) ->  "("^(showES es1) ^ " + " ^ (showES es2)^")"
  | ESOr (Some pi, es1, es2) -> "[" ^ showPure pi ^ "]"^ "("^(showES es1) ^ " + " ^ (showES es2)^")"
  | Ttimes (es, t) -> "("^(showES es) ^ "#" ^ (showTerms t)^")"
  | Kleene es -> "(" ^ (showES es) ^ "^" ^ "*"^")"
  | Par (es1, es2) -> "("^(showES es1) ^ " || " ^ (showES es2)^")"
  ;;




(*To pretty print effects*)
let rec showEffect (e:effect) :string = 
  match e with 
  | [] -> ""
  | [(p, es)] -> showPure p ^ "/\\" ^ showES es 
  | (p, es):: rest -> showPure p ^ "/\\" ^ showES es  ^ " \\/ "  ^ showEffect rest 
  ;;

let rec printType (ty:_type) :string =
  match ty with
    INT -> "int "
  | FLOAT -> "float "
  | BOOL  -> "bool "
  | VOID  -> "void ";;


let rec printParam (params: param):string = 
  match params with 
    [] -> ""
  | [(t, v)] -> printType t ^ v
  | (t, v)::xs ->  printType t ^ v ^ "," ^ printParam xs ;;


let rec print_real_Param (params: expression list):string = 
  let rec printarg v = (match v with
  | Value v -> string_of_value v 
  | Call (name, elist) -> name ^ "(" ^ print_real_Param elist ^ ")"
  | BinOp (e1, e2, str) -> string_of_value e1 ^ str ^ string_of_value e2 
  | _ -> "undefined"
  ) in 
  match params with 
    [] -> ""
  | [v] ->  printarg v
    
  | v::xs ->  
    let pre = printarg v in 
    pre ^ "," ^ print_real_Param xs ;;



let rec printExpr (expr: expression):string = 
  match expr with 
  | Value v -> string_of_value v 
  | LocalDel (t, v, e)->  printType t ^ v ^ " = " ^ printExpr e
  | Call (name, elist) -> name ^ "(" ^ print_real_Param elist ^ ")"
  (*| Assign (v, e) -> v ^ " = " ^ printExpr e *)
  | Seq (e1, e2) -> printExpr e1 ^ ";" ^ printExpr e2
  | Parallel (e1, e2) -> printExpr e1 ^ "||" ^ printExpr e2
  | GuardE (pi, e2) -> "[" ^ showPure pi ^ "] " ^ printExpr e2
  | EventRaise (ev, param, ops) -> ev ^ (
    match param with 
    | None -> ""
    | Some v -> "("^ string_of_value v ^")"
  )^ string_of_assigns ops 
  | Deadline (e, n) -> "deadline (" ^ printExpr e ^", " ^ string_of_value n ^")\n"
  | Timeout (e, n) -> "timeout (" ^ printExpr e ^", " ^ string_of_value n ^")\n"

  | Delay n -> "delay " ^  string_of_value n ^"\n"
  | IfElse (e1, e2, e3) -> "if " ^ printExpr e1 ^ " then " ^ printExpr e2 ^ " else " ^ printExpr e3 
  | Cond (e1, e2, str) -> string_of_value e1 ^ str ^ string_of_value e2 
  | BinOp (e1, e2, str) -> string_of_value e1 ^ str ^ string_of_value e2 
  | Assertion eff -> "Assert: " ^ showEffect eff 
  ;;


let compareParm (p1:int option ) (p2:int option ) :bool = 
  match (p1, p2) with 
    (None, None) -> true 
  | (Some n1, Some n2) -> n1 == n2
  | _ -> false 
  ;;

let compareEvent (ev1:(pure * string * int option * assign list)) (ev2:(pure * string * int option * assign list)):bool =
  let (_, str1, p1, _) = ev1 in
  let (_, str2, p2, _) = ev2 in
  String.compare str1 str2 == 0 && compareParm p1 p2
  ;;

let rec iter f = function
  | [] -> ()
  | [x] ->
      f true x
  | x :: tl ->
      f false x;
      iter f tl

let rec addConstrain effect addPi = List.map (fun (pi, eff) -> ( (PureAnd (pi, addPi)), eff))  effect
   ;;

let to_buffer ?(line_prefix = "") ~get_name ~get_children buf x =
  let rec print_root indent x =
    bprintf buf "%s\n" (get_name x);
    let children = get_children x in
    iter (print_child indent) children
  and print_child indent is_last x =
    let line =
      if is_last then
        "└─ "
      else
        "├─ "
    in
    bprintf buf "%s%s" indent line;
    let extra_indent =
      if is_last then
        "    "
      else
        "│   "
    in
    print_root (indent ^ extra_indent) x
  in
  Buffer.add_string buf line_prefix;
  print_root line_prefix x

let printTree ?line_prefix ~get_name ~get_children x =
  let buf = Buffer.create 1000 in
  to_buffer ?line_prefix ~get_name ~get_children buf x;
  Buffer.contents buf

type binary_tree =
  | Node of string * (binary_tree  list )
  | Leaf

let get_name = function
    | Leaf -> "."
    | Node (name, li) -> name;;

let get_children = function
    | Leaf -> []
    | Node (_, li) -> List.filter ((<>) Leaf) li;;


(*All the entailmnet rules, but so far not been used*)
type rule = LHSOR   | RHSOR 
          | LHSEX   | RHSEX 
          | LHSSUB  | RHSSUB 
          | LHSCASE | RHSCASE 
          | UNFOLD  | DISPROVE 
          | FRAME   | REOCCUR
          | RHSAND

(*the effects entailment context*)
type context =  ( pure * es * pure * es) list

type hypotheses = (es * es) list






let rec substituteTermWithAgr (t:terms) (realArg:expression) (formalArg: var):terms = 

  match t with 
    Var str -> if String.compare formalArg str == 0 then 
      
    (
      match realArg with 
      | Value v -> (
        match v with 
        | Integer n -> Number n
        | Variable v -> Var v
        | Bool true -> Number 1
        | Bool false -> Number 0
        | _ -> raise (Foo "substituteTermWithAgr")
      )
      | BinOp (Variable v, Integer n, "+") -> Plus (Var v, Number n)
      | BinOp (Variable v, Integer n, "-") -> Minus (Var v, Number n)
      | _ -> raise (Foo "substituteTermWithAgr exception")
    )
    else 
      (
      
      Var str )
  | Number n -> Number n
  | Plus (term, n) -> Plus (substituteTermWithAgr term realArg formalArg, n)
  | Minus (term, n) -> Minus (substituteTermWithAgr term realArg formalArg, n)
  ;;

let substituteValueWithAgr (i:value) (realArg:expression) (formalArg:var): value =
  match i with
  | Variable str -> if String.compare formalArg str == 0 then 
    (
      match realArg with 
      | Value v -> (
        match v with 
        | Integer n -> Integer n
        | Variable v -> Variable v
        | Bool true -> Integer 1
        | Bool false -> Integer 0
        | _ -> raise (Foo "substituteTermWithAgr")
      )
      | _ -> raise (Foo "substituteValueWithAgr exception")
    )
    else 
      (
      
        Variable str )
  | _ -> i 
;;

let rec substituteESWithAgr (es:es) (realArg:expression) (formalArg: var):es = 
  match es with 
    Bot  -> es
  | Emp  -> es
  | Event (Present (str, Some i, ops))  -> Event (Present (str, Some (substituteValueWithAgr i realArg formalArg),  ops))
  | Event _  -> es
  | Guard (p, es1) -> Guard (p, substituteESWithAgr es1 realArg formalArg)
  | Cons (es1, es2) ->  Cons (substituteESWithAgr es1 realArg formalArg, substituteESWithAgr es2 realArg formalArg)
  | ESOr (pi, es1, es2) ->  ESOr (pi, substituteESWithAgr es1 realArg formalArg, substituteESWithAgr es2 realArg formalArg)
  | Ttimes (esIn, t) -> Ttimes (substituteESWithAgr esIn realArg formalArg, substituteTermWithAgr t realArg formalArg)
  | Kleene esIn -> Kleene (substituteESWithAgr esIn realArg formalArg)
  | Par (es1, es2) ->  Par (substituteESWithAgr es1 realArg formalArg, substituteESWithAgr es2 realArg formalArg)
  ;;





(*To pretty print effects entialments*)


let showEntailmentEff (eff1:effect)( eff2:effect):string = showEffect eff1 ^ " |- "  ^ showEffect eff2;;

(*To pretty print event sequence entailment*)
let showEntailmentES (es1:es) (es2:es):string = showES es1 ^ " |- "  ^ showES es2;;


(*To pretty print entialment rules*)
let showRule (r:rule):string = 
  match r with
    LHSOR -> " [LHSOR] "
  | RHSAND -> " [RHSAND] "
  | RHSOR -> " [RHSOR] "
  | LHSEX -> " [LHSEX] "  
  | RHSEX -> " [RHSEX] " 
  | LHSSUB -> " [LHSSUB] "
  | RHSSUB -> " [RHSSUB] "
  | LHSCASE -> " [LHSCASE] "
  | RHSCASE -> " [RHSCASE] "
  | UNFOLD  -> " [UNFOLD] "
  | DISPROVE -> " [DISPROVE] "
  | FRAME  -> " [FRAME] "
  | REOCCUR -> " [REOCCUR] "

(*To pretty print all the context entailments
let rec showContext (d:context):string = 
  match d with
    [] -> ""
  | (piL, esL, piR, esR)::rest -> (showEntailmentEff (Effect (piL, esL)) (Effect (piR, esR)) )^ ("\n") ^ showContext rest
  ;;
  *)

(*
let rec reverseEs (es:es) : es = 
  match es with 
    Bot -> Bot
  | Emp -> Emp
  | Event _ -> es
  | Cons (es1, es2) -> Cons (reverseEs es2, reverseEs es1)
  | ESOr (es1, es2) -> ESOr (reverseEs es1, reverseEs es2)
  | Ttimes (es1, t) -> Ttimes (reverseEs es1, t)
  | Kleene es1 ->  Kleene (reverseEs es1)
  ;;

let rec reverseEff (eff:effect) : effect = List.map (fun (p,es) ->  (p, reverseEs es) ) eff 
;;

*)
let rec substituteTermWithAgr (t:terms) (realArg:expression) (formalArg: var):terms = 
  match t with 
    Var str -> if String.compare formalArg str == 0 then 
    (
      match realArg with 
      | Value v -> (
        match v with 
        |Integer n -> Number n
        | Variable v -> Var v
        | Bool true -> Number 1
        | Bool false -> Number 0
        | _ -> raise (Foo "substituteTermWithAgr exception1")

        )
      | BinOp (Variable v, Integer n, "+") -> Plus (Var v, Number n)
      | BinOp (Variable v, Integer n, "-") -> Minus (Var v, Number n)
      | _ -> raise (Foo "substituteTermWithAgr exception")
    )
    else Var str 
  | Number n -> Number n
  | Plus (term, n) -> Plus (substituteTermWithAgr term realArg formalArg, n)
  | Minus (term, n) -> Minus (substituteTermWithAgr term realArg formalArg, n)
  ;;




let rec splitDisj (p:pure) (es:es):effect =
  match p with 
    PureOr (p1, p2) -> List.append (splitDisj p1 es)  (splitDisj p2 es ) 
  | _ -> [(p, es)] 
  ;;

let rec splitConj (p:pure) :(pure list) =
  match p with 
    PureAnd (p1, p2) -> List.append (splitConj p1 )  (splitConj p2  ) 
  | _ -> [(p)] 
  ;;

let rec normalPureToDisj (p:pure):pure = 
  let listOfCONJ = splitConj p in 
  let filterList = List.filter (fun p ->
  match p with 
  | TRUE -> false 
  | _ -> true 
    ) listOfCONJ in
  if List.length filterList == 0 then TRUE 
  else List.fold_left (fun acc a -> PureAnd(acc, a)) (List.hd filterList) (List.tl filterList) 
  (*match p with 
    PureAnd (p1, PureOr(pIn1, pIn2)) ->  
      let dealP1 = normalPureToDisj p1 in
      let temp1 = normalPureToDisj (PureAnd(dealP1, pIn1)) in 
      let temp2 = normalPureToDisj (PureAnd(dealP1, pIn2)) in 
      PureOr (temp1 , temp2 )
  | PureAnd (PureOr(pIn1, pIn2), p2) ->  
      let dealP2 = normalPureToDisj p2 in
      let temp1 = normalPureToDisj (PureAnd(dealP2, pIn1)) in 
      let temp2 = normalPureToDisj (PureAnd(dealP2, pIn2)) in 
      PureOr (temp1 , temp2 )
  | Neg pi -> Neg (normalPureToDisj pi)
  | _ -> p
  *)
  ;;

let rec deletePureOrInEff (eff:effect):effect = List.flatten (List.map (fun (pi, es) -> 
  let disjPure = normalPureToDisj pi in
  splitDisj disjPure es ) eff)
  ;;

let rec compareTerm (term1:terms) (term2:terms) : bool = 
  match (term1, term2) with 
    (Var s1, Var s2) -> true
  | (Number n1, Number n2) -> n1 == n2 
  | (Plus (tIn1, num1), Plus (tIn2, num2)) -> compareTerm tIn1 tIn2 && compareTerm num1  num2
  | (Minus (tIn1, num1), Minus (tIn2, num2)) -> compareTerm tIn1 tIn2 && compareTerm num1  num2
  | _ -> false 
  ;;


let rec stricTcompareTerm (term1:terms) (term2:terms) : bool = 
  match (term1, term2) with 
    (Var s1, Var s2) -> String.compare s1 s2 == 0
  | (Number n1, Number n2) -> n1 == n2 
  | (Plus (tIn1, num1), Plus (tIn2, num2)) -> stricTcompareTerm tIn1 tIn2 && stricTcompareTerm num1  num2
  | (Minus (tIn1, num1), Minus (tIn2, num2)) -> stricTcompareTerm tIn1 tIn2 && stricTcompareTerm num1  num2
  | _ -> false 
  ;;

let rec comparePure (pi1:pure) (pi2:pure):bool = 
  match (pi1 , pi2) with 
    (TRUE, TRUE) -> true
  | (FALSE, FALSE) -> true 
  | (Gt (t1, t11), Gt (t2, t22)) -> stricTcompareTerm t1 t2 && stricTcompareTerm t11  t22
  | (Lt (t1, t11), Lt (t2, t22)) -> stricTcompareTerm t1 t2 && stricTcompareTerm t11  t22
  | (GtEq (t1, t11), GtEq (t2, t22)) -> stricTcompareTerm t1 t2 && stricTcompareTerm t11  t22
  | (LtEq (t1, t11), LtEq (t2, t22)) -> stricTcompareTerm t1 t2 && stricTcompareTerm t11  t22
  | (Eq (t1, t11), Eq (t2, t22)) -> stricTcompareTerm t1 t2 && stricTcompareTerm t11  t22
  | (PureOr (p1, p2), PureOr (p3, p4)) ->
      (comparePure p1 p3 && comparePure p2 p4) || (comparePure p1 p4 && comparePure p2 p3)
  | (PureAnd (p1, p2), PureAnd (p3, p4)) ->
      (comparePure p1 p3 && comparePure p2 p4) || (comparePure p1 p4 && comparePure p2 p3)
  | (Neg p1, Neg p2) -> comparePure p1 p2
  | _ -> false
  ;;

let rec getAllPi piIn acc= 
    (match piIn with 
      PureAnd (pi1, pi2) -> append (getAllPi pi1 acc ) (getAllPi pi2 acc )
    | _ -> append acc [piIn]
    )
    ;;

let rec existPi pi li = 
    (match li with 
      [] -> false 
    | x :: xs -> if comparePure pi x then true else existPi pi xs 
    )
    ;;

let rec normalTerms (t:terms):terms  = 
  match t with 
    Minus (Minus(s, Number n1), Number n2) ->  Minus(s, Number (n1 + n2))
  | Minus (Number n1, Number n2) ->  Number (n1- n2) 
  | Plus (Number n1, Number n2) -> Number (n1 + n2)
  | _ -> t 
  ;;

let compareEvent ev1 ev2 : bool=
  match (ev1, ev2) with 
  | (Present (str1, _, _), Present (str2, _, _)) -> if String.compare str1 str2 = 0 then true else false 
  | (Absent str1, Absent str2) -> if String.compare str1 str2 = 0 then true else false 
  | (Any, Any) -> true 
  | _ -> false 
  ;;

let rec acompareTerms t1 t2 : bool =
  match (t1, t2) with 
  | (Var _, Var _) -> true 
  | (Number n1, Number n2) -> n1 = n2 
  | (Plus (t11, t12), Plus (t21, t22)) -> acompareTerms t11 t21 && acompareTerms t12 t22
  | (Minus (t11, t12), Minus (t21, t22)) -> acompareTerms t11 t21 && acompareTerms t12 t22
  | _ -> false 
;;


let rec aCompareES es1 es2 = 
  match (es1, es2) with 
    (Bot, Bot) -> true
  | (Emp, Emp) -> true
  | (Event ev1, Event ev2) -> 
    compareEvent ev1 ev2 
  | (Cons (es1L, es1R), Cons (es2L, es2R)) -> 
    if (aCompareES es1L es2L) == false then false
    else (aCompareES es1R es2R)
  | (Par (es1L, es1R), Par (es2L, es2R)) -> 
    if (aCompareES es1L es2L) == false then false
    else (aCompareES es1R es2R)

  | (ESOr (pi1, es1L, es1R), ESOr (pi2, es2L, es2R)) -> 
     (match (pi1, pi2) with 
      | (None, Some _) 
      | (Some _ , None) -> false 
      | (None, None) -> 
      if ((aCompareES es1L es2L) && (aCompareES es1R es2R)) then true 
      else ((aCompareES es1L es2R) && (aCompareES es1R es2L))
      | (Some pi1', Some pi2') -> 
      if ((comparePure pi1' pi2') &&(aCompareES es1L es2L) && (aCompareES es1R es2R)) then true 
      else ((aCompareES es1L es2R) && (aCompareES es1R es2L))
     )


  | (Kleene esL, Kleene esR) -> aCompareES esL esR
  | (Ttimes (esL, t1), Ttimes (esR, t2)) -> aCompareES esL esR && acompareTerms t1 t2 
  | _ -> false
;;
 



let entailConstrains pi1 pi2 = 

  let sat = not (askZ3 (Neg (PureOr (Neg pi1, pi2)))) in
  (*
  print_string (showPure pi1 ^" -> " ^ showPure pi2 ^" == ");
  print_string (string_of_bool (sat) ^ "\n");
  *)
  sat;;

let rec normalPure (pi:pure):pure = 
  let allPi = getAllPi pi [] in
  let rec clear_Pi pi li = 
    (match li with 
      [] -> [pi]
    | x :: xs -> if existPi pi li then clear_Pi x xs else append [pi] (clear_Pi x xs)
    )in 
  let finalPi = clear_Pi TRUE allPi in
  let rec connectPi li acc = 
    (match li with 
      [] -> acc 
    | x :: xs -> if entailConstrains TRUE x then (connectPi xs acc) else PureAnd (x, (connectPi xs acc)) 
    ) in 
  let filte_true = List.filter (fun ele-> not (comparePure ele TRUE)  ) finalPi in 
  if length filte_true == 0 then  TRUE
  else connectPi (tl filte_true) (hd filte_true)
  ;;



