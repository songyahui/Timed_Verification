open String
open List
open Ast
open Printf
open Parser
open Lexer
open Askz3
open Pretty
open Int32



(*
ocamlc -o trs  Tree.ml  Rewriting.ml
*)

(*----------------------------------------------------
------------------Utility Functions------------------
----------------------------------------------------*)
exception Foo of string

module CS = Set.Make(Int32) (*context set*)

type ctxSet = (CS.t * CS.t) list



(*used to generate the free veriables, for subsititution*)
let counter: int ref = ref 0;;

let globelVar : string list ref = ref [];;

let initialise () = 
  let _ = globelVar := [] in 
  let _ = counter :=  0 in 
  ()
;;

let getAfreeVar () :string  =

    let x = "t"^string_of_int (!counter) in 
    let _ = counter := !counter + 1 in 
    let _ = globelVar:=x :: !globelVar in  
    x 
;;

let rec compareEff eff1 eff2 =
  match (eff1, eff2) with
  | ([(FALSE, _ )], [(FALSE, _)]) -> true 
  | ([(FALSE, _ )], [(_, Bot )]) -> true 
  | ([(_, Bot)], [(FALSE, _ )]) -> true 
  | ([(_, Bot )], [(_, Bot)]) -> true 
  | ( [(pi1, es1)], [ (pi2, es2 )]) -> aCompareES es1 es2
  (*| ( (eff11, eff12),  (eff21, eff22)) -> 
      let one =  (compareEff eff11  eff21) && (compareEff eff12  eff22) in
      let two =  (compareEff eff11  eff22) && (compareEff eff12  eff21 ) in
      one || two*)
  | _ -> false
  ;;

let rec concertive (es:es) (t:int): es = 
  if t ==0 then Emp 
  else Cons (es, concertive es (t -1))
  ;;

let rec normalES (es:es) (pi:pure) : es = 
  match es with
    Bot -> es
  | Emp -> es
  | Event _ -> es
  | Par (Emp, es2) -> normalES es2 pi
  | Par (es1, Emp) -> normalES es1 pi
  | Par (Bot, es2) -> Bot
  | Par (es1, Bot) -> Bot
  | Par (es1, es2) -> Par (normalES es1 pi, normalES es2 pi)
  | Guard (pi1) -> Guard (pi1) 
  | Cons (Cons (esIn1, esIn2), es2)-> normalES (Cons (esIn1, Cons (esIn2, es2))) pi 
  | Cons (es1, es2) -> 
      let normalES1 = normalES es1 pi  in
      let normalES2 = normalES es2 pi  in
      (match (normalES1, normalES2) with 
        (Emp, _) -> normalES2 
      | (_, Emp) -> normalES1
      | (Bot, _) -> Bot
      | (_, Bot) -> Bot

      | (Kleene (esIn1), Kleene (esIn2)) -> 
          if aCompareES esIn1 esIn2 == true then normalES2
          else Cons (normalES1, normalES2)
      | (Kleene (esIn1), Cons(Kleene (esIn2), es2)) -> 
          if aCompareES esIn1 esIn2 == true then normalES2
          else Cons (normalES1, normalES2) 

      | (normal_es1, normal_es2) -> 

        Cons (normal_es1, normal_es2)
        
      )

	| ESOr (es1, es2) -> 
      (match (normalES es1 pi , normalES es2 pi ) with 
        (Bot, Bot) -> Bot
      | (Bot, norml_es2) -> norml_es2
      | (norml_es1, Bot) -> norml_es1
      | (ESOr(es1In, es2In), norml_es2 ) ->
        if aCompareES norml_es2 es1In || aCompareES norml_es2 es2In then ESOr(es1In, es2In)
        else ESOr (ESOr(es1In, es2In), norml_es2 )
      | (norml_es2, ESOr(es1In, es2In) ) ->
        if aCompareES norml_es2 es1In || aCompareES norml_es2 es2In then ESOr(es1In, es2In)
        else ESOr (norml_es2, ESOr(es1In, es2In))
      | (Emp, Kleene norml_es2) ->  Kleene norml_es2
      | (Kleene norml_es2, Emp) ->  Kleene norml_es2

      | (norml_es1, norml_es2) -> 
        if aCompareES  norml_es1 norml_es2 == true then norml_es1
        else 
        (match (norml_es1, norml_es2) with
          (norml_es1, Kleene norml_es2) ->  
          if aCompareES norml_es1 norml_es2 == true then Kleene norml_es2
          else ESOr (norml_es1, Kleene norml_es2)
        | (Kleene norml_es2, norml_es1) ->  
          if aCompareES norml_es1 norml_es2 == true then Kleene norml_es2
          else ESOr (Kleene norml_es2, norml_es1)
        |  _-> ESOr (norml_es1, norml_es2)
        )
      ;)

  | Ttimes (Bot, _) -> Bot        
  | Ttimes (es1, terms) -> 
      let t = normalTerms terms in 
      let normalInside = normalES es1 pi  in 
      Ttimes (normalInside, t) 
  | Kleene es1 -> 
      let normalInside = normalES es1 pi  in 
      (match normalInside with
        Emp -> Emp
      | Kleene esIn1 ->  Kleene (normalES esIn1 pi )
      | ESOr(Emp, aa) -> Kleene aa 
      | _ ->  Kleene normalInside)

;;

let rec normalESUnifyTime (es:es) (pi:pure) : (es * pure) = 
  let es' = normalES es pi in 
  match es' with
  | Ttimes (Ttimes (es1, t1) , t2 ) -> (Ttimes (es1, t1), Eq(t1, t2)) 
  | Cons (es1, es2) -> 
    let (es1', pi1) =   normalESUnifyTime es1 pi in   
    let (es2', pi2) =   normalESUnifyTime es2 pi in   
    (Cons(es1', es2'), PureAnd(PureAnd(pi1, pi2), pi))
  | ESOr (es1, es2) -> 
    let (es1', pi1) =   normalESUnifyTime es1 pi in   
    let (es2', pi2) =   normalESUnifyTime es2 pi in   
    (ESOr(es1', es2'), PureAnd(PureAnd(pi1, pi2), pi))
  | Kleene (es1) ->
    let (es1', pi1) =   normalESUnifyTime es1 pi in   
    (Kleene (es1'),  pi1)
  | _ -> (es', TRUE)
  ;;

let globalVToPure (v:globalV) : pure =
  let pureList = List.map (fun (str, n) -> Eq(Var str, Number n)) v in 
  let rec helper li: pure = 
    match li with 
    | [] -> TRUE 
    | p :: rest -> PureAnd (p, helper rest)
  in 
  helper pureList
;;


let rec nullable (pi :pure) (es:es) : bool=
  match es with
    Bot -> false 
  | Emp -> true
  | Event _ -> false 
  | Cons (es1 , es2) -> (nullable pi es1) && (nullable pi es2)
	| ESOr (es1 , es2) -> (nullable pi es1) || (nullable pi es2)
  | Ttimes (es1, t) ->  askZ3 (PureAnd(pi, Eq(t, Number 0))) 
  | Kleene es1 -> true
  | Par (es1 , es2) -> (nullable pi es1) && (nullable pi es2)
  | Guard (pi1) -> false 
;;

let nullableEff (eff:effect)  : bool = 
  List.fold_left (fun acc (pi, es) -> acc || (nullable pi es)) false eff;;

(*assert (nullable (Eq (Var "t", Number 0)) (Ttimes (Emp, Var "t")) == true);;
assert (nullable (Eq (Var "t", Number 1)) (Ttimes (Emp, Var "t")) == false);;
*)

let rec fst (pi :pure) (es:es) : head list = 
  match es with
    Bot -> []
  | Emp -> []
  | Event ev ->  [Instant ev]
  | Ttimes (es1, t) -> 
    let es1' =normalES es1 pi in  
    (match  es1' with 
    | Emp -> [T t]
    | Event (ev) ->  [Ev(ev, t)]
    | _ -> fst pi es1')
  | Cons (es1 , es2) ->  if nullable pi es1 then append (fst pi es1) (fst pi es2) else fst pi es1
  | ESOr (es1, es2) -> append (fst pi es1 ) (fst pi es2)

  | Par (es1, es2) -> append (fst pi es1 ) (fst pi es2 )
  | Kleene es1 -> fst pi es1
  | Guard (pi1) -> [Tauh pi1]

;;

let fstEff (eff:effect)  : head list = List.flatten (List.map (fun (pi, es) -> fst pi es) eff);; 

let appendEff_ES eff es: effect = List.map (fun (pi, es1) -> (pi, Cons (es1, es))) eff;;  

let entailEvent ev1 ev2 : bool =
  match (ev1, ev2) with 
  | (_, Any) -> true 
  | (Present (str1, _, _), Present (str2, _, _)) -> String.compare str1 str2 == 0 
  | (Present (str1, _, _), Absent str2) -> String.compare str1 str2 != 0 
  | (Absent str1, Absent str2) ->  String.compare str1 str2 == 0
  | _ -> false 
;;



let rec derivitive (pi :pure) (es:es) (f:head) : (es * pure) =
  match es with 
  | Bot -> (Bot, TRUE)
  | Emp -> (Bot, TRUE)
  | Cons (es1 , es2) ->  
      let (es1_der, side1) = derivitive pi es1 f in 
      let es1' = Cons (es1_der, es2) in 
      let (es2_der, side2) = derivitive pi es2 f in    
      if nullable pi es1
        then (ESOr (es1', es2_der), PureAnd(side1, side2))  
        else (es1', side1)



  | ESOr (es1, es2) -> 
      let (es1_der, side1) = derivitive pi es1 f in 
      let (es2_der, side2) = derivitive pi es2 f in
      (ESOr (es1_der, es2_der), PureAnd(side1, side2)) 

  | Kleene es1 -> 
      let (es1_der, side1) = derivitive pi es1 f in 
      (Cons (es1_der, es), side1)
  | Par (es1, es2) ->
      let helper esIn = 
        let (der, side) = derivitive pi esIn f in 
        match normalES der pi with 
        | Bot -> (esIn, Ast.TRUE)
        | _ -> (der, side)
      in 
      let (es1', side1) = helper es1 in 
      let (es2', side2) = helper es2 in 
      (Par (es1', es2'), PureAnd(side1, side2))
  | Guard (pi1) -> 
    (match f with 
    | Tauh pi2 -> if entailConstrains pi2 pi1 then (Emp, TRUE) else (es, TRUE)
    | _ -> (es, TRUE)
    )
      
  | Event (Any) -> (Emp, TRUE)

  | Event ev1 -> 
		(match f with 
		| T  t -> (Bot, TRUE)
    | Tauh pi1 ->  (match ev1 with 
                  | Tau pi2 -> if entailConstrains pi1 pi2 then (Emp, TRUE) else (Bot, TRUE)
                  | _ -> (Bot, TRUE)
                  )
		| Ev (ev, t) -> (Bot, TRUE)
		| Instant ev -> if entailEvent ev ev1 then (Emp, TRUE) else (Bot, TRUE)
		)
	| Ttimes (Emp, tIn) -> 
		(match f with 
		| T  t -> (Emp,  Eq(t , tIn))
		| Ev (ev, t) -> (Bot, TRUE)
    | Tauh pi1 -> (Bot, TRUE)
		| Instant ev -> (Bot, TRUE)
		)
	| Ttimes (Event ev1, tIn) -> 
		(match f with 
		| T  t ->  let t_new = getAfreeVar () in 
      (Ttimes (Event ev1, Var t_new), PureAnd(Eq(Plus (t,Var t_new) , tIn), GtEq (Var t_new, Number 0)))
		| Ev (ev, t) ->  if entailEvent ev ev1 then (Emp, Eq(tIn, t)) else (Bot, TRUE)
    | Tauh pi1 -> (Bot, TRUE)

		| Instant ev ->  if entailEvent ev ev1 then (Ttimes (Emp, tIn), TRUE) else (Bot, TRUE)
		)
	
	| Ttimes (es1, tIn) -> 
		(match f with 
		| T  t ->  let t_new = getAfreeVar () in 
      (Ttimes (es1, Var t_new), PureAnd(Eq(Plus (t,Var t_new) , tIn), GtEq (Var t_new, Number 0)))
		| Ev (ev, t) ->  
		  let (es1_der, side1) = derivitive pi es1 f in 
      let t_new = getAfreeVar () in 
      let p_new = PureAnd (side1, PureAnd(Eq(Plus (t,Var t_new) , tIn), GtEq (Var t_new, Number 0))) in 
      (Ttimes (es1_der, Var t_new), p_new)
    | Tauh pi1 -> (Bot, TRUE)


		
		| Instant ev ->  let (es1_der, side1) = derivitive pi es1 f in 
      (Ttimes (es1_der, tIn), pi)

		)

;;

(*
let rec derivitive (pi :pure) (es:es) (f:head) (v:globalV): (es * pure) =
  match f with 
  | T  t ->
    (match es with 
      Bot -> (Bot, TRUE)
    | Emp -> (Bot, TRUE)
    | Event (Any) -> (Emp, TRUE)
    | Event ev -> (Bot, TRUE)
    | Ttimes (Emp, tIn) -> (Emp,  Eq(t , tIn))
    | Ttimes (es1, tIn) -> 
      let t_new = getAfreeVar () in 
      (Ttimes (es1, Var t_new), PureAnd(Eq(Plus (t,Var t_new) , tIn), GtEq (Var t_new, Number 0)))

    | Cons (es1 , es2) ->  
      let (es1_der, side1) = derivitive pi es1 f in 
      let es1' = Cons (es1_der, es2) in 
      let (es2_der, side2) = derivitive pi es2 f in    
      if nullable pi es1 
        then (ESOr (es1', es2_der), PureAnd(side1, side2))  
        else (es1', side1)

    | ESOr (es1, es2) -> 
      let (es1_der, side1) = derivitive pi es1 f in 
      let (es2_der, side2) = derivitive pi es2 f in
      (ESOr (es1_der, es2_der), PureAnd(side1, side2)) 

    | Kleene es1 -> 
      let (es1_der, side1) = derivitive pi es1 f in 
      (Cons (es1_der, es), side1)
    | Par (es1, es2) ->
      let helper esIn = 
        let (der, side) = derivitive pi esIn f in 
        match normalES der pi with 
        | Bot -> derivitive pi esIn (T t) v
        | _ -> (der, side)
      in 
      let (es1', side1) = helper es1 in 
      let (es2', side2) = helper es2 in 
      (Par (es1', es2'), PureAnd(side1, side2))
    | Guard (pi1, es1) -> 
      if askZ3 (PureAnd(pi1, globalVToPure v)) then derivitive pi es1 f v 
      else (es, TRUE)
      
    
    )
  | Ev (ev, t) -> 
    (match es with 
      Bot -> (Bot, TRUE)
    | Emp -> (Bot, TRUE)
    | Event ev1 -> if entailEvent ev ev1 then (Emp, TRUE) else (Bot, TRUE)
    | Ttimes (Event ev1, tIn) -> 
      if entailEvent ev ev1 then (Emp, Eq(tIn, t)) else (Bot, TRUE)

    | Ttimes (es1, tIn) -> 

      let (es1_der, side1) = derivitive pi es1 f in 
      let t_new = getAfreeVar () in 
      let p_new = PureAnd (side1, PureAnd(Eq(Plus (t,Var t_new) , tIn), GtEq (Var t_new, Number 0))) in 
      (Ttimes (es1_der, Var t_new), p_new)

    | Cons (es1 , es2) ->  
      let (es1_der, side1) = derivitive pi es1 f in 
      let es1' = Cons (es1_der, es2) in 
      let (es2_der, side2) = derivitive pi es2 f in    
      if nullable pi es1 
        then (ESOr (es1', es2_der), PureAnd(side1, side2))  
        else (es1', side1)

    | ESOr (es1, es2) -> 
      let (es1_der, side1) = derivitive pi es1 f in 
      let (es2_der, side2) = derivitive pi es2 f in
      (ESOr (es1_der, es2_der), PureAnd(side1, side2)) 

    | Kleene es1 -> 
      let (es1_der, side1) = derivitive pi es1 f in 
      (Cons (es1_der, es), side1)

    | Par (es1, es2) ->
      let helper esIn = 
        let (der, side) = derivitive pi esIn f in 
        match normalES der pi with 
        | Bot -> derivitive pi esIn (T t) v
        | _ -> (der, side)
      in 
      let (es1', side1) = helper es1 in 
      let (es2', side2) = helper es2 in 
      (Par (es1', es2'), PureAnd(side1, side2))
    | Guard (pi1, es1) -> 
      if askZ3 (PureAnd(pi1, globalVToPure v)) then derivitive pi es1 f v 
      else (es, TRUE)
    
    )

  | Instant ev -> 
    (match es with 
      Bot -> (Bot, TRUE)
    | Emp -> (Bot, TRUE)
    | Event ev1 -> if entailEvent ev ev1 then (Emp, TRUE) else (Bot, TRUE)
    | Ttimes (es1, tIn) -> 

      let (es1_der, side1) = derivitive pi es1 f in 
      (Ttimes (es1_der, tIn), pi)

    | Cons (es1 , es2) ->  
      let (es1_der, side1) = derivitive pi es1 f in 
      let es1' = Cons (es1_der, es2) in 
      let (es2_der, side2) = derivitive pi es2 f in    
      if nullable pi es1 
        then (ESOr (es1', es2_der), PureAnd(side1, side2))  
        else (es1', side1)

    | ESOr (es1, es2) -> 
      let (es1_der, side1) = derivitive pi es1 f in 
      let (es2_der, side2) = derivitive pi es2 f in
      (ESOr (es1_der, es2_der), PureAnd(side1, side2)) 

    | Kleene es1 -> 
      let (es1_der, side1) = derivitive pi es1 f in 
      (Cons (es1_der, es), side1)
    | Par (es1, es2) ->
      let helper esIn = 
        let (der, side) = derivitive pi esIn f in 
        match normalES der pi with 
        | Bot -> (esIn, Ast.TRUE)
        | _ -> (der, side)
      in 
      let (es1', side1) = helper es1 in 
      let (es2', side2) = helper es2 in 
      (Par (es1', es2'), PureAnd(side1, side2))
    | Guard (pi1, es1) -> 
      if askZ3 (PureAnd(pi1, globalVToPure v)) then derivitive pi es1 f v 
      else (es, TRUE)
    )



  
;;
*)





let rec normalEffect (eff:effect) :effect =
  let noPureOr:effect  = deletePureOrInEff eff in 
  let final = List.filter (fun (p, es) -> 
  match (p,  es ) with 
  | (_,  Bot) -> false 
  | (Ast.FALSE,  _) -> false  
  | _ -> true 
  ) (List.map (fun (p, es) -> 
      let (es', pi') = normalESUnifyTime es p in 
      ( pi', es')) noPureOr) in 
  if List.length final == 0 then [(FALSE, Bot)]
  else final 
  ;;



let reoccur lhs rhs delta : bool =  
  List.fold_left (fun acc (lhspy, rhshy) -> 
  let result = aCompareES lhs lhspy && aCompareES rhs rhshy in 
  acc || result
  ) false delta 
  ;;

(*
let valuationLHS: globalV ref=  ref [] ;;
let valuationRHS: globalV ref=  ref [] ;;
*)

let rec containment (side:pure) (effL:effect) (effR:effect) (delta:hypotheses) : (binary_tree * bool) = 
  let normalFormL = normalEffect effL in 
  let normalFormR = normalEffect effR in
  let showEntail  =  showEntailmentEff normalFormL normalFormR (*^ "  ***> " ^ (showPure (normalPure side)) *) in
  (*  print_string (showEntail^"\n");*)
  if nullableEff  normalFormL  = true &&  (nullableEff normalFormR  = false) then   (Node (showEntail ^ showRule DISPROVE,[] ), false)

  else 
    let (finalTress, finalRe) = List.fold_left (fun (accT, accR) (pL, esL) -> 
      let (subtree, re) = List.fold_left (fun (accInT, accInR) (pR, esR) -> 
        let (subtreeIn, reIn) = 
          if reoccur (esL) (esR) delta then 
            if comparePure pR TRUE then (Node (showEntail ^ showRule REOCCUR,[] ), true)
            else 
              if entailConstrains (PureAnd (pL, side)) pR then (Node (showEntail ^ showRule REOCCUR,[] ), true)
              else (Node (showEntail ^ " [PURE ER] ", []), false)
             
          else 
            let fstSet = fst pL esL  in
            if List.length (fstSet) == 0 then 
              if comparePure pR TRUE then (Node (showEntail ^ showRule REOCCUR,[] ), true)
              else 
                if entailConstrains (PureAnd (pL, side)) pR then (Node (showEntail ^ " [NO FST]", [] ), true)
                else (Node (showEntail ^ " [PURE ER] ", []), false)
            else 
            let (subtrees, re) = List.fold_left (fun (accT, accR) f -> 
            let (derL, sideL) = derivitive pL esL f  in 
            let (derR, sideR) = derivitive pR esR f  in 
            let side' = PureAnd(side, PureAnd(sideL, sideR)) in 
            let (subtree, result) = containment side' [(pL, derL)] [(pR, derR)] ((esL, esR) :: delta) in 
            (List.append accT [subtree], accR && result) 
            ) ([], true) fstSet in 
            (Node (showEntail ^ showRule UNFOLD, subtrees ), re)

          in 
        (subtreeIn::accInT, reIn || accInR)  
      ) ([], false) normalFormR in 
      (List.append subtree accT, re && accR)

    ) ([], true) normalFormL in 
    if List.length (finalTress) == 1 then 
      (List.hd finalTress, finalRe)
    else 
      (Node (showEntail ^ " [SPLITLHS] ", finalTress), finalRe)


  

  

  ;;

let rec reNameTerms t str: terms = 
match t with
  Var name -> 
    if (String.compare name "n" == 0) then Var name
    else 
    Var (str^name)
| Number n -> t
| Plus (t1, t2) -> Plus (reNameTerms t1 str, reNameTerms t2 str)
| Minus (t1, t2) -> Minus (reNameTerms t1 str, reNameTerms t2 str)

;; 


let rec reNamePure p str : pure =
  match p with
| Gt (t1, t2) -> Gt (reNameTerms t1 str, reNameTerms t2 str)
| Lt (t1, t2) ->  Lt (reNameTerms t1 str, reNameTerms t2 str)
| GtEq (t1, t2) ->  GtEq (reNameTerms t1 str, reNameTerms t2 str)
| LtEq (t1, t2) ->  LtEq (reNameTerms t1 str, reNameTerms t2 str)
| Eq (t1, t2) ->  Eq (reNameTerms t1 str, reNameTerms t2 str)
| PureOr (p1, p2) -> PureOr (reNamePure p1 str, reNamePure p2 str)
| PureAnd (p1, p2) -> PureAnd (reNamePure p1 str, reNamePure p2 str)
| Neg p1 -> Neg (reNamePure p1 str)
| _ -> p 
;; 

let rec reNameEs es str =
  match es with
| Cons (es1, es2) -> Cons (reNameEs es1 str, reNameEs es2 str)

| ESOr (es1, es2) -> ESOr (reNameEs es1 str, reNameEs es2 str)
| Ttimes (es1, t) -> Ttimes (reNameEs es1 str, reNameTerms t str) 
| Kleene es1 -> Kleene (reNameEs es1 str )
| Par (es1, es2) -> Par (reNameEs es1 str, reNameEs es2 str)
| _ -> es 
;;

let reNameEffect (eff:effect) str: effect = 
  List.map (fun (p, es) -> (reNamePure p str, reNameEs es str )) eff
;;

let printReportHelper lhs rhs : (binary_tree * bool) = 
  
  (*
  let normalFormL = normalEffect lhs in 
  let normalFormR = normalEffect rhs in
  let showEntail  =  showEntailmentEff normalFormL normalFormR (*^ "  ***> " ^ (showPure (normalPure side)) *) in
  print_string (showEntail ^"\n"); 

  Leaf , true*)
	containment TRUE (normalEffect (reNameEffect lhs "l") ) (reNameEffect rhs "r") []   
  ;;



let printReport lhs rhs :string =
  let _ = initialise () in 
  let startTimeStamp = Sys.time() in
  let (tree, re) =  printReportHelper lhs rhs  in
  let verification_time = "[Verification Time: " ^ string_of_float ((Sys.time() -. startTimeStamp) *. 1000.0) ^ " ms]\n" in
  let result = printTree ~line_prefix:"* " ~get_name ~get_children tree in
  let buffur = ( "===================================="^"\n[Result] " ^(if re then "Succeed\n" else "Fail\n") ^verification_time^" \n\n"^ result)
  in buffur
  ;;
