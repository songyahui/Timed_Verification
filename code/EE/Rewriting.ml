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

let optionPureAnd pi1 pi2 : pure option  = 
  match (pi1, pi2) with 
  | (None, None) -> None 
  | (Some pi1', Some pi2') -> Some (PureAnd (pi1', pi2'))
  | (None, _) -> pi2
  | ( _ , None) -> pi1
;;

let optionPureAndHalf pi1 pi2 : pure   = 
  match pi1 with 
  | None -> pi2 
  | Some pi1' ->  PureAnd (pi1', pi2)
;;

let rec normalESUnifyTime (es:es) (pi:pure) : (es * pure option ) = 
  let es' = normalES es pi in 
  match es' with
  | Ttimes (Ttimes (es1, t1) , t2 ) -> 
    (*print_string (showES es ^"\n"); *)
    (Ttimes (es1, t1), Some (Eq(t1, t2))) 
  | Cons (es1, es2) -> 
    let (es1', pi1) =   normalESUnifyTime es1 pi in   
    let (es2', pi2) =   normalESUnifyTime es2 pi in   
    (Cons(es1', es2'), optionPureAnd pi1 pi2)
  | ESOr (es1, es2) -> 
    let (es1', pi1) =   normalESUnifyTime es1 pi in   
    let (es2', pi2) =   normalESUnifyTime es2 pi in   
    (ESOr(es1', es2'), optionPureAnd pi1 pi2)
  | Kleene (es1) ->
    let (es1', pi1) =   normalESUnifyTime es1 pi in   
    (Kleene (es1'),  pi1)
  | _ -> (es', None)
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
  | Guard (pi1) -> [Instant(Tau pi1); Instant (Tau (Neg pi1))]

;;

let fstEff (eff:effect)  : head list = List.flatten (List.map (fun (pi, es) -> fst pi es) eff);; 

let appendEff_ES eff es: effect = List.map (fun (pi, es1) -> (pi, Cons (es1, es))) eff;;  

let entailEvent ev1 ev2 : bool =
  match (ev1, ev2) with 
  | (_, Any) -> true 
  | (Tau pi1, Tau pi2) -> entailConstrains pi1 pi2
  | (Present (str1, _, _), Present (str2, _, _)) -> String.compare str1 str2 == 0 
  | (Present (str1, _, _), Absent str2) -> String.compare str1 str2 != 0 
  | (Absent str1, Absent str2) ->  String.compare str1 str2 == 0
  | _ -> false 
;;



let rec derivitive (pi :pure) (es:es) (f:head) : (es * pure option)  =
  match es with 
  | Bot -> (Bot, None)
  | Emp -> (Bot, None)
  | Cons (es1 , es2) ->  
      let (es1_der, side1) = derivitive pi es1 f in 
      let es1' = Cons (es1_der, es2) in 
      let (es2_der, side2) = derivitive pi es2 f in    
      if nullable pi es1
        then (ESOr (es1', es2_der), optionPureAnd side1 side2)  
        else (es1', side1)


        (*
        let t_new = getAfreeVar () in 
          (ESOr (es1', Cons(Ttimes(es1, Var t_new), es2_der)), Some (optionPureAndHalf (optionPureAnd side1 side2) (Ast.Eq(Var t_new, Number 0)))  )
       
        *)



  | ESOr (es1, es2) -> 
      let (es1_der, side1) = derivitive pi es1 f in 
      let (es2_der, side2) = derivitive pi es2 f in
      (ESOr (es1_der, es2_der), optionPureAnd side1 side2) 

  | Kleene es1 -> 
      let (es1_der, side1) = derivitive pi es1 f in 
      (Cons (es1_der, es), side1)
  | Par (es1, es2) ->
      let helper esIn = 
        let (der, side) = derivitive pi esIn f in 
        match normalES der pi with 
        | Bot -> (esIn, None)
        | _ -> (der, side)
      in 
      let (es1', side1) = helper es1 in 
      let (es2', side2) = helper es2 in 
      (Par (es1', es2'), optionPureAnd side1 side2)
  | Guard (pi1) -> 
    (match f with 
    | Instant (Tau pi2) -> if entailConstrains pi2 pi1 then (Emp, None) else (es, None)
    | _ -> (es, None)
    )
      
  | Event (Any) -> (Emp, None)

  | Event ev1 -> 
		(match f with 
		| T  t -> (Bot, None)
		| Ev (ev, t) -> (Bot, None)
		| Instant ev -> if entailEvent ev ev1 then (Emp, None) else (Bot, None)
		)
  | Ttimes (Ttimes (es1, t1) , t2 ) -> 
    let (es1_der, side1) = derivitive pi (Ttimes (es1, t1)) f in 
    (es1_der, Some (optionPureAndHalf side1 (Eq(t1, t2))))

	| Ttimes (Emp, tIn) -> 
		(match f with 
		| T  t -> (Emp,  Some (Eq(t , tIn)))
		| Ev (ev, t) -> (Bot, None)
		| Instant ev -> (Bot, None)
		)
	| Ttimes (Event ev1, tIn) -> 
		(match f with 
		| T  t ->  let t_new = getAfreeVar () in 
      (Ttimes (Event ev1, Var t_new), Some (PureAnd(Eq(Plus (t,Var t_new) , tIn), GtEq (Var t_new, Number 0))))
		| Ev (ev, t) ->  if entailEvent ev ev1 then (Emp,Some ( Eq(tIn, t))) else (Bot, None)

		| Instant ev ->  if entailEvent ev ev1 then (Ttimes (Emp, tIn), None) else (Bot, None)
		)
	
	| Ttimes (es1, tIn) -> 
		(match f with 
		| T  t ->  let t_new = getAfreeVar () in 
      (Ttimes (es1, Var t_new), Some (PureAnd(Eq(Plus (t,Var t_new) , tIn), GtEq (Var t_new, Number 0))))
		| Ev (ev, t) ->  
		  let (es1_der, side1) = derivitive pi es1 (Instant ev) in 
      (match normalES es1_der pi with 
      | Emp -> (Emp, side1)
      | _ -> 
        let t_new = getAfreeVar () in 
        let p_new = optionPureAndHalf side1 (PureAnd(Eq(Plus (t,Var t_new) , tIn), GtEq (Var t_new, Number 0))) in 
        (Ttimes (es1_der, Var t_new), Some p_new)
      )
		
		| Instant ev ->  let (es1_der, side1) = derivitive pi es1 f in 
        match normalES es1_der pi with 
        | Bot -> (Bot, Some (Eq (tIn, Number 0)))
        | _ -> 
      (Ttimes (es1_der, tIn), side1)

		)

;;



let rec normalEffect (eff:effect) :effect =
  let noPureOr:effect  = (* deletePureOrInEff *) eff in 
  let final = List.filter (fun (p, es) -> 
  match (p,  es ) with 
  | (_,  Bot) -> false 
  | (Ast.FALSE,  _) -> false  
  | _ -> true 
  ) (List.map (fun (p, es) -> 
      (*let (es', pi') = normalESUnifyTime es p in 
      (  normalPure    (optionPureAndHalf  pi' p), es')) noPureOr) in 
      *)
      normalPure p, normalES es p) noPureOr )in 
  if List.length final == 0 then (
    (*print_string (showEffect eff ^ "\n");raise (Foo ("lallalal")); *)
    [(FALSE, Bot)]
  )
  else final 
  ;;



let reoccur lhs rhs delta : bool =  

  let rec helper li = 
    match li with
    | [] -> false 
    | (lhspy, rhshy):: rest -> 
      if aCompareES lhs lhspy then 
        if aCompareES rhs rhshy 
        then true 
        else helper rest 
      else helper rest
  in helper delta


  ;;

let delta : hypotheses ref = ref []



let rec containment (side:pure) (effL:effect) (effR:effect) : (binary_tree * bool) = 
  let normalFormL = normalEffect effL in 
  let normalFormR = normalEffect effR in
  let showEntail  =  showEntailmentEff normalFormL normalFormR (*^ "  ***> " ^ (showPure (normalPure side))*)  in
  (*  print_string (showEntail^"\n");*)
  if nullableEff  normalFormL  = true &&  (nullableEff normalFormR  = false) then   
    (Node (showEntail ^ showRule DISPROVE,[] ), false)

  else 
    let (finalTress, finalRe) = List.fold_left (fun (accT, accR) (pL, esL) -> 
      let (subtree, re) = List.fold_left (fun (accInT, accInR) (pR, esR) -> 
        let (subtreeIn, reIn) = 
          if askZ3 pL == false then (Node (showEntail ^ " [PURE ER LHS] ", []), false) else 

          if reoccur (esL) (esR) !delta then 
            (Node (showEntail ^ showRule REOCCUR,[] ), true)
            (*if comparePure pR TRUE then (Node (showEntail ^ showRule REOCCUR,[] ), true)
            else   
              if entailConstrains (PureAnd (pL, side)) pR then (Node (showEntail ^ showRule REOCCUR,[] ), true)
              else (Node (showEntail ^ " [PURE ER2] ", []), false)
              *)
             
          else 
            let fstSet = fst pL esL  in
            if List.length (fstSet) == 0 then 
              if comparePure pR TRUE then (Node (showEntail ^ " [NO FST1]",[] ), true)
              else 
                if entailConstrains (PureAnd (pL, side)) pR then (Node (showEntail ^ " [NO FST2]", [] ), true)
                else (Node (showEntail ^ " [PURE ER3] ", []), false)
            else 
            let (subtrees, re) = List.fold_left (fun (accT, accR) f -> 
            let (derL, sideL) = derivitive pL esL f  in 
            let (derR, sideR) = derivitive pR esR f  in 
            let side' = optionPureAndHalf (optionPureAnd sideL sideR)  side  in 
            let _ = delta := ((esL, esR) :: !delta) in 
            let (subtree, result) = containment side' [(pL, derL)] [(pR, derR)]  in 
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
    if (String.compare name "n" == 0 || String.compare name "d1" == 0 || String.compare name "d2" == 0) then Var name
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



let rec gatherTTermsFromES (es:es) : terms list = 
  match es with
    Bot -> [] 
  | Emp -> []
  | Event _ -> [] 
  | Cons (es1 , es2) -> List.append (gatherTTermsFromES es1) (gatherTTermsFromES es2)
	| ESOr (es1 , es2) -> List.append (gatherTTermsFromES es1) (gatherTTermsFromES es2)
  | Ttimes (es1, t) ->  [t]
  | Kleene es1 -> (gatherTTermsFromES es1)
  | Par (es1 , es2) -> List.append (gatherTTermsFromES es1) (gatherTTermsFromES es2)
  | Guard (pi1) -> [] 
  ;;

let gatherTTerms (eff:effect) : terms list =
  List.flatten (List.map (fun (_, es) -> 
    gatherTTermsFromES es 
  ) eff) ;;

let addPureToEff p eff = List.map (fun (pi, es) ->(PureAnd (pi, p), es)) eff ;;

let printReportHelper lhs rhs : (binary_tree * bool) = 
  
  (*
  let normalFormL = normalEffect lhs in 
  let normalFormR = normalEffect rhs in
  let showEntail  =  showEntailmentEff normalFormL normalFormR (*^ "  ***> " ^ (showPure (normalPure side)) *) in
  print_string (showEntail ^"\n"); 
    (Leaf , true)


  *)
  let a : hypotheses ref = ref [] in 

  let _ = (delta: hypotheses ref) := !a in 
  let renamedLHS = reNameEffect lhs "l"  in  
  let renamedRHS = reNameEffect rhs "r"  in 
  let alltheTVar = (gatherTTerms renamedRHS) in 


  let side = if List.length alltheTVar == 0 then Ast.TRUE else
    List.fold_left (fun acc a -> Ast.PureAnd (acc , Ast.GtEq( a, Number 0))) (Ast.GtEq(List.hd alltheTVar, Number 0)) (List.tl alltheTVar) in 
  containment (normalPure side) (renamedLHS) (renamedRHS)    

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

(* *********************************************************************)
(* *********************************************************************)
(* *********************************************************************)
(* ****************  REWRITING THE CONCRETE SYSTEM   *******************)
(* *********************************************************************)
(* *********************************************************************)
(* *********************************************************************)


let valuationTRS: globalV ref=  ref [] ;;


let globalVToPure (v:globalV) : pure =
  let pureList = List.map (fun (str, n) -> Eq(Var str, Number n)) v in 
  let rec helper li: pure = 
    match li with 
    | [] -> TRUE 
    | p :: rest -> PureAnd (p, helper rest)
  in 
  helper pureList
;;

let rec updateOneValue (str, terms) screenshot: globalV = 
  match screenshot with 
  | [] -> raise (Foo (str ^" does not exist in current V "))
  | (s, t) :: rest -> if String.compare s str == 0 then (str, terms):: rest 
    else (s, t) :: (updateOneValue (str, terms) rest)

;;

let termToInt t : int = 
  match  t with 
  | Number n -> n 
  | _ -> raise (Foo "error termToInt")
;;



let rec updateValuation (ops:globalV) : unit = 
  match ops with
  | [] -> ()
  | (str, terms):: rest -> let _ = valuationTRS := updateOneValue (str, terms) (!valuationTRS) in updateValuation rest ;;

let rec derivitive_concrete (pi :pure) (es:es) (f:head) : (es)  =
  match es with
  Bot -> Bot 
| Emp -> Bot
| Cons (es1 , es2) ->  
  let (es1_der) = derivitive_concrete pi es1 f in 
  let es1' = Cons (es1_der, es2) in 
  let (es2_der) = derivitive_concrete pi es2 f in    
  if nullable pi es1
    then (ESOr (es1', es2_der))
    else (es1')

| ESOr (es1 , es2) -> ESOr (derivitive_concrete pi es1 f, derivitive_concrete pi es2 f) 
| Kleene es1 -> Kleene (derivitive_concrete pi es1 f)
| Guard (pi1) -> if entailConstrains (globalVToPure !valuationTRS) pi1 then Emp else es
| Event (Tau pi1) -> if entailConstrains (globalVToPure !valuationTRS) pi1 then Emp else Bot

| Par (es1 , es2) -> 
  let es1_der = derivitive_concrete pi es1 f in 
  (match normalES es1_der pi with 
  | Bot -> Par (es1 , derivitive_concrete pi es2 f)
  | _ -> Par (es1_der, es2))

| Event Any -> Emp 
| Event (Absent str) -> 
  (match f with 
  | (Instant (Present (strh, _, _))) -> if String.compare strh str == 0 then Bot else Emp 
  | _ -> Emp 
  )

| Event (Present(str, v, ops)) -> 
  (match f with 
  | Instant (Present(s, v, o)) -> 
    if compareEvent ((Present(s, v, o))) (Present(str, v, ops)) 
    then (updateValuation (List.map (fun (s, t) -> (s, termToInt t)) ops); Emp )
    else Bot 
  | _ -> Bot )
  
| Ttimes (Ttimes (es1, t1) , t2 ) -> 
  derivitive_concrete pi (Ttimes (es1, t1)) f

| Ttimes (Emp, tIn) -> 
		(match f with 
		| T  t -> (Emp)
		| Ev (ev, t) -> (Bot)
		| Instant ev -> (Bot)
		)
| Ttimes (Event ev1, tIn) -> 
		(match f with 
		| T  t ->  let t_new = getAfreeVar () in 
      (Ttimes (Event ev1, Var t_new))
		| Ev (ev, t) ->  if entailEvent ev ev1 then (Emp) else (Bot)

		| Instant ev ->  if entailEvent ev ev1 then (Ttimes (Emp, tIn)) else (Bot)
		)
	
| Ttimes (es1, tIn) -> 
		(match f with 
		| T  t ->  let t_new = getAfreeVar () in 
      (Ttimes (es1, Var t_new))
		| Ev (ev, t) ->  
		  let (es1_der) = derivitive_concrete pi es1 (Instant ev) in 
      (match normalES es1_der pi with 
      | Emp -> (Emp)
      | _ -> 
        let t_new = getAfreeVar () in 
        (Ttimes (es1_der, Var t_new))
      )
		
		| Instant ev ->  let (es1_der) = derivitive_concrete pi es1 f in 
        match normalES es1_der pi with 
        | Bot -> (Bot)
        | _ -> 
      (Ttimes (es1_der, tIn))

		)





;;


let rec containment_concrete (effL:effect) (effR:effect) : (binary_tree * bool) = 
  let normalFormL = normalEffect effL in 
  let normalFormR = normalEffect effR in
  let showEntail  =  showEntailmentEff normalFormL normalFormR (*^ "  ***> " ^ (showPure (normalPure side))*)  in
  (*  print_string (showEntail^"\n");*)
  if nullableEff  normalFormL  = true &&  (nullableEff normalFormR  = false) then   
    (Node (showEntail ^ showRule DISPROVE,[] ), false)

  else 
    let (finalTress, finalRe) = List.fold_left (fun (accT, accR) (pL, esL) -> 
      let (subtree, re) = List.fold_left (fun (accInT, accInR) (pR, esR) -> 
        let (subtreeIn, reIn) = 
          if askZ3 pL == false then (Node (showEntail ^ " [PURE ER LHS] ", []), false) else 

          if reoccur (esL) (esR) !delta then 
            (Node (showEntail ^ showRule REOCCUR,[] ), true)
             
          else 
            let fstSet = fst pL esL  in
            if List.length (fstSet) == 0 then (Node (showEntail ^ " [NO FST1]",[] ), true)
            else 
            let (subtrees, re) = List.fold_left (fun (accT, accR) f -> 
            let (derL) = derivitive_concrete pL esL f  in 
            let (derR) = derivitive_concrete pR esR f  in 
            let _ = delta := ((esL, esR) :: !delta) in 
            let (subtree, result) = containment_concrete [(pL, derL)] [(pR, derR)]  in 
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

let printReportHelper_concrete lhs rhs : (binary_tree * bool) = 
  
  let a : hypotheses ref = ref [] in 
  let _ = (delta: hypotheses ref) := !a in 

  containment_concrete (lhs) (rhs)    

  ;;

let printReport_concrete (valuation: globalV) (lhs:effect) (rhs:effect) :string =
  let _ = initialise () in 
  let _ = valuationTRS := valuation in 
  let startTimeStamp = Sys.time() in
  let (tree, re) =  printReportHelper_concrete  lhs rhs  in
  let verification_time = "[Verification Time: " ^ string_of_float ((Sys.time() -. startTimeStamp) *. 1000.0) ^ " ms]\n" in
  let result = printTree ~line_prefix:"* " ~get_name ~get_children tree in
  let buffur = ( "===================================="^"\n[Result] " ^(if re then "Succeed\n" else "Fail\n") ^verification_time^" \n\n"^ result)
  in buffur
  ;;