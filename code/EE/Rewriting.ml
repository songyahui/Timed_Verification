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

let varNames = ["t1"; "t2"; "t3"; "t4";"t5";"t6";"t7";"t8";"t9";"t10"
;"t11"; "t12"; "t13"; "t14";"t15";"t16";"t17";"t18";"t19";"t20"
;"t21"; "t22"; "t23"; "t24";"t25";"t26";"t27";"t28";"t29";"t30"];;

(*used to generate the free veriables, for subsititution*)
let freeVar: string list ref = ref varNames;;

let globelVar : string list ref = ref [];;

let initialise () = 
  let _ = globelVar := [] in 
  let _ = freeVar :=  varNames in 
  ()
;;

let getAfreeVar () :string  =
  if List.length !freeVar == 0 then  raise ( Foo "freeVar list too small exception!")
  else 
    let x = List.hd !freeVar in 
    let _ = globelVar:=x :: !globelVar in  
    let _ = freeVar := List.tl !freeVar in 
    x 
;;


let rec nullable (pi :pure) (es:es) : bool=
  match es with
    Bot -> false 
  | Emp -> true
  | Event _ -> false 
  | Cons (es1 , es2) -> (nullable pi es1) && (nullable pi es2)
  | ESOr (es1 , es2) -> (nullable pi es1) || (nullable pi es2)
  | Ttimes (es1, t) ->  false
  | Kleene es1 -> true
;;

let nullableEff (eff:effect) : bool = 
  List.fold_left (fun acc (pi, es) -> acc || (nullable pi es)) false eff;;

(*assert (nullable (Eq (Var "t", Number 0)) (Ttimes (Emp, Var "t")) == true);;
assert (nullable (Eq (Var "t", Number 1)) (Ttimes (Emp, Var "t")) == false);;
*)

let rec fst (pi :pure) (es:es): head list = 
  match es with
    Bot -> []
  | Emp -> []
  | Event ev ->  let t = getAfreeVar () in [Ev(ev, Var t)]
  | Ttimes (Emp, t) -> [Tau t]
  | Ttimes (es1, t) ->  fst pi es1
  | Cons (es1 , es2) ->  if nullable pi es1 then append (fst pi es1) (fst pi es2) else fst pi es1
  | ESOr (es1, es2) -> append (fst pi es1) (fst pi es2)
  | Kleene es1 -> fst pi es1
;;

let fstEff (eff:effect) : head list = List.flatten (List.map (fun (pi, es) -> fst pi es) eff);; 

let appendEff_ES eff es: effect = List.map (fun (pi, es1) -> (pi, Cons (es1, es))) eff;;  

let entailEvent ev1 ev2 : bool =
  match (ev1, ev2) with 
  | (_, Any) -> true 
  | (Present str1, Present str2) -> String.compare str1 str2 == 0 
  | (Present str1, Absent str2) -> String.compare str1 str2 != 0 
  | (Absent str1, Absent str2) ->  String.compare str1 str2 == 0
  | _ -> false 
;;


let rec derivitive (pi :pure) (es:es) (f:head) : (es * pure) =
  match f with 
  | Tau  t ->
    (match es with 
      Bot -> (Bot, TRUE)
    | Emp -> (Bot, TRUE)
    | Event ev -> (Event ev, TRUE)
    | Ttimes (Emp, tIn) -> (Emp,  Eq(t , tIn))
    | Ttimes (es1, tIn) -> 
      let t_new = getAfreeVar () in 
      (Ttimes (es1, Var t_new), PureAnd(Eq(Plus (t,Var t_new) , tIn), Gt (Var t_new, Number 0)))

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
    )
  | Ev (ev, t) -> 
    (match es with 
      Bot -> (Bot, TRUE)
    | Emp -> (Bot, TRUE)
    | Event ev1 -> if entailEvent ev ev1 then (Emp, TRUE) else (Bot, TRUE)
    | Ttimes (es1, tIn) -> 
      let (es1_der, side1) = derivitive pi es1 f in 
      let t_new = getAfreeVar () in 
      let p_new = PureAnd (side1, PureAnd(Eq(Plus (t,Var t_new) , tIn), Gt (Var t_new, Number 0))) in 
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
    )


  
;;


(*


let rec getSize (es:es) : int=
  match es with
    Bot -> 0 
  | Emp -> 1
  | Event _ -> 1 
  | Cons (es1 , es2) ->  (getSize es1) + (getSize es2)
  | ESOr (es1 , es2) ->  max (getSize es1)  (getSize es2)
  | ESAnd (es1 , es2) -> max (getSize es1) (getSize es2)
  | Ttimes (es1, t) ->  
    (match t with 
      Number n -> (getSize es1) * n
    | _ -> (getSize es1)
    )
  | Underline -> 1
  | Kleene es1 -> (getSize es1)
  | _ -> raise (Foo "getSize")
;;



let rec isBotES (es:es) :bool = 
  match es with 
    Bot -> true 
  | _ -> false 
;;

let rec isEmpES (es:es) :bool = 
  match es with 
    Emp -> true 
  | _ -> false 
;;





let rec appendEff_ES eff es = 
  match eff with 
    Effect (p , es_eff) ->  Effect(p, Cons (es_eff, es))
  | Disj (eff1 , eff2)  ->  Disj (appendEff_ES eff1 es, appendEff_ES eff2 es)
  
  (*raise ( Foo "appendEff_ES exception!")*)
  ;;

let ifShouldDisj (temp1:effect) (temp2:effect) : effect = 
  match (temp1, temp2) with
      (Effect(pure1, evs1), Effect(pure2, evs2)) -> 
        if comparePure pure1 pure2 then  Effect (pure1, ESOr (evs1, evs2))
        else Disj (temp1, temp2 )
      | _ -> 
      Disj (temp1, temp2 )
  ;;
let rec ifShouldConj (temp1:effect) (temp2:effect) : effect = 
  match (temp1, temp2) with
      (Effect(pure1, evs1), Effect(pure2, evs2)) -> 
        Effect (PureAnd (pure1, pure2), ESAnd (evs1, evs2))
    | (Effect(pure1, evs1), Disj (eff1, eff2)) -> 
      Disj (ifShouldConj temp1 eff1, ifShouldConj temp1 eff2)
    | (Disj (eff1, eff2), _) ->
      Disj (ifShouldConj eff1 temp2, ifShouldConj eff2 temp2)
      (*Disj (temp1, temp2 )*)
  ;;

let rec compareES es1 es2 = 
  
  match (es1, es2) with 
    (Bot, Bot) -> true
  | (Emp, Emp) -> true
  | (Event (s1,p1), Event (s2,p2)) -> 
    compareEvent (s1,p1) (s2,p2)
  | (Not (s1,p1), Not (s2,p2)) -> 
    compareEvent (s1,p1) (s2,p2)
  | (Cons (es1L, es1R), Cons (es2L, es2R)) -> (compareES es1L es2L) && (compareES es1R es2R)
  | (ESOr (es1L, es1R), ESOr (es2L, es2R)) -> 
      let one = ((compareES es1L es2L) && (compareES es1R es2R)) in
      let two =  ((compareES es1L es2R) && (compareES es1R es2L)) in 
      one || two
  | (ESAnd (es1L, es1R), ESAnd (es2L, es2R)) -> 
      let one = ((compareES es1L es2L) && (compareES es1R es2R)) in
      let two =  ((compareES es1L es2R) && (compareES es1R es2L)) in 
      one || two
  | (Ttimes (esL, termL), Ttimes (esR, termR)) -> 
      let insideEq = (compareES esL esR) in
      let termEq = compareTerm termL termR in
      insideEq && termEq
  | (Kleene esL, Kleene esR) -> compareES esL esR
  | (Underline, Underline ) -> true
  | _ -> false
;;



let rec splitEffects eff : (pure * es) list = 
  match eff with 
    Effect (p1, es1) -> [(p1, es1)]
  | Disj (eff1, eff2) -> append (splitEffects eff1) (splitEffects eff2)
  ;;

let rec concertive (es:es) (t:int): es = 
  if t ==0 then Emp 
  else Cons (es, concertive es (t -1))
  ;;

(*this is use to keep the bot in head for negation usage *)
let rec normalES_Bot es pi = 
  match es with
    Bot -> es
  | Emp -> es
  | Event _ -> es
  | Not _ -> es 
  | Underline -> Underline
  | Cons (Cons (esIn1, esIn2), es2)-> normalES_Bot (Cons (esIn1, Cons (esIn2, es2))) pi
  | Cons (es1, es2) -> 
      let normalES1 = normalES_Bot es1 pi in
      let normalES2 = normalES_Bot es2 pi in
      (match (normalES1, normalES2) with 
        (Emp, _) -> normalES2
      | (_, Emp) -> normalES1

      | (Kleene (esIn1), Kleene (esIn2)) -> 
          if aCompareES esIn1 esIn2 == true then normalES2
          else Cons (normalES1, normalES2)
      | (Kleene (esIn1), Cons(Kleene (esIn2), es2)) -> 
          if aCompareES esIn1 esIn2 == true then normalES2
          else Cons (normalES1, normalES2) 

      | (normal_es1, normal_es2) -> 
        match (normal_es1, normal_es2) with 
        |  (Cons (esIn1, esIn2), es2)-> normalES_Bot (Cons (esIn1, Cons (esIn2, es2))) pi 
        |  (ESOr (or1, or2), es2) -> normalES_Bot (ESOr ( (Cons (or1, es2)),  (Cons (or2, es2)))) pi
        |  (es1, ESOr (or1, or2)) -> normalES_Bot (ESOr ( (Cons (es1, or1)),  (Cons (es1, or2)))) pi
        | _-> Cons (normal_es1, normal_es2)
      ;)
  | ESOr (es1, es2) -> 
      (match (normalES_Bot es1 pi, normalES_Bot es2 pi) with 
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

  | ESAnd (es1, es2) -> 
      (match (normalES_Bot es1 pi, normalES_Bot es2 pi) with 

      | (Bot, norml_es2) -> Bot
      | (norml_es1, Bot) -> Bot
      | (Event (s1, p1), Event (s2, p2)) -> if compareEvent (s1, p1) (s2, p2) then Event (s1, p1) else Bot

      | (Emp, norml_es2) -> if nullable pi norml_es2 then Emp else Bot 
      | (norml_es1, Emp) -> if nullable pi norml_es1 then Emp else Bot 

      | (norml_es1, norml_es2) -> 
        if aCompareES  norml_es1 norml_es2 == true then norml_es1
        else ESAnd (norml_es1, norml_es2)

      )


  | Ttimes (es1, terms) -> 
      let t = normalTerms terms in 
      let normalInside = normalES_Bot es1 pi in 
      (match normalInside with
        Emp -> Emp
      | _ -> 
        let allPi = getAllPi pi [] in 
        if (existPi (Eq (terms, Number 0)) allPi) || (compareTerm t (Number 0 )) then Emp else Ttimes (normalInside, t))
        (*else if (existPi (Eq (terms, n)) allPi)) then Emp else Ttimes (normalInside, t))*)
  | Kleene es1 -> 
      let normalInside = normalES_Bot es1 pi in 
      (match normalInside with
        Emp -> Emp
      | Kleene esIn1 ->  Kleene (normalES_Bot esIn1 pi)
      | ESOr(Emp, aa) -> Kleene aa
      | _ ->  Kleene normalInside)



  ;;
  *)

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

let rec normalES (es:es) (pi:pure) :es = 
  match es with
    Bot -> es
  | Emp -> es
  | Event _ -> es
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
      (match normalInside with
        
      | _ -> 
        let allPi = getAllPi pi [] in 
        if (existPi (Eq (terms, Number 0)) allPi) then Emp else 
          match t with
            Number num -> concertive normalInside num 
          | _ -> Ttimes (normalInside, t))
        (*else if (existPi (Eq (terms, n)) allPi)) then Emp else Ttimes (normalInside, t))*)
  | Kleene es1 -> 
      let normalInside = normalES es1 pi  in 
      (match normalInside with
        Emp -> Emp
      | Kleene esIn1 ->  Kleene (normalES esIn1 pi )
      | ESOr(Emp, aa) -> Kleene aa
      | _ ->  Kleene normalInside)

;;



let rec normalEffect (eff:effect) :effect =
  let noPureOr:effect  = deletePureOrInEff eff in 
  let final = List.filter (fun (p, es) -> 
  match (p,  es ) with 
  | (_,  Bot) -> false 
  | (Ast.FALSE,  _) -> false  
  | _ -> true 
  ) (List.map (fun (p, es) -> (p, normalES es p)) noPureOr) in 
  if List.length final == 0 then [(FALSE, Bot)]
  else final 
  ;;

let reoccur normalFormL normalFormR delta : bool = false ;;



let rec containment (side:pure) (effL:effect) (effR:effect) (delta:hypotheses) : (binary_tree * bool) = 
  let normalFormL = normalEffect effL in 
  let normalFormR = normalEffect effR in
  let showEntail  =  showEntailmentEff normalFormL normalFormR ^ "  ***> " ^ (showPure (normalPure side)) in
  (*  print_string (showEntail^"\n");*)
  if nullableEff  normalFormL = true &&  (nullableEff normalFormR = false) then   (Node (showEntail ^ showRule DISPROVE,[] ), false)
  else if reoccur normalFormL normalFormR delta then  (Node (showEntail ^ showRule REOCCUR,[] ), true)

  else 
    let (finalTress, finalRe) = List.fold_left (fun (accT, accR) (pL, esL) -> 
      let (subtree, re) = List.fold_left (fun (accInT, accInR) (pR, esR) -> 
        let (subtreeIn, reIn) = 
          

            let fstSet = fst pL esL in
            if List.length (fstSet) == 0 then 
              if entailConstrains (PureAnd (pL, side)) pR then (Node (showEntail ^ " [NO FST]", [] ), true)
              else (Node (showEntail ^ " [PURE ER] ", []), false)
            else 
            let (subtrees, re) = List.fold_left (fun (accT, accR) f -> 
            let (derL, sideL) = derivitive pL esL f in 
            let (derR, sideR) = derivitive pR esR f in 
            let side' = PureAnd(side, PureAnd(sideL, sideR)) in 
            let (subtree, result) = containment side' [(pL, derL)] [(pR, derR)] ((normalFormL, normalFormR) :: delta) in 
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


  
  
  




  
(*
  (Node (showEntail ^ "not yet",[] ), true)
  
*)
  

  ;;

let rec reNameTerms t str: terms = 
match t with
  Var name -> Var (str^name)
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
| _ -> es 
;;

let reNameEffect (eff:effect) str: effect = 
  List.map (fun (p, es) -> (reNamePure p str, reNameEs es str )) eff
;;

let printReportHelper lhs rhs : (binary_tree * bool) = 
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
