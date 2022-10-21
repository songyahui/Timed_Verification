open List
open Ast
open Parser
open Askz3
open Pretty


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
  (*
  if !counter > 15 then raise (Foo "something wrong?")
  else *)

    let x = "t"^string_of_int (!counter) in 
    let _ = counter := !counter + 1 in 
    let _ = globelVar:=x :: !globelVar in  
    x 
;;

let compareEff eff1 eff2 =
  match (eff1, eff2) with
  | ([(FALSE, _ )], [(FALSE, _)]) -> true 
  | ([(FALSE, _ )], [(_, Bot )]) -> true 
  | ([(_, Bot)], [(FALSE, _ )]) -> true 
  | ([(_, Bot )], [(_, Bot)]) -> true 
  | ( [(_, es1)], [ (_, es2 )]) -> aCompareES es1 es2
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
  | Par (es1, es2) -> 
    let es1' = normalES es1 pi in 
    let es2' = normalES es2 pi in 

    (match (es1', es2') with 
    | (Emp, _) -> es2'
    | (_, Emp) -> es1'
    | (Bot, Bot) -> Bot
    | (Bot, _) -> es2'
    | (_, Bot) -> es1'
    (*
    | (Cons (Ttimes (es1, t1), es12), Cons (Ttimes (Emp, t2), es22)) 
    | (Cons (Ttimes (Emp, t2), es22), Cons (Ttimes (es1, t1), es12)) ->

      let trace1 =  (Cons (Ttimes (Emp, t2), Par (Cons(Ttimes (es1, (Minus (t1, t2))), es12), es22))) in 
      let trace2 =  Cons (Cons (Ttimes (es1, t1), Ttimes (Emp, (Minus (t2, t1)))), Par (es12, es22)) in 
      
    

      if entailConstrains pi (GtEq(t1, t2)) then trace1 
      else if entailConstrains pi (Lt(t1, t2)) then trace2
      else ESOr(trace1, trace2)
      
      


    | (Cons (Ttimes (es1, t1), es12), Ttimes (Emp, t2)) 
    | (Ttimes (Emp, t2), Cons (Ttimes (es1, t1), es12)) ->
      let trace1 = (Cons (Ttimes (Emp, t2), Cons(Ttimes (es1, (Minus (t1, t2))), es12))) in 
      let trace2 = Cons (Cons (Ttimes (es1, t1), Ttimes (Emp, (Minus (t2, t1)))), es12)  in 


    
      if entailConstrains pi (GtEq(t1, t2)) then trace1 
      else if entailConstrains pi (Lt(t1, t2)) then trace2
      else ESOr(trace1, trace2)


    | (Ttimes (_, _), Ttimes (Emp, _)) 
    | (Ttimes (Emp, _), Ttimes (_, _)) -> raise (Foo "par 4")

    | _ -> Par (es1', es2')
    *)
    | _ -> Par (es1', es2')

)


  | Guard (pi1, es1) -> Guard (pi1, normalES es1 pi) 
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
      | (Kleene (esIn1), Cons(Kleene (esIn2), _)) -> 
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
      | Emp -> Emp
      | Bot -> Emp
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
    if stricTcompareTerm t1 t2 then (Ttimes (es1, t1), None)
    else (Ttimes (es1, t1), Some (Eq(t1, t2))) 
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
  | Ttimes (es1, t) ->  
    let pure = (PureAnd(pi, Eq(t, Number 0)))  in 
    (*print_string (showPure pure ^ ", " ^ string_of_bool ( askZ3 pure) ^ "\n");*)
    (askZ3 pure) && nullable pi es1
  | Kleene _ -> true
  | Par (es1 , es2) -> (nullable pi es1) && (nullable pi es2)
  | Guard (_) -> false
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
    let es1' = normalES es1 pi in  
    (match  es1' with 
    | Emp -> [T t]
    | Event (ev) ->  [Ev(ev, t)]
    | _ -> List.map (fun h -> 
      let t_new = getAfreeVar () in 
      match h with 
      | Instant ev -> Ev(ev, Var t_new)
      | _ -> h
      ) (fst pi es1')
    )
  | Cons (es1 , es2) ->  if nullable pi es1 then append (fst pi es1) (fst pi es2) else fst pi es1
  | ESOr (es1, es2) -> append (fst pi es1 ) (fst pi es2)

  | Par (es1, es2) -> append (fst pi es1 ) (fst pi es2 )
  | Kleene es1 -> fst pi es1
  | Guard (pi1, _) -> [Instant(Tau pi1); Instant (Tau (Neg pi1))]

;;

let fstEff (eff:effect)  : head list = List.flatten (List.map (fun (pi, es) -> fst pi es) eff);; 

let appendEff_ES eff es: effect = List.map (fun (pi, es1) -> (pi, Cons (es1, es))) eff;;  

let entailEvent ev1 ev2 : bool =
  match (ev1, ev2) with 
  | (_, Any) -> true 
  | (Tau pi1, Tau pi2) -> entailConstrains pi1 pi2
  | (Present (str1, v1, _), Present (str2, v2, _)) -> String.compare str1 str2 == 0 && compareMaybeValue v1 v2 
  | (Present (str1, _, _), Absent str2) -> String.compare str1 str2 != 0 
  | (Absent str1, Absent str2) ->  String.compare str1 str2 == 0
  | _ -> false 
;;



let rec derivitive (pi :pure) (es:es) (f:head) : (es * pure option) list =
  match normalES es pi with 
  | Bot -> [(Bot, None)]
  | Emp -> [(Bot, None)]
  | Cons ((Ttimes(es1', t)) , es2) ->  
    let es1 = (Ttimes(es1', t)) in 
    let derList1 = derivitive pi es1 f in (*  *)
    let longer = List.map (fun (es1_der, side1) -> (Cons(es1_der, es2), side1)) derList1 in 
    if nullable pi es1
      then 
        let temp = derivitive pi (Cons (es1', es2))  f in 
        let shorter = List.map (fun (a1, a2) -> 
        (a1, Some (optionPureAndHalf  a2 (Eq(t, Number 0))))
        ) temp in
        List.append longer shorter
      else longer

  | Cons (es1 , es2) ->  
    let derList1 = derivitive pi es1 f in (*  *)
    let longer = List.map (fun (es1_der, side1) -> (Cons(es1_der, es2), side1)) derList1 in 
    let derList2  = derivitive pi es2 f in  
    if nullable pi es1
      then 
        let shorter = derList2 in
        List.append longer shorter
      else longer


  | ESOr (es1, es2) -> 
      let derList1 = derivitive pi es1 f in 
      let derList2 = derivitive pi es2 f in
      List.append derList1 derList2

  | Kleene es1 -> 
      let derList = derivitive pi es1 f in 
      List.map (fun (es1_der, side1) -> (Cons (es1_der, es), side1))derList
      
  | Par (es1, es2) ->
      let helper esIn = 
        let  derList  = derivitive pi esIn f in 
        List.map (fun (der, side) -> 
          match normalES der pi with 
          | Bot -> (esIn, None)
          | _ -> (der, side)
        )derList
      in 
      let derList1 = helper es1 in 
      let derList2 = helper es2 in 
      List.flatten(
        List.map (fun (esIn1, sideIn1) -> 
          List.map (fun (esIn2, sideIn2) -> 
            (Par(esIn1, esIn2), optionPureAnd sideIn1 sideIn2)
            )derList2
        )derList1
      )
  | Guard (pi1, es1) -> 
    (match f with 
    | Instant (Tau pi2) -> if entailConstrains pi2 pi1 then [(es1, None)] else [(es, None)]
    | _ -> [(es, None)]
    )
      
  | Event (Any) -> [(Emp, None)]

  | Event ev1 -> 
		(match f with 
		| T  _ -> [(Bot, None)]
		| Ev (_, _) -> [(Bot, None)]
		| Instant ev -> if entailEvent ev ev1 then [(Emp, None)] else [(Bot, None)]
		)

  | Ttimes (Ttimes (es1, t1) , t2 ) -> 
    let eff_der = derivitive pi (Ttimes (es1, t1)) f in 
    List.map (fun (es1_der, side1)->
      if stricTcompareTerm t1 t2 then (es1_der, side1)
      else 
      (es1_der, Some (optionPureAndHalf side1 (Eq(t1, t2))))
    )eff_der

  | Ttimes (Emp, tIn) -> 
		(match f with 
		| T  t -> 
      if stricTcompareTerm t tIn then [(Emp, None)]
      else [(Emp,  Some (Eq(t , tIn)))]
		| Ev (_, _) -> [(Bot, None)]
		| Instant _ -> [(Bot, None)]
		)

	| Ttimes (Event ev1, tIn) -> 
		(match f with 
		| T  t ->  let t_new = getAfreeVar () in 
      [(Ttimes (Event ev1, Var t_new), Some (PureAnd(Eq(Plus (t,Var t_new) , tIn), GtEq (Var t_new, Number 0))))]
		| Ev (ev, t) ->  if entailEvent ev ev1 then 
      (if stricTcompareTerm tIn t then [(Emp, None)]
      else [(Emp,Some ( Eq(tIn, t)))]) else [(Bot, None)]

		| Instant ev ->  if entailEvent ev ev1 then [(Ttimes (Emp, tIn), None)] else [(Bot, None)]
		)
	
	| Ttimes (es1, tIn) -> 
		(match f with 
		| T  t ->  let t_new = getAfreeVar () in 
      [(Ttimes (es1, Var t_new), Some (PureAnd(Eq(Plus (t,Var t_new) , tIn), GtEq (Var t_new, Number 0))))]
		| Ev (ev, t) ->  
		  let eff_Der1 = derivitive pi es1 (Instant ev) in 
      List.map (fun (es1_der, side1) -> 
        (match normalES es1_der pi with 
        | Emp -> if stricTcompareTerm tIn t then (Emp, side1)
          else (Emp, Some (optionPureAndHalf side1 (Eq(tIn, t))))
        | _ -> 
          let t_new = getAfreeVar () in 
          let p_new = optionPureAndHalf side1 (PureAnd(Eq(Plus (t,Var t_new) , tIn), GtEq (Var t_new, Number 0))) in 
          (Ttimes (es1_der, Var t_new), Some p_new)
      )
      )eff_Der1
		
		| Instant _ ->  
        let eff_Der1  = derivitive pi es1 f in 
        List.map (fun (es1_der, side1) -> 
          match normalES es1_der pi with 
          | Bot -> (Bot, Some (Eq (tIn, Number 0)))
          | _ -> (Ttimes (es1_der, tIn), side1)
      )eff_Der1

		)

;;



let normalEffect (eff:effect) :effect =
  let noPureOr:effect  = (* deletePureOrInEff *) eff in 
  let final = List.filter (fun (p, es) -> 
  match (p,  es ) with 
  | (_,  Bot) -> false 
  | (Ast.FALSE,  _) -> false  
  | _ -> true 
  ) (List.map (fun (p, es) -> 
      let (es', pi') = normalESUnifyTime es p in 
      (  normalPure    (optionPureAndHalf  pi' p), es')) noPureOr) in 
      
      (*normalPure p, normalES es p) noPureOr )in *)
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

let rec existNameAgr (li:string list) (name:string): bool = 
  match li with
  | [] -> false 
  | x :: xs -> if String.compare x name == 0 then true else existNameAgr xs name 
;;

let rec gatherTermsFromTerms (list_parm:param) (t:terms): string list = 
  match t with
| Var name -> 
  let list_Arg = List.map (fun (_, a) -> a) list_parm in 
  if (existNameAgr list_Arg name ) then [name]
  else []
| Number _ -> []
| Plus (t1, t2) -> List.append (gatherTermsFromTerms list_parm t1) (gatherTermsFromTerms list_parm t2)
| Minus (t1, t2) -> List.append (gatherTermsFromTerms list_parm t1) (gatherTermsFromTerms list_parm t2)


let rec gatherTermsFromPure (list_parm:param) (p:pure) : string list =
  match p with 
  | Gt (t1, t2) 
  | Lt (t1, t2)   
  | GtEq (t1, t2)   
  | LtEq (t1, t2)   
  | Eq (t1, t2) ->  List.append (gatherTermsFromTerms list_parm t1) (gatherTermsFromTerms list_parm t2)
  | PureOr (p1, p2)  
  | PureAnd (p1, p2) -> List.append (gatherTermsFromPure list_parm p1) (gatherTermsFromPure list_parm p2)
  | Neg p1 -> (gatherTermsFromPure list_parm p1)
  | TRUE|FALSE -> []
  ;;




let rec gatherTTermsFromES (list_parm:param) (es:es) : terms list = 
  match es with
    Bot -> [] 
  | Emp -> []
  | Event _ -> [] 
  | Cons (es1 , es2) -> List.append (gatherTTermsFromES list_parm es1) (gatherTTermsFromES list_parm es2)
	| ESOr (es1 , es2) -> List.append (gatherTTermsFromES list_parm es1) (gatherTTermsFromES list_parm es2)
  | Ttimes (_, t) ->  [t]
  | Kleene es1 -> (gatherTTermsFromES list_parm es1)
  | Par (es1 , es2) -> List.append (gatherTTermsFromES list_parm es1) (gatherTTermsFromES list_parm es2)
  | Guard (_) -> [] 
  ;;

let gatherTTerms (list_parm:param) (eff:effect) : terms list =
  List.flatten (List.map (fun (_, es) -> 
    gatherTTermsFromES list_parm es 
  ) eff) ;;


let showEntailGneral normalFormL normalFormR side   =  showEntailmentEff normalFormL normalFormR ^ "  ***> " ^ (showPure (normalPure side)) ;; 


let existNonRelatedToTerms p terms list_parm : bool =
  let termsP =  (gatherTermsFromPure list_parm p) in 
  let rec herlper t1 li = 
    match li with 
    | [] -> true 
    | t2::xs -> if String.compare t1 t2 == 0 then false  else herlper t1 xs 
  in 
  let rec aux li: bool = 
    match li with 
    | [] -> false 
    | x::xs -> if herlper x terms then true else aux xs 
  in aux termsP ;;

let filterOut (side:pure) (pR:pure) list_parm: pure = 
  let terms =  gatherTermsFromPure list_parm side in 
  let terms = List.append (List.map (fun (_, a)-> a) list_parm) terms in 
  let splitConjpR = splitConj pR in 
  let filter' = List.filter (fun p -> existNonRelatedToTerms p terms list_parm == false) splitConjpR in 

  if List.length filter' == 0 then TRUE 
  else List.fold_left (fun acc a -> PureAnd(acc, a)) (List.hd filter') (List.tl filter') 
;;

let isBot es pi: bool = 
  match normalES es pi with
  | Bot -> true 
  | _ ->  false 
  ;;


let rec containment (list_parm:param) (side:pure) (effL:effect) (effR:effect) delta: (binary_tree * bool) = 
  let normalFormL = normalEffect effL in 
  let normalFormR = normalEffect effR in
  let showEntail  =  showEntailmentEff normalFormL normalFormR ^ "  ***> " ^ (showPure (normalPure side))  in
  (*print_string (showEntail^"\n");*)


    let (finalTress, finalRe) = List.fold_left (fun (accT, accR) (pL, esL) -> 

      let rec iterateRHS (accInT, accInR) li = 
        match li with
        | [] -> (accInT, accInR) 
        | (pR, esR) :: lirest -> 
        let (subtreeIn, reIn) = 
          if askZ3 pL == false then 
            ([Node (showEntail ^ " [PURE False LHS] ", [])], true)) else 
          
          if nullable pL esL  = true &&  (nullable  (PureAnd(pL, pR)) esR  = false) then   
            ([Node (showEntail ^ showRule DISPROVE,[] )], false)
        
          else if reoccur (esL) (esR) delta (*!delta*) then 
   
            ([Node (showEntail ^ " [REOCCUR]",[] )], true)
             
          else 
            let fstSet = fst pL esL  in
            if List.length (fstSet) == 0 then 
              (* SYH to compute weather rhs is overlapping side 
              if overlapterms pR (normalPure side) == false then ([Node (showEntail ^ " [PROVE]",[] )], true)
              else 
              *)
                (if entailConstrains (PureAnd (pL, side)) (filterOut side pR list_parm) then 
                  
                  ([Node (showEntail ^ " [PROVE]", [] )], true)
                else 
                  (*print_string(showPure (PureAnd (pL, side)) ^ "==>" ^ showPure (filterOut side pR list_Arg) ^"\n"); *)
                  ([Node (showEntail ^ " [PURE ER] ", [])], false)
                )

            else 
            let (subtrees, re) = List.fold_left (fun (accT, accR) f -> 


              let esLDer = derivitive pL esL f  in (* (derL, sideL) *)
              let esRDer = derivitive pR esR f  in (*  (derR, sideR) *)

              let rec iteratorDerRHS (accDerT, accDerR) rhsDerList lhsDer : (binary_tree list * bool) = 
                let (derL, sideL) = lhsDer in 
                match rhsDerList with 
                | [] -> (accDerT, accDerR)
                | (derR, sideR) :: rhsDerListrest -> 
                  let side' = optionPureAndHalf (optionPureAnd sideL sideR)  side  in 
                  let delta' =  ((esL, esR) :: delta) in 
                  let (subtreeDer, resultDer) = containment list_parm  side' [(pL, derL)] [(pR, derR)] delta' in 
                  if resultDer == true then ([subtreeDer], resultDer)
                  else iteratorDerRHS (List.append accDerT [subtreeDer], accDerR|| resultDer) rhsDerListrest lhsDer 
              in 

              let rec iteratorDerLHS (accDerT, accDerR) lhsDerList: (binary_tree list * bool) = 
                match lhsDerList with 
                | [] -> (accDerT, accDerR)
                | lhsDer :: lhsDerListrest -> 
                  let (subtreeDer, resultDer) = iteratorDerRHS ([], false) esRDer lhsDer in 
                  if resultDer == false then (subtreeDer, resultDer)
                  else iteratorDerLHS (List.append accDerT subtreeDer, accDerR && resultDer) lhsDerListrest 
              in 
              let (subtree, result) = iteratorDerLHS ([], true) (List.filter (fun (ees, _) -> isBot ees pL == false) esLDer) in 

              (List.append accT subtree, accR && result) 
            ) ([], true) fstSet in 
            ([Node(showEntailmentEff [(pL, esL)] [(pR, esR)] ^ "  ***> " ^ (showPure (normalPure side)) ^ showRule UNFOLD , subtrees)], re)

          in 
        if reIn == true then (subtreeIn, reIn) 
        else iterateRHS (List.append accInT subtreeIn , reIn || accInR) lirest 
      in 
      let (subtree, re) = iterateRHS ([], false) (normalFormR) in 
            

      (List.append accT subtree , re && accR)
    ) ([], true) normalFormL in 
    if List.length (finalTress) == 1 then 
      (List.hd finalTress, finalRe)
    else 
      (Node (showEntail ^ " [SPLITLHS] ", finalTress), finalRe)


  ;;



let rec reNameTerms (list_parm:param) t str: terms = 
match t with
  Var name -> 
    let list_Arg = List.map (fun (_, a) -> a) list_parm in 
    if (existNameAgr list_Arg name ) then Var name
    else 
    Var (str^name)
| Number _ -> t
| Plus (t1, t2) -> Plus (reNameTerms list_parm t1 str, reNameTerms list_parm t2 str)
| Minus (t1, t2) -> Minus (reNameTerms list_parm t1 str, reNameTerms list_parm t2 str)

;; 


let rec reNamePure (list_parm:param) p str : pure =
  match p with
| Gt (t1, t2) -> Gt (reNameTerms list_parm t1 str, reNameTerms list_parm t2 str)
| Lt (t1, t2) ->  Lt (reNameTerms list_parm t1 str, reNameTerms list_parm t2 str)
| GtEq (t1, t2) ->  GtEq (reNameTerms list_parm t1 str, reNameTerms list_parm t2 str)
| LtEq (t1, t2) ->  LtEq (reNameTerms list_parm t1 str, reNameTerms list_parm t2 str)
| Eq (t1, t2) ->  Eq (reNameTerms list_parm t1 str, reNameTerms list_parm t2 str)
| PureOr (p1, p2) -> PureOr (reNamePure list_parm p1 str, reNamePure list_parm p2 str)
| PureAnd (p1, p2) -> PureAnd (reNamePure list_parm p1 str, reNamePure list_parm p2 str)
| Neg p1 -> Neg (reNamePure list_parm p1 str)
| _ -> p 
;; 

let rec reNameEs (list_parm:param) es str =
  match es with
| Cons (es1, es2) -> Cons (reNameEs list_parm es1 str, reNameEs list_parm es2 str)

| ESOr (es1, es2) -> ESOr (reNameEs list_parm es1 str, reNameEs list_parm es2 str)
| Ttimes (es1, t) -> Ttimes (reNameEs list_parm es1 str, reNameTerms list_parm t str) 
| Kleene es1 -> Kleene (reNameEs list_parm es1 str )
| Par (es1, es2) -> Par (reNameEs list_parm es1 str, reNameEs list_parm es2 str)
| Guard (pi1, es1) -> Guard (reNamePure list_parm pi1 str, reNameEs list_parm es1 str) 
| _ -> es 
;;

let reNameEffect (list_parm:param) (eff:effect) str: effect = 
  List.map (fun (p, es) -> (reNamePure list_parm p str, reNameEs list_parm es str )) eff
;;






let addPureToEff p eff = List.map (fun (pi, es) ->(PureAnd (pi, p), es)) eff ;;

let printReportHelper (list_parm:param) lhs rhs : (binary_tree * bool) = 
  
  (*
  let normalFormL = normalEffect lhs in 
  let normalFormR = normalEffect rhs in
  let showEntail  =  showEntailmentEff normalFormL normalFormR (*^ "  ***> " ^ (showPure (normalPure side)) *) in
  print_string (showEntail ^"\n"); 
    (Leaf , true)


  *)

  let renamedLHS = reNameEffect list_parm lhs "l"  in  
  let renamedRHS = reNameEffect list_parm rhs "r"  in 

  
  let alltheTVar = List.append (gatherTTerms list_parm renamedLHS) (gatherTTerms list_parm renamedRHS) in 
  let side = if List.length alltheTVar == 0 then Ast.TRUE else
    List.fold_left (fun acc a -> Ast.PureAnd (acc , Ast.GtEq( a, Number 0))) 
    (Ast.GtEq(List.hd alltheTVar, Number 0)) (List.tl alltheTVar) in 
  
  containment  list_parm (Ast.TRUE) (List.map (fun (p, es)-> (PureAnd (p,side),es)) renamedLHS) (renamedRHS)  []  

  ;;


let printReport (list_parm:param) lhs rhs :string =
  let _ = initialise () in 
  let startTimeStamp = Sys.time() in
  let (tree, re) =  printReportHelper list_parm lhs rhs  in
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



let globalVToPure (v:globalV) : pure =
  let pureList = List.map (fun (str, n) -> Eq(Var str, Number n)) v in 
  let rec helper li: pure = 
    match li with 
    | [] -> TRUE 
    | p :: rest -> PureAnd (p, helper rest)
  in 
  helper pureList
;;

let rec retriveVar valuation str : int = 
  match valuation with 
  | [] -> raise (Foo (str ^" does not exist in current V "))
  | (s, t) ::rest -> if String.compare s str == 0 then t 
  else retriveVar rest str
  ;;

let rec retriveAndCompute valuation terms : int = 
  match terms with 
  | Var str -> retriveVar valuation str
  | Number n -> n 
  | Plus (t1, t2) -> (retriveAndCompute valuation t1) + (retriveAndCompute valuation t2)
  | Minus (t1, t2) -> (retriveAndCompute valuation t1) - (retriveAndCompute valuation t2)


let rec updateOneValue ((str, terms)) valuation: globalV = 
  match valuation with 
  | [] -> raise (Foo (str ^" does not exist in current V "))
  | (s, t) :: rest -> if String.compare s str == 0 
    then (str, retriveAndCompute valuation terms):: rest 
    else (s, t) :: (updateOneValue (str, terms) rest)

;;



let rec updateValuation valuation (ops:assign list) : globalV = 
  match ops with
  | [] -> valuation
  | (str, terms):: rest -> 
    let new_valuation = updateOneValue (str, terms) (valuation)  in 
    updateValuation new_valuation rest 
;;


let rec parallecompose  (pi :pure) (trace1: headTrace) (trace2: headTrace) :headTrace list = 
  match (trace1, trace2) with 
  | ([], []) -> [[]]
  | (x, []) 
  | ([], x) -> [x]
  | (x::xs, y::ys) -> 
    (
      let temp = parallecompose pi xs ys in 
      match (x, y) with 
      | (Instant _, _) 
      | (_, Instant _) -> 
        let aaa = (List.append (List.map (fun t -> x::y:: t) temp) (List.map (fun t -> y::x:: t) temp)) in 
        let bbb = [[x];[y]] in 
        List.append aaa bbb

      | (Ev (_, t1), Ev (_, t2)) -> 

        print_string ("EvEv: " ^ string_of_head x ^ "   " ^ string_of_head y ^ "\n");
        if entailConstrains pi (Gt(t1, t2)) then (List.map (fun t -> y::x:: t) temp)
        else if entailConstrains pi (Lt(t1, t2)) then (List.map (fun t -> x::y:: t) temp) 
        else 
          
          let temp1 = parallecompose pi (x::xs) ys in 
          let temp2= parallecompose pi (xs) (y::ys) in 
        
          let aaa = List.append (List.map (fun t -> y:: t) temp1) (List.map (fun t -> x:: t) temp2) in 
          let bbb = [[x];[y]] in 
          List.append aaa bbb

      |  (Ev (_, t1), T t2) -> 
        print_string ("EvT: " ^ string_of_head x ^ "   " ^ string_of_head y ^ "\n");

         if entailConstrains pi (Lt(t1, t2)) then (List.map (fun t -> x::(T (Minus(t2, t1))):: t) temp)
         else if entailConstrains pi (Gt(t1, t2)) then (List.map (fun t -> y::x:: t) temp)
         else 
          (print_string ("EvT lolololo" ^ "\n");
          List.append (List.map (fun t -> y::x:: t) temp) (List.map (fun t -> x::y:: t) temp)
)


      |  (T t2, Ev (_, t1)) -> 
          print_string ("TEv: " ^ string_of_head x ^ "   " ^ string_of_head y ^ "\n");

         if entailConstrains pi (Lt(t1, t2)) then 
            (print_string ("lolololo" ^ "\n");
            (List.map (fun t -> y::(T (Minus(t2, t1))):: t) temp))
         else if entailConstrains pi (Gt(t1, t2)) then (List.map (fun t -> x::y:: t) temp)
         else 
          (print_string ("TEv lolololo" ^ "\n");

          List.append (List.map (fun t -> y::x:: t) temp) (List.map (fun t -> x::y:: t) temp))




      | _ -> (List.map (fun t -> x::y:: t) temp)
      
    )
    ;;




let rec fst_concrete valuation  (pi :pure) (es:es) : (head) list = 
  match es with
    Bot -> []
  | Emp -> []
  (*| Event (Tau _) -> []*)
  | Event ev ->  [Instant ev]
  | Ttimes (es1, t) -> 
    let es1' = normalES es1 pi in  
    (match  es1' with 
    | Emp -> [T t]
    | Event (ev) -> [ Ev(ev, t) ]
    | _ -> raise (Foo (showES es1'))(*List.map (fun h -> 
      let t_new = getAfreeVar () in 
      match h with 
      | Instant ev -> Ev(ev, Var t_new)
      | _ -> h
      ) (fst_concrete valuation  pi es1')*)
    )
  | Cons (es1 , _) ->  (*if nullable pi es1 
  then append (fst_concrete valuation  pi es1) (fst_concrete valuation  pi es2) else*) fst_concrete valuation  pi es1
  | ESOr (es1, es2) -> append (fst_concrete valuation  pi es1 ) (fst_concrete valuation  pi es2)

  | Par (es1, es2) -> 
    let htrace1 = (fst_concrete valuation  pi es1 ) in 
    let htrace2 = (fst_concrete valuation  pi es2 ) in 
    let zipH = shaffleZIP htrace1 htrace2 in 
    (*if cheatinggloalVar then 
     List.flatten (List.map (fun (trace1, trace2) -> 
      match (trace1, trace2) with 
      |  (Ev(_, _), T _) -> 
        if String.compare "lf1" (string_of_head trace2) == 0 then [trace1]
        else [trace1; trace2]
      | (T _, Ev(_, _)) -> 
        if String.compare "lf1" (string_of_head trace1) == 0 then [trace2]
        else [trace1; trace2]
                
      | _ -> [trace1; trace2]
      )zipH)

    else 
    *)

    List.flatten (List.map (fun (trace1, trace2) -> 
      match (trace1, trace2) with 
      |  (Ev(_, t1), T t2) -> 
                if entailConstrains pi (Gt(t2, t1)) then [trace1]
                else [trace1; trace2]
      | (T t1, Ev(_, t2)) -> 
                if entailConstrains pi (Gt(t1, t2)) then [trace2]
                else [trace1; trace2]          
      | _ -> [trace1; trace2]
  )zipH)
  (*
     
  *)

  | Kleene es1 -> fst_concrete valuation  pi es1
  | Guard (pi1, es1) -> 
    if entailConstrains (globalVToPure valuation) pi1 then 
    fst_concrete valuation  pi es1 else []
    

;;

let rec normalConcreteES valuation (es:es) (pi:pure) : es = 
  match es with
    Bot -> es
  | Emp -> es
  | Event _ -> es
  | Par (es1, es2) -> 
    let es1' = normalConcreteES valuation es1 pi in 
    let es2' = normalConcreteES valuation es2 pi in 

    (match (es1', es2') with 
    | (Emp, _) -> es2'
    | (_, Emp) -> es1'
    | (Bot, Bot) -> Bot
    | (Bot, _) -> es2'
    | (_, Bot) -> es1'
    (*| (Cons (Ttimes (es1, t1), es12), Cons (Ttimes (Emp, t2), es22)) 
    | (Cons (Ttimes (Emp, t2), es22), Cons (Ttimes (es1, t1), es12)) ->
    
      let trace1 =  (Cons (Ttimes (Emp, t2), Par (Cons(Ttimes (es1, (Minus (t1, t2))), es12), es22))) in 
      let trace2 =  Cons (Cons (Ttimes (es1, t1), Ttimes (Emp, (Minus (t2, t1)))), Par (es12, es22)) in 
      
    
      print_string("SYH11: " ^ showPure  pi ^ " ==> "^ showPure (GtEq(t1, t2)) ^ " " ^ string_of_bool ( entailConstrains pi (GtEq(t1, t2))) ^ "\n");
      print_string("SYH12: " ^ showPure  pi ^ " ==> "^ showPure (Lt(t1, t2)) ^ " " ^ string_of_bool ( entailConstrains pi (GtEq(t1, t2))) ^ "\n");

      if entailConstrains pi (GtEq(t1, t2)) then trace1 
      else if entailConstrains pi (Lt(t1, t2)) then trace2
      else ESOr(trace1, trace2)
      
      


    | (Cons (Ttimes (es1, t1), es12), Ttimes (Emp, t2)) 
    | (Ttimes (Emp, t2), Cons (Ttimes (es1, t1), es12)) ->
      let trace1 = (Cons (Ttimes (Emp, t2), Cons(Ttimes (es1, (Minus (t1, t2))), es12))) in 
      let trace2 = Cons (Cons (Ttimes (es1, t1), Ttimes (Emp, (Minus (t2, t1)))), es12)  in 

      print_string("SYH21: " ^ showPure  pi ^ " ==> "^ showPure (GtEq(t1, t2)) ^ " " ^ string_of_bool ( entailConstrains pi (GtEq(t1, t2))) ^ "\n");
      print_string("SYH32: " ^ showPure  pi ^ " ==> "^ showPure (Lt(t1, t2)) ^ " " ^ string_of_bool ( entailConstrains pi (GtEq(t1, t2))) ^ "\n");

    
      if entailConstrains pi (GtEq(t1, t2)) then trace1 
      else if entailConstrains pi (Lt(t1, t2)) then trace2
      else ESOr(trace1, trace2)
    | (Ttimes (_, _), Ttimes (Emp, _)) 
    | (Ttimes (Emp, _), Ttimes (_, _)) -> raise (Foo "par 4")
    | _ -> Par (es1', es2')
    *)
    | _ -> Par (es1', es2')

    
)


  
    (*Guard (pi1, normalConcreteES valuation es1 pi) *)
  | Cons (Cons (esIn1, esIn2), es2)-> normalConcreteES valuation (Cons (esIn1, Cons (esIn2, es2))) pi 
  | Cons (es1, es2) -> 
      let normalES1 = normalConcreteES valuation es1 pi  in
      let normalES2 = normalConcreteES valuation es2 pi  in
      (match (normalES1, normalES2) with 
        (Emp, _) -> normalES2 
      | (_, Emp) -> normalES1
      | (Bot, _) -> Bot
      | (_, Bot) -> Bot

      | (Kleene (esIn1), Kleene (esIn2)) -> 
          if aCompareES esIn1 esIn2 == true then normalES2
          else Cons (normalES1, normalES2)
      | (Kleene (esIn1), Cons(Kleene (esIn2), _)) -> 
          if aCompareES esIn1 esIn2 == true then normalES2
          else Cons (normalES1, normalES2) 

      | (normal_es1, normal_es2) -> 

        Cons (normal_es1, normal_es2)
        
      )

	| ESOr (es1, es2) -> 
      (match (normalConcreteES valuation es1 pi , normalConcreteES valuation es2 pi ) with 
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
      let normalInside = normalConcreteES valuation es1 pi  in 
      Ttimes (normalInside, t) 
  | Kleene es1 -> 
      let normalInside = normalConcreteES valuation es1 pi  in 
      (match normalInside with
      | Emp -> Emp
      | Bot -> Emp
      | Kleene esIn1 ->  Kleene (normalConcreteES valuation esIn1 pi )
      | ESOr(Emp, aa) -> Kleene aa 
      | _ ->  Kleene normalInside)

  | Guard (pi1, es1) -> Guard (pi1, normalConcreteES valuation es1 pi)

;;


let rec postprocessDeleteBar valuation (es:es) : es = 
  match es with
  | Cons ((Event(Tau pi1)), es2) ->
    if entailConstrains (globalVToPure valuation) pi1 
    then es2
    else Bot
  | (Event(Tau pi1)) -> 
    if entailConstrains (globalVToPure valuation) pi1 
    then Emp
    else Bot

  | Cons (Guard (pi1, es1), es2) ->
    if entailConstrains (globalVToPure valuation) pi1 
  (* then derivitive_concrete valuation pi es1 f *)
    then Cons (es1, es2)
    else es
  | Guard (pi1, es1) -> 
    if entailConstrains (globalVToPure valuation) pi1 
  (* then derivitive_concrete valuation pi es1 f *)
    then es1
    else es
  

  | Par (es1, es2) -> 
    Par (postprocessDeleteBar valuation es1, postprocessDeleteBar valuation es2)
  | ESOr(es1, es2) -> 
    ESOr (postprocessDeleteBar valuation es1, postprocessDeleteBar valuation es2)

  | _ -> es 
  ;;


let updateState valuation  (f:head)  : globalV = 
  match f with 
  | Instant (Present(_, _, ops)) 
  | Ev ((Present(_, _, ops)), _) -> 
      updateValuation valuation ops
  | _ -> valuation
  ;;

let rec derivitive_concreteRec valuation (pi :pure) (es:es) (f:headTrace) : (es * pure option) = 
  match f with 
  | [] -> raise (Foo "error derivitive_concreteRec") 
  | [x] -> derivitive_concrete valuation pi es x
  | x :: xs -> 

    let (der1, side1) = derivitive_concrete valuation pi (postprocessDeleteBar valuation (normalConcreteES valuation es pi)) x in 
    let der1 = postprocessDeleteBar valuation der1 in 
    print_string ("=====\nhouhouhou: " ^ (string_of_head x) ^"   "^string_of_globalV valuation ^ "\n");
    print_string (showES es ^ "\n");
    print_string (showES der1 ^ "\n");


    (match side1 with
    | None -> 
      derivitive_concreteRec (updateState valuation x) pi der1 xs 
    | Some side1 ->  derivitive_concreteRec (updateState valuation x) (PureAnd(pi, side1)) der1 xs 
)
and derivitive_concrete valuation (pi :pure) (es:es) (f:head) : (es * pure option) =
  (*print_string ("derivitive_concrete:   " ^ showES es ^ "\n");*)
  match normalES es pi with 
  | Bot -> (Bot, None)
  | Emp -> (Bot, None)


  | Cons(Event (Tau pi1), es1) ->  
    
    if entailConstrains (globalVToPure valuation) pi1 
  (* then derivitive_concrete valuation pi es1 f *)
    then derivitive_concrete valuation pi es1 f 
    else (Bot, None)

  | Event (Tau pi1) ->  
  (*print_string (showES es ^ "\n"); raise (Foo ("derivitive_concrete Tau: " ) );*)
    if entailConstrains (globalVToPure valuation) pi1 
    then (Emp, None)
    else (Bot, None)

  (*| Cons ((Ttimes(es1', t)) , es2) ->  
    let es1 = (Ttimes(es1', t)) in 
    let derList1 = derivitive_concrete valuation pi es1 f in (*  *)
    let longer = List.map (fun (es1_der, side1) -> (Cons(es1_der, es2), side1)) derList1 in 
    longer
    (*if nullable pi es1
      then 
        let temp = derivitive_concrete valuation pi (Cons (es1', es2))  f in 
        let shorter = List.map (fun (a1, a2) -> 
        (a1, Some (optionPureAndHalf  a2 (Eq(t, Number 0))))
        ) temp in
        List.append longer shorter
      else longer
      *)
*)
  | Cons (es1 , es2) ->  
    let (derList1, side ) = derivitive_concrete valuation pi es1 f in (*  *)
    let longer = Cons(derList1, es2) in 
    (*
        let derList2 (**)  = derivitive_concrete valuation pi es2 f in  
    if nullable pi es1
      then 
        let shorter = derList2 in
        List.append longer shorter
        else
        *)
       (longer, side)


  | ESOr (es1, es2) -> 
      let (derList1, side1) = derivitive_concrete valuation pi es1 f in 
      let (derList2, side2) = derivitive_concrete valuation pi es2 f in
      (ESOr(derList1, derList2), optionPureAnd side1 side2)

      (*List.append derList1 derList2*)

  | Kleene es1 -> 
      let (derList, side) = derivitive_concrete valuation pi es1 f in 
      (Cons (derList, es), side)

  | Par (es1, es2) ->
      let helper esIn = 
        let  (derList, side)  = derivitive_concrete valuation pi esIn f in 
          let der = normalES derList pi in 
          match der with 
          | Bot -> (esIn, None)
          | _ -> (der, side)
      in 
      let (derList1, side1) = helper es1 in 
      let (derList2, side2) = helper es2 in 
      let temp =  Par (derList1, derList2) in 
      (*let rec existHead ff ll = 
        match ll with 
        | [] -> false 
        | x::xs -> if String.compare (string_of_head ff) (string_of_head x) == 0 
        then true else   existHead ff xs 
      in 
      *)
      (temp, optionPureAnd side1 side2)

      
  | Guard (pi1, es1) ->
    if entailConstrains (globalVToPure valuation) pi1 
    then derivitive_concrete valuation pi es1 f 
    (*then es1 *)
    else (es, None)
    
    
      
  | Event (Any) -> (Emp, None)

  | Event ev1 -> 
    (*print_string (string_of_head f ^ "   " ^showES (Event ev1) ^ "\n");*)
		(match f with 
		| T  _ -> (Bot, None)
		| Ev (_, _) -> (Bot, None)
		| Instant ev -> if entailEvent ev ev1 then (Emp, None) else (Bot, None)
		)

  | Ttimes (Ttimes (es1, t1) , t2 ) -> 
    let (es1_der, side1) = derivitive_concrete valuation pi (Ttimes (es1, t1)) f in 
    if stricTcompareTerm t1 t2 then (es1_der, side1)
    else 
      (es1_der, Some (optionPureAndHalf side1 (Eq(t1, t2))))

  | Ttimes (Emp, tIn) -> 
		(match f with 
		| T  t -> 
      if stricTcompareTerm t tIn then (Emp, None)
      else (Emp,  Some (Eq(t , tIn)))
		| Ev (_, t2) -> 
      if entailConstrains pi (Lt(t2, tIn)) then (Ttimes (Emp, Minus(tIn, t2)), None)
      else (Bot, None)
		| Instant _ -> (Bot, None)
		)

	| Ttimes (Event ev1, tIn) -> 

		(match f with 
		| T  _ ->  
    (Bot, None)
    (*let t_new = getAfreeVar () in 
      (Ttimes (Event ev1, Var t_new), Some (PureAnd(Eq(Plus (t,Var t_new) , tIn), GtEq (Var t_new, Number 0))))
      *)
		| Ev (ev, t) ->  

      if entailEvent ev ev1 then 
        (if stricTcompareTerm tIn t then (Emp, None)
        else (Emp,Some ( Eq(tIn, t)))) 
      else (Bot, None)

		| Instant ev ->  if entailEvent ev ev1 then (Ttimes (Emp, tIn), None) else (Bot, None)
		)
	
	| Ttimes (es1, tIn) -> 

    raise (Foo ("derivitive_concrete Ttimes (es1, tIn)"));
		(match f with 
		| T  t ->  let t_new = getAfreeVar () in 
      (Ttimes (es1, Var t_new), Some (PureAnd(Eq(Plus (t,Var t_new) , tIn), GtEq (Var t_new, Number 0))))
		| Ev (ev, t) ->  
		  let (es1_der, side1) = derivitive_concrete valuation pi es1 (Instant ev) in 
        (match normalES es1_der pi with 
        | Emp -> if stricTcompareTerm tIn t then (Emp, side1)
          else (Emp, Some (optionPureAndHalf side1 (Eq(tIn, t))))
        | _ -> 
          let t_new = getAfreeVar () in 
          let p_new = optionPureAndHalf side1 (PureAnd(Eq(Plus (t,Var t_new) , tIn), GtEq (Var t_new, Number 0))) in 
          (Ttimes (es1_der, Var t_new), Some p_new)
      )
		
		| Instant _ ->  
        let (es1_der, side1)  = derivitive_concrete valuation pi es1 f in 
          match normalES es1_der pi with 
          | Bot -> (Bot, Some (Eq (tIn, Number 0)))
          | _ -> (Ttimes (es1_der, tIn), side1)

		)

;;




let compareHead h1 h2 : bool =
  match (h1, h2) with 
  | (Instant ev1, Instant ev2) -> compareEvent ev1 ev2 
  |( Ev (ev1, t1), Ev (ev2, t2)) -> compareEvent ev1 ev2  && compareTerm t1 t2 
  | (T t1, T t2) -> compareTerm t1 t2 
  | _ -> false 
  ;;

let rec normalFstSet (li : head list ): (head list) = 
  let rec existHead h hxs = 
    match hxs with 
    | [] -> false 
    | y ::ys -> if compareHead h y then true else existHead h ys
  in
  match li with 
  | [] -> []
  | x ::xs -> if existHead x xs then normalFstSet xs else x :: (normalFstSet xs)
  ;;



let rec updateStateRec valuation (f:headTrace) : globalV = 
  match f with 
  | [] -> valuation
  | x :: xs -> updateStateRec (updateState valuation x) xs 
  ;;






  

let normalConcreteEffect valuation (eff:effect) :effect =
  let final = List.filter (fun (p, es) -> 
  match (p,  es ) with 
  | (_,  Bot) -> false 
  | (Ast.FALSE,  _) -> false  
  | _ -> true 
  ) (List.map (fun (p, es) -> 
      let (es', pi') = normalESUnifyTime es p in 
      let pure_new =  normalPure    (optionPureAndHalf  pi' p) in 
      (pure_new , postprocessDeleteBar valuation (normalConcreteES valuation es' pure_new))) eff) in 
      
  if List.length final == 0 then (
    (*print_string (showEffect eff ^ "\n");raise (Foo ("lallalal")); *)
    [(FALSE, Bot)]
  )
  else final 
  ;;

  


let rec containment_concrete valuation list_Arg (side:pure) (effL:effect) (effR:effect) delta: (binary_tree * bool) = 
  (*
  print_string ("Next State: \n");
  print_string(string_of_globalV valuation^"\n");
*)
  let normalFormL = normalConcreteEffect valuation effL in 
  let normalFormR = normalConcreteEffect valuation effR in
  let showEntail  = showEntailmentEff normalFormL normalFormR (*^ "  ***> " ^ (showPure (normalPure side))*)  in
  
  (*print_string (showEntail ^"\n");
  *)

  if nullableEff  normalFormL  = true &&  (nullableEff normalFormR  = false) then   
    (Node (showEntail ^ showRule DISPROVE,[] ), false)

  else 
    let (finalTress, finalRe) = List.fold_left (fun (accT, accR) (pL, esL) -> 
      let rec iterateRHS (accInT, accInR) li = 
        match li with
        | [] -> (accInT, accInR) 
        | (pR, esR) :: lirest -> 
        let (subtreeIn, reIn) = 

          (*if askZ3 pL == false then (Node (showEntail ^ " [PURE ER LHS] ", []), false) else 
          *)
          if nullable pL esL  = true &&  (nullable  (PureAnd(pL, pR)) esR  = false) then   
            ([Node (showEntail ^ showRule DISPROVE,[] )], false)

          else if List.length delta >=1 && reoccur (esL) (esR) [(List.hd delta)] then 
            (
              
            
              print_string ("Next State: \n");
  print_string(string_of_globalV valuation^"\n");

            print_string("Deadlock: \n" ^ showEntail^ "\n");
            raise (Foo "Deadlock");

            ([Node (showEntail ^ " [Deadlock]",[] )], false))
        
          else if reoccur (esL) (esR) delta (*!delta*) then 
   
            ([Node (showEntail ^ " [REOCCUR]",[] )], true)

          else 
            let fstSet = fst_concrete valuation  pL esL  in
            if List.length (fstSet) == 0 then 
              (* SYH to compute weather rhs is overlapping side 
              if overlapterms pR (normalPure side) == false then ([Node (showEntail ^ " [PROVE]",[] )], true)
              else 
              *)
                (if entailConstrains (PureAnd (pL, side)) (filterOut side pR list_Arg) then 
                  
                  ([Node (showEntail ^ " [PROVE]", [] )], true)
                else 
                  (*print_string(showPure (PureAnd (pL, side)) ^ "==>" ^ showPure (filterOut side pR list_Arg) ^"\n"); *)
                  ([Node (showEntail ^ " [PURE ER] ", [])], false)
                )
            else 
            
            let rec iterateLHSF (accT, accR) (fL:head list) = 
              match fL with 
              | [] -> (accT, accR)
              | f :: iterateLHSFrest -> 

              (*print_string ("Look Inside!!!!"^ "\n");
              print_string(string_of_head f^"\n");

              print_string(string_of_globalV valuation^"\n");*)

              let valuation' = updateState valuation f in 

              (*print_string(string_of_globalV valuation' ^"\n");*)


              let (derL, sideL) = derivitive_concrete valuation pL esL f  in (* (derL, sideL) *)
              let (derR, sideR) = derivitive_concrete valuation pR esR f  in (*  (derR, sideR) *)
              let side' = optionPureAndHalf (optionPureAnd sideL sideR)  side  in 
              let delta' =  ((esL, esR) :: delta) in 

              let (subtree, result) = containment_concrete valuation' list_Arg  side' [(pL, derL)] [(pR, derR)] delta' in 



             (* let rec iteratorDerRHS (accDerT, accDerR) rhsDerList lhsDer : (binary_tree list * bool) = 
                let (derL, sideL) = lhsDer in 
                match rhsDerList with 
                | [] -> (accDerT, accDerR)
                | (derR, sideR) :: rhsDerListrest -> 
                  let side' = optionPureAndHalf (optionPureAnd sideL sideR)  side  in 
                  let (subtreeDer, resultDer) = containment_concrete valuation' list_Arg  side' [(pL, derL)] [(pR, derR)] delta' in 
                  if resultDer == true then ([subtreeDer], resultDer)
                  else iteratorDerRHS (List.append accDerT [subtreeDer], accDerR|| resultDer) rhsDerListrest lhsDer 
              in 

              let rec iteratorDerLHS (accDerT, accDerR) lhsDerList: (binary_tree list * bool) = 
                match lhsDerList with 
                | [] -> (accDerT, accDerR)
                | lhsDer :: lhsDerListrest -> 
                  let (subtreeDer, resultDer) = iteratorDerRHS ([], false) esRDer lhsDer in 
                  if resultDer == false then (subtreeDer, resultDer)
                  else iteratorDerLHS (List.append accDerT subtreeDer, accDerR && resultDer) lhsDerListrest 
              in 
              let (subtree, result) = iteratorDerLHS ([], true) (List.filter (fun (ees, _) -> isBot ees pL == false) esLDer) in 

              *)
              if result == false then ([subtree], result)
              else 
              iterateLHSF (List.append accT [subtree], accR && result) iterateLHSFrest


             in 
            let (subtrees, re) = iterateLHSF ([], true) fstSet in 

            
            ([Node(showEntailmentEff [(pL, esL)] [(pR, esR)] ^ "  ***> " ^ (showPure (normalPure side)) ^ showRule UNFOLD , subtrees)], re)

          in 
        if reIn == true then (subtreeIn, reIn) 
        else iterateRHS (List.append accInT subtreeIn , reIn || accInR) lirest 
      in 
      let (subtree, re) = iterateRHS ([], false) (normalFormR) in 

      (List.append accT subtree , re && accR)
    ) ([], true) normalFormL in 
    if List.length (finalTress) == 1 then 
      (List.hd finalTress, finalRe)
    else 
      (Node (showEntail ^ " [SPLITLHS] ", finalTress), finalRe)

;;

let printReportHelper_concrete valuation (list_parm:param) lhs rhs : (binary_tree * bool) = 
  let renamedLHS = reNameEffect list_parm lhs "l"  in  
  let renamedRHS = reNameEffect list_parm rhs "r"  in 
  let _ = List.map (fun (_, a) -> a) list_parm in 
  containment_concrete  valuation list_parm (Ast.TRUE) (renamedLHS) (renamedRHS)  []  



  ;;

let printReport_concrete (valuation: globalV) (list_parm:param) (lhs:effect) (rhs:effect) :string =
  (*print_string ("Initial State!!!!");
  print_string(string_of_globalV valuation^"\n");
  *)
  let _ = initialise () in 
  let startTimeStamp = Sys.time() in
  let (tree, re) =  printReportHelper_concrete valuation list_parm lhs rhs  in
  let verification_time = "[Verification Time: " ^ string_of_float ((Sys.time() -. startTimeStamp) *. 1000.0) ^ " ms]\n" in
  let _ (*result *) = printTree ~line_prefix:"* " ~get_name ~get_children tree in
  let buffur = ( "===================================="^"\n[Result] " ^(if re then "Succeed\n" else "Fail\n")
   ^verification_time^" \n\n"  (*^ result*))
  in buffur
  ;;

  (*
    print_string (showES es^"\n");
  print_string (showES (ESOr (derivitive_concrete valuation pi es1 f, derivitive_concrete valuation pi es2 f))^"\n");

  raise (Foo (string_of_globalV (!valuationTRS)));

  *)