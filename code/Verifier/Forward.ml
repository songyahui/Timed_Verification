open String
open List
open Ast
open Printf
open Parser
open Lexer
open Pretty
open Rewriting 
open Sys

let verifier_counter: int ref = ref 0;;


let verifier_initialise () = 
  let _ = verifier_counter :=  0 in 
  ()
;;

let verifier_getAfreeVar () :string  =
  let x = "f"^string_of_int (!verifier_counter) in 
  verifier_counter := !verifier_counter + 1;
  x 
;;









let rec printSpec (s:spec ) :string = 
  match s with 
  PrePost (e1, e2) -> "\n[Pre: " ^ showEffect e1 ^ "]\n[Post:"^ showEffect e2 ^"]\n"



let rec input_lines file =
  match try [input_line file] with End_of_file -> [] with
   [] -> []
  | [line] -> (String.trim line) :: input_lines file
  | _ -> failwith "Weird input_line return value"


let rec concatEffEs (eff:effect) p es : effect = 
  List.map (fun (p1, e1) -> ( (PureAnd(p1,p)), Cons (e1, es))) eff
;; 
 

let rec concatEffEff (eff1:effect) (eff2:effect) : effect = 
  List.flatten (List.map (fun (p2, e2) -> concatEffEs eff1 p2 e2) eff2 )
  

      ;;

let rec searchMeth (prog: program) (name:string) : meth option= 
  match prog with 
    [] -> None
  | x::xs -> 
    (match x with 
      Include str -> searchMeth xs name
    | Method (Meth (t, mn , list_parm, PrePost (pre, post), expression)) -> 
      if mn = name then Some (Meth (t, mn , list_parm, PrePost (pre, post), expression))
      else searchMeth xs name 
    | Global _ -> searchMeth xs name  
    )
    ;;




let rec substitutePureWithAgr (pi:pure) (realArg:expression) (formalArg: var):pure = 
  match pi with 
    TRUE -> pi 
  | FALSE ->pi
  | Gt (term, n) ->  Gt (substituteTermWithAgr term realArg formalArg, substituteTermWithAgr n realArg formalArg)
  | Lt (term, n) ->  Lt (substituteTermWithAgr term realArg formalArg, substituteTermWithAgr n realArg formalArg)
  | GtEq (term, n) ->  GtEq (substituteTermWithAgr term realArg formalArg, substituteTermWithAgr n realArg formalArg)
  | LtEq (term, n) ->  LtEq (substituteTermWithAgr term realArg formalArg, substituteTermWithAgr n realArg formalArg)
  | Eq (term, n) ->  Eq (substituteTermWithAgr term realArg formalArg, substituteTermWithAgr n realArg formalArg)
  | PureOr (p1, p2) -> PureOr (substitutePureWithAgr p1 realArg formalArg, substitutePureWithAgr p2 realArg formalArg)
  | PureAnd (p1, p2) -> PureAnd (substitutePureWithAgr p1 realArg formalArg, substitutePureWithAgr p2 realArg formalArg)
  | Neg p -> Neg (substitutePureWithAgr p realArg formalArg)
  ;;




let rec substituteEffWithAgr (eff:effect) (realArg:expression) (formalArg: var):effect = 
  List.map (fun (pi, es) ->  (substitutePureWithAgr pi realArg formalArg, substituteESWithAgr es realArg formalArg)) eff
;;

let substituteEffWithAgrs (eff:effect) (realArgs: expression list) (formal: (_type * var) list ) =
  let realArgs' = List.filter (fun x -> 
                                match x with 
                              | Value (Unit) -> false 
                              | _-> true ) realArgs in 
                              

  let formalArgs = List.map (fun (a, b) -> b) formal in 
  let pairs = List.combine realArgs' formalArgs in 

  let rec subArgOnebyOne (effIn:effect) (pairs:(expression * var ) list): effect = 
    (match pairs with 
      [] -> effIn 
    | (realArg, formalArg):: xs  -> 
      let subThisPair = substituteEffWithAgr effIn realArg formalArg in
      subArgOnebyOne subThisPair xs 
    )
  in subArgOnebyOne eff pairs;;



let checkPrecondition (state:effect) (pre:effect)  = 
  let reverseState =  ( state) in
  let reversePre =  ( pre) in 
  (*check containment*)
  let (result_tree, result) =  Rewriting.printReportHelper reverseState reversePre in 
  let tree = Node (showEntailmentEff reverseState reversePre, [result_tree]) in

  if result == false then 
  let printTree = printTree ~line_prefix:"* " ~get_name ~get_children tree in
  print_string printTree;
  (result, tree)

  else 
  
  (result, tree);;

let condToPure (expr :expression) :pure = 
  match expr with 
    Cond (Variable v, Integer n, "==")  -> Eq (Var v, Number n)
  | Cond (Variable v, Variable n, "==")  -> Eq (Var v, Var n)
  | Cond (Variable v, Integer n, "<=")  -> PureOr(Eq (Var v, Number n),Lt (Var v, Number n))
  | Cond (Variable v, Integer n, ">=")  -> PureOr(Eq (Var v, Number n),Gt (Var v, Number n))
  | Cond (Variable v, Integer n, ">")  -> Gt (Var v, Number n)
  | Cond (Variable v, Integer n, "<")  -> Lt (Var v, Number n)
  | _ -> raise (Foo ("exception in condToPure"^ printExpr expr))
  ;;

(*let concatanateEffEff eff1 eff2 : effect = 
  List.flatten (List.map (fun (p1, es1) -> List.map (fun (p2, es2) -> 
    (PureAnd(p1, p2), Cons (es1, es2))
  ) eff2) eff1)
  ;;
*)

let valueToTerm v : terms =
  match v with 
  | Integer n -> Number n 
  | Variable str -> Var str 
  | _ -> raise (Foo "not yet in valueToTerm ")
  ;;

let condToString (expr :expression) : string = 
  match expr with 
    Cond (Variable v, Integer n, "==")  -> v
  | Cond (Variable v, Variable n, "==")  -> v
  | Cond (Variable v, Integer n, "<=")  -> v
  | Cond (Variable v, Integer n, ">=")  -> v
  | Cond (Variable v, Integer n, ">")  -> v
  | Cond (Variable v, Integer n, "<")  -> v
  | _ -> raise (Foo ("exception in condToString"^ printExpr expr))
  ;;

let relatedToGlobalV (condIf:expression) (prog:program) : bool = 
  let listAssign = List.flatten (List.map (fun a -> 
    match a with 
    | Global (ops, _) ->   [ops]
    | _ -> [] 
  ) prog) in 
  List.exists (fun a -> String.compare a (condToString condIf) == 0 ) listAssign 
  ;;
  
let prependESToEFF es eff = 
  List.map (fun (pi, es1) -> (pi, Cons(es, es1))) eff ;;


let rec verifier (caller:string) (expr:expression) (precondition:effect) (current:effect) (prog: program): effect = 
  match expr with 
  | EventRaise (ev, p, ops) -> List.map (fun (pi, es) -> (pi, Cons (es, Event (Present (ev, p, ops) )))) current
  | Seq (e1, e2) -> 
    let eff1 = verifier caller e1 precondition current prog in 
    verifier caller e2 precondition eff1 prog

  | IfElse (e1, e2, e3) -> 
    let condIf = condToPure e1 in 
    if relatedToGlobalV e1 prog
    then
      List.flatten (
        List.map ( fun (pi_c, es_c) ->
          let eff1 = verifier caller e2 (concatEffEff precondition current) [(pi_c, Event(Tau condIf))] prog in 
          let eff2 = verifier caller e3 (concatEffEff precondition current) [(pi_c, Event(Tau (Neg condIf)))] prog in 
          List.append (prependESToEFF es_c eff1) (prependESToEFF es_c eff2)
  


        ) current
      )



    else  
      let condElse = Neg condIf in 
      let state_C_IF  = addConstrain current condIf in 
      let state_C_ELSE  = addConstrain current condElse in 
      List.append (verifier caller e2 precondition state_C_IF prog) (verifier caller e3 precondition state_C_ELSE prog)

  (*| Assign (v, e) -> verifier caller e precondition current prog  *)
  | Timeout (e, n) -> 
    List.flatten (
      List.map ( fun (pi_c, es_c) -> 
        let eff = verifier caller e (concatEffEff precondition current) [(pi_c, Emp)] prog in 
        let x = verifier_getAfreeVar () in 
        let addABound = List.map (fun (pi, es) -> (Gt(Var x, valueToTerm n), Ttimes(es, Var x))) eff in 
        prependESToEFF es_c addABound
 


      ) current
    )


  | Deadline (e, n) -> 
    List.flatten (
      List.map ( fun (pi_c, es_c) -> 
        let eff = verifier caller e (concatEffEff precondition current) [(pi_c, Emp)] prog in 
        let x = verifier_getAfreeVar () in 
        let addABound = List.map (fun (pi, es) -> (LtEq(Var x, valueToTerm n), Ttimes(es, Var x))) eff in 
        prependESToEFF es_c addABound
 


      ) current
    )


  | Delay n -> 
    let x = verifier_getAfreeVar () in 
    List.map (fun (pi, es) -> (PureAnd(pi, Eq(Var x, valueToTerm n)), Cons (es, Ttimes (Emp, Var x)))) current

  | LocalDel (t, v , e) ->   verifier caller e precondition current prog      
  | Assertion eff ->   
    let his_cur =  (concatEffEff precondition current) in 
    let (result, tree) = checkPrecondition (his_cur) eff in 
    if result == true then current 
    else raise (Foo ("Assertion " ^ showEffect eff ^" does not hold!"))

  | Parallel (e1, e2) -> 
      List.flatten (
        List.map ( fun (pi_c, es_c) ->
          let eff1 = verifier caller e1 (concatEffEff precondition current) [(pi_c, Emp)] prog in 
          let eff2 = verifier caller e2 (concatEffEff precondition current) [(pi_c, Emp)] prog in 
          let pair = List.combine eff1 eff2 in 
          let new_Eff = List.map (fun ((pi1, es1), (pi2, es2)) -> (normalPure (PureAnd (pi1, pi2)), Par (es1, es2))) pair in 

          prependESToEFF es_c new_Eff
  


        ) current
      )

            
  | Call (name, exprList) -> 
    (match searchMeth prog name with 
      None -> 
       if (String.compare name "printf" == 0) then current
       else raise (Foo ("Method: "^ name ^" not defined!"))
    | Some me -> 
      (

        match me with 
          Meth (t, mn , list_parm, PrePost (pre, post), expression) -> 
          
            
            let subPre = substituteEffWithAgrs pre exprList list_parm in 
            let subPost = substituteEffWithAgrs post exprList list_parm in
            
            (*print_string ("======\n");
            print_string (List.fold_left (fun acc a -> acc ^ printExpr a) "" exprList);
            print_string ("\n");
            print_string (List.fold_left (fun acc (_, a) -> acc ^  a) "" list_parm);

            print_string ("\n" ^ showEffect pre^ "\n" ^ showEffect subPre^ "\n\n") ;
            print_string (showEffect post^ "\n" ^ showEffect subPost^ "\n") ;
*)

            let his_cur =  (concatEffEff precondition current) in 

            let (result, tree) = checkPrecondition (his_cur) subPre in 
            (*print_string ((printTree ~line_prefix:"* " ~get_name ~get_children tree));*)
            
            if result == true then 
              (
                (*print_string ("[Precondition holds] when " ^caller ^" is calling " ^ mn ^"\n\n");*)
              let newState = ( (concatEffEff ( current) ( subPost))) in
              newState)
            else 
            
            raise (Foo ("PreCondition does not hold when " ^ caller^" is calling: "^ name ^"!"))
            
      
      )
    )
    
    | GuardE (pi, e1) -> 
      List.flatten (
        List.map ( fun (pi_c, es_c) -> 
        let eff1 = verifier caller e1 (concatEffEff precondition current) [(pi_c, Guard pi)] prog in 
        prependESToEFF es_c eff1

        ) current
      )
    

    | _ -> current
    ;;

let rec extracPureFromPrecondition (eff:effect) :effect = 
  List.map (fun (pi, es) ->  (pi, Emp))eff
;;

let rec verification (decl:(bool * declare)) (prog: program): string = 
  let (isIn, dec) = decl in 
  if isIn == false then ""
  else 
  let startTimeStamp = Sys.time() in
  match dec with 
  | Include str -> ""
  | Global _ -> ""
  | Method (Meth (t, mn , list_parm, PrePost (pre, post), expression)) -> 
    let head = "[Verification for method: "^mn^"]\n"in 
    let precon = "[Precondition: "^(showEffect ( pre)) ^ "]\n" in
    let postcon = "[Postcondition: "^ (showEffect ( post)) ^ "]\n" in 
    let acc =  (verifier mn expression (pre) [(TRUE, Emp)] prog) in 
    let acc' = (normalEffect acc) in 
    
    let accumulated = "[Real Effect: " ^(showEffect acc') ^ "]\n" in 
    (*print_string((showEntailmentEff acc post) ^ "\n") ;*)
    
    (*let varList = (*append*) (getAllVarFromEff acc) (*(getAllVarFromEff post)*) in  
    *)
    let (result_tree, result) =  Rewriting.printReportHelper  (acc') post in 
    let result = "[Result: "^ (if result then "Succeed" else "Fail") ^"]\n" in 
    let verification_time = "[Verification Time: " ^ string_of_float ((Sys.time() -. startTimeStamp) *. 1000.0) ^ " ms]\n" in
    let printTree = printTree ~line_prefix:"* " ~get_name ~get_children result_tree in
    "=======================\n"^ head ^ precon ^ accumulated ^ postcon ^ result ^verification_time^ "\n" ^ printTree ^ "\n" 
    
 ;;

let rec printMeth (me:meth) :string = 
  match me with 
    Meth (t, mn , list_parm, PrePost (pre, post), expression) -> 
    let p = printType t ^ mn^ "(" ^ printParam list_parm ^ ") "^ printSpec (PrePost (pre, post))^"{"^ printExpr expression ^"}\n" in
    p 
    ;;



let rec printProg (pram: declare list) :string =
  match pram with 
    [] -> ""
  | x::xs -> 
    let str = (match x with 
              Include str -> str ^ "\n" 
            | Method me -> printMeth me 
            | Global op -> string_of_assigns [op]
    )in
    str ^ printProg xs ;;

let getIncl (d:declare) :bool = 
  match d with 
    Include str -> (String.compare str "primitives.c") != 0
  | _ -> false 
  ;;



let rec getIncludedFiles (p:(bool * declare) list) :(bool * declare) list = 
  let readFromFile (name:string):(bool * declare) list  = 
    let currentP = split_on_char '/' (Sys.getcwd ()) in 
    let serverOrNot = List.exists (fun a -> String.compare a "cgi-bin" == 0) currentP in 

    let inputfile = if serverOrNot then (Sys.getcwd () ^ "/../src/program/" ^ name) 
                    else (Sys.getcwd () ^ "/src/program/" ^ name) 
    in
    let ic = open_in inputfile in
    try 
      let lines =  (input_lines ic ) in  
      let line = List.fold_right (fun x acc -> acc ^ "\n" ^ x) (List.rev lines) "" in 
      let raw_prog = List.map (fun a -> (false, a)) (Parser.prog Lexer.token (Lexing.from_string line)) in
      let prog = getIncludedFiles raw_prog in 
  
      close_in ic;                  (* 关闭输入通道 *) 
      prog
    with e ->                      (* 一些不可预见的异常发生 *)
      close_in_noerr ic;           (* 紧急关闭 *)
      raise e                      (* 以出错的形式退出: 文件已关闭,但通道没有写入东西 *)
  in 
  let incl = List.filter (fun (ind, x) -> getIncl x) (p) in 
  let getName:(string list ) = List.map (fun (ind, x) -> 
                              match x with 
                              Include str -> str
                            | _ -> "") incl in
  let appendUp  = List.fold_right (fun (x) acc -> append (readFromFile x) acc ) (getName) p in 
 
  appendUp;;


let () =
  let inputfile = (Sys.getcwd () ^ "/" ^ Sys.argv.(1)) in
(*    let outputfile = (Sys.getcwd ()^ "/" ^ Sys.argv.(2)) in
print_string (inputfile ^ "\n" ^ outputfile^"\n");*)
  let ic = open_in inputfile in
  try
      let lines =  (input_lines ic ) in
      let line = List.fold_right (fun x acc -> acc ^ "\n" ^ x) (List.rev lines) "" in
      let raw_prog = List.map (fun a -> (true, a)) (Parser.prog Lexer.token (Lexing.from_string line)) in
      let prog = getIncludedFiles raw_prog in

      
      (*let testprintProg = printProg (List.map (fun (_, a) -> a) raw_prog) in 
      print_string testprintProg; *)

      let evn = List.map (fun (ind, a) -> a) prog in
      let verification_re = List.fold_left (fun acc dec  -> acc ^ (verification dec evn)) "" prog  in
      (*let oc = open_out outputfile in    (* 新建或修改文件,返回通道 *)
      (*      let startTimeStamp = Sys.time() in*)
      (*fprintf oc "%s\n" verification_re;   (* 写一些东西 *)*)
      print_string (verification_re ^"\n");
      (*print_string (string_of_float(Sys.time() -. startTimeStamp)^"\n" );*)
      close_out oc;                (* 写入并关闭通道 *)
      *)
      print_string (verification_re ^"\n");
      flush stdout;                (* 现在写入默认设备 *)
      close_in ic                  (* 关闭输入通道 *)

    with e ->                      (* 一些不可预见的异常发生 *)
      close_in_noerr ic;           (* 紧急关闭 *)
      raise e                      (* 以出错的形式退出: 文件已关闭,但通道没有写入东西 *)

   ;;
