(*
open String
open List

open Pretty
*)
open Ast
open Forward

let string_of_concrete_effect _: string = ""

  ;;


let concrete_verify startTimeStamp (auguments) (prog: concrete_prog): string = 
  let (_, mn , list_parm, CPrePost (pre, post), expression) = auguments in 
  let head = "[Verification for method: "^mn^"]\n"in 
    let precon = "[Precondition: "^(string_of_concrete_effect (pre)) ^ "]\n" in
    let postcon = "[Postcondition: "^ (string_of_concrete_effect ( post)) ^ "]\n" in 
    ""
    (*let start = pre in 
    let acc =  (verifier mn list_parm expression (pre) start prog) in 
    let forward_time = "[Forward Time: " ^ string_of_float ((Sys.time() -. startTimeStamp) *. 1000.0) ^ " ms]\n" in
    let acc' = List.map (fun (pi, es) -> (normalPureDeep pi, es)) (normalEffect acc) in 
    
    let accumulated = "[Real Effect: " ^(showEffect acc') ^ "]\n" in 
    let (result) =  printReport_concrete (getGlobelDeclear prog) acc' (List.hd post) in 
    "=======================\n"^ head ^ precon ^ accumulated ^ postcon ^ forward_time ^ result ^ "\n" 
    *)
  
  ;;

  let concrete_verification (decl:(bool * concrete_declare)) (prog: concrete_prog): string = 
    let (isIn, dec) = decl in 
    if isIn == false then ""
    else 
    let startTimeStamp = Sys.time() in
    match dec with 
    | CInclude _ -> ""
    | CGlobal _ -> ""
    | CMethod (CMeth (t, mn , list_parm, CPrePost (pre, post), expression)) -> 
      concrete_verify startTimeStamp (t, mn , list_parm, CPrePost (pre, post), expression) prog 

   ;;
  



let () =
  let inputfile = (Sys.getcwd () ^ "/" ^ Sys.argv.(1)) in
  let ic = open_in inputfile in
  try
      let lines =  (input_lines ic ) in
      let line = List.fold_right (fun x acc -> acc ^ "\n" ^ x) (List.rev lines) "" in
      let raw_prog = List.map (fun a -> (true, a)) (Parser.concrete_prog Lexer.token (Lexing.from_string line)) in
      let prog = raw_prog in

      let evn = List.map (fun (_, a) -> a) prog in
      let verification_re = List.fold_left (fun acc dec  -> acc ^ (concrete_verification dec evn)) "" prog  in

      print_string (verification_re ^"\n");
      
      

      

      flush stdout;                (* 现在写入默认设备 *)
      close_in ic                  (* 关闭输入通道 *)

    with e ->                      (* 一些不可预见的异常发生 *)
      close_in_noerr ic;           (* 紧急关闭 *)
      raise e                      (* 以出错的形式退出: 文件已关闭,但通道没有写入东西 *)

   ;;
