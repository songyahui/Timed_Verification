(*----------------------------------------------------
---------------------DATA STRUCTURE-----------------
----------------------------------------------------*)             

type terms = Var of string
           | Number of int
           | Plus of terms * terms
           | Minus of terms * terms 

(* We use a string to represent an single event *)
type event =  
      | Present of (string * value option * assign list) 
      | Tau of pure 
      | Absent of string 
      | Any 
      
and mn = string
and var = string 
and includ = string 

and head = 
      | Instant of event
      | Ev    of (event * terms) 
      | Tau   of terms 

(*E vent sequence *)
and es = Bot 
        | Emp 
        | Event  of event 
        | Guard  of (pure * es)
        | Cons   of es * es
        | ESOr   of es * es
        | Ttimes of es * terms
        | Par    of es * es 
        | Kleene of es



(*Arithimetic pure formulae*)
and pure = TRUE
          | FALSE
          | Gt of terms * terms
          | Lt of terms * terms
          | GtEq of terms * terms
          | LtEq of terms * terms
          | Eq of terms * terms
          | PureOr of pure * pure
          | PureAnd of pure * pure
          | Neg of pure

(*Effects*)
and effect = (pure * es) list 

and globalV = (string * int) list


and entilment = EE of effect * effect

and spec = PrePost of effect * effect

and _type = INT | FLOAT | BOOL | VOID

and globelV = assign list 

and value = Unit 
| UnitPAR
| Integer of int 
| Bool of bool
| Float of float
| String of string
| Variable of var

and assign =  (var * terms)  


and expression = 
          | Value of value
          | LocalDel of _type * var * expression 
          | Call of mn * expression list 
          | Seq of expression * expression
          | Parallel of expression * expression
          | EventRaise of (string * value option * assign list) 
          | Timeout of (expression * value)  
          | Deadline of (expression * value)
          | Delay of value
          | IfElse of expression * expression * expression
          | Cond of value * value * string
          | BinOp of value * value * string
          | Assertion of effect
          | GuardE of pure * expression

          

and param  = (_type * var) list

and meth = Meth of _type * mn * param * spec * expression

and declare = Include of string | Method of meth | Global of assign

and program = declare list

