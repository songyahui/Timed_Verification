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
      | T     of terms 



(*E vent sequence *)
and es = Bot 
        | Emp 
        | Event  of event 
        | Guard  of pure 
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

and spec = PrePost of effect * (effect list)

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

and condition = value * value * string


and expression = 
          | Value of value
          | LocalDel of _type * var * expression 
          | Call of mn * expression list 
          | Seq of expression * expression
          | IfElse of condition * expression * expression 
          | BinOp of value * value * string
          | Assertion of effect
(* timed related constructs *)
          | Assign of assign
          | GuardE of pure * expression
          | Parallel of expression * expression
          | EventRaise of (string * value option * assign list) 
          | Delay of terms 
          | Deadline of (expression * terms)
          | Timeout of (expression * expression * terms)  
          | Interrupt of (expression * expression * terms)  

          

and param  = (_type * var) list

and meth = Meth of _type * mn * param * spec * expression

and declare = Include of string | Method of meth | Global of assign

and program = declare list

