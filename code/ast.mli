(*----------------------------------------------------
---------------------DATA STRUCTURE-----------------
----------------------------------------------------*)             

type terms = Var of string
           | Number of int
           | Plus of terms * terms
           | Minus of terms * terms 

(* We use a string to represent an single event *)
type event =  Present of string | Absent of string | Any 
type mn = string
type var = string 
type includ = string 

type head = 
      | Instant of event
      | Ev    of (event * terms) 
      | Tau   of terms 

(*E vent sequence *)
type es = Bot 
        | Emp 
        | Event  of event 
        | Cons   of es * es
        | ESOr   of es * es
        | Ttimes of es * terms
        | Par    of es * es 
        | Kleene of es



(*Arithimetic pure formulae*)
type pure = TRUE
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
type effect = (pure * es) list 


type entilment = EE of effect * effect

type spec = PrePost of effect * effect

type _type = INT | FLOAT | BOOL | VOID


type value = Unit 
| Integer of int 
| Bool of bool
| Float of float
| String of string
| Variable of var

type assign =  (var * value)  


type expression = 
          | Value of value
          | LocalDel of _type * var * expression 
          | Call of mn * expression list 
          | Seq of expression * expression
          | EventRaise of (string * value option * assign list) 
          | Timeout of (expression * int)  
          | Deadline of (expression * int)
          | Delay of int
          | IfElse of expression * expression * expression
          | Cond of value * value * string
          | BinOp of value * value * string
          | Assertion of effect

type param  = (_type * var) list

type meth = Meth of _type * mn * param * spec * expression

type declare = Include of string | Method of meth | Global of assign

type program = declare list

