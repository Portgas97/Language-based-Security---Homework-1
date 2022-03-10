(******************************************************************************************)
(*************************************    HOMEWORK    *************************************)
(*************************************       1        *************************************)
(******************************************************************************************)


(* 
  An environment is a map from identifier to a value (what the identifier is bound to).
  For simplicity we represent the environment as an association list, i.e., a list of pair (identifier, data)
  in which the value is polymorphic.
*)
type 'v env = (string * 'v) list;;

(*
  Given an environment {env} and an identifier {x} it returns the data {x} is bound to.
  If there is no binding, it raises an exception.
*)
let rec lookup env x =
  match env with
  | []        -> failwith (x ^ " not found")
  | (y, v)::r -> if x=y then v else lookup r x;;


(* types of possible permissions, placeholder *)
type permission =
  | P_Read
  | P_Send
  | P_Write
  | P_Open
  | P_Close;;
 

(* permission set of a single function *)
(* ASSUMPTION: The programmer-supplied list of permissions has no duplicates *)
type permissionList = (permission) list;;


type permissionStack = (permissionList) list;;



(* Stack of PermissionList to be passed around during function instancing *)

(* Defining the expressions *)
type expr =
  | CstI of int (* primitive numeric value *)
  | CstB of bool (* primitive numeric value *)
  | Var of string (* identifiers in the program*)
  | Let of string * expr * expr (* variable to define, expr for the value, let body *)
  | Prim of string * expr * expr (* operator, operand, operand *)
  | If of expr * expr * expr (* guard, then, else*)
  | Fun of string * expr * permissionList (* anonymous function. It takes an argument, a body and a list of permissions *)
  | Call of expr * expr (* function, argument *)
  | Read of string
  | Write of string
  | Send of expr * string;;


(* Intermediate representation: expressions extended with Abort routine and global state manipulation *)
type iexpr =
  | CstI of int
  | CstB of bool
  | Var of string
  | Let of string * iexpr * iexpr
  | Prim of string * iexpr * iexpr
  | If of iexpr * iexpr * iexpr
  | Fun of string * iexpr * permissionList
  | Call of iexpr * iexpr
  | Read of string
  | Write of string
  | Send of iexpr * string
  | Abort of string
  | GLet of iexpr * iexpr
  | GVar;;
 

type ivalue =
  | Int of int
  (* 
  Arguments of Clusure: formal parameter, body of the function, the environment at the moment of the declaration 
  (in which we will look for the non-local references) 
  *)
  | Closure of string * iexpr * permissionList * ivalue env;; 
 

type gstate = GState of int;;


(* 
  this method checks if a given function has the neededPermission in its permission list
   do not be confused, this checks only for a single function, and does not stackwalk
*) 
let rec checkPermission permissionList neededPermission = 
  match permissionList with
  | [] -> false
  | y::r -> if y = neededPermission then true else checkPermission r neededPermission;;
 

(*
  Stackwalking method to check permissions on all functions in call stack
*)
let rec stackWalking permissionStack neededPermission =
  match permissionStack with
  | [] -> true
  | y::r -> if checkPermission y neededPermission then stackWalking r neededPermission else false;;
 


let rec ieval (e : iexpr) (env : ivalue env) (g : gstate) (pStack: permissionStack): ivalue * gstate  =
  match e with
  | CstI i -> (Int i, g)
  | CstB b -> (Int (if b then 1 else 0), g)
  | Var x  -> (lookup env x, g)
  | Prim(ope, e1, e2) ->
      let (v1, g') = ieval e1 env g pStack in
      let (v2, g'') = ieval e2 env g' pStack in
      begin
        match (ope, v1, v2) with
        | ("*", Int i1, Int i2) -> (Int (i1 * i2), g'')
        | ("+", Int i1, Int i2) -> (Int (i1 + i2), g'')
        | ("-", Int i1, Int i2) -> (Int (i1 - i2), g'')
        | ("=", Int i1, Int i2) -> (Int (if i1 = i2 then 1 else 0), g'')
        | ("<", Int i1, Int i2) -> (Int (if i1 < i2 then 1 else 0), g'')
        |  _ -> failwith "unknown primitive or wrong type"
      end
  | Let(x, eRhs, letBody) ->
      let (xVal, g') = ieval eRhs env g pStack in
      let letEnv = (x, xVal) :: env in (* new envirornment *)
        ieval letBody letEnv g' pStack
  | If(e1, e2, e3) ->
      begin
        match ieval e1 env g pStack with (* not eager *)
        | (Int 0, g') -> ieval e3 env g' pStack (* else branch*)
        | (Int _, g') -> ieval e2 env g' pStack (* then branch*)
        | _     -> failwith "eval If" (* no int value, error *)
      end
  | Fun(x,fBody,permList) -> (Closure(x, fBody, permList, env), g) (* extended with the permission list *)
  | Call(eFun, eArg) ->
      let (fClosure, _) = ieval eFun env g pStack in
      begin
        match fClosure with
        | Closure (x, fBody, fDeclPermList, fDeclEnv) ->
            let (xVal, g') = ieval eArg env g pStack in
            let fBodyEnv = (x, xVal) :: fDeclEnv in (* extends the environment of the declaration, static scope *)
            let fDeclPermStack = fDeclPermList::pStack
            in ieval fBody fBodyEnv g' fDeclPermStack
        | _ -> failwith "eval Call: not a function"
      end
  | Read(_) -> if stackWalking pStack P_Read then (Int 0, g) else failwith("No Read permission on stack")
  | Write(_) -> if stackWalking pStack P_Write then (Int 0, g) else failwith("No Read permission on stack")
  | Send(x, _) -> if stackWalking pStack P_Send then let (_, g') = ieval x env g pStack in (Int 1, g') else failwith("No Send permission on stack")
  | Abort msg -> failwith msg
  | GLet(letVal, letBody) -> let (xVal, _) = ieval letVal env g pStack
      in begin match xVal with 
        | Int(i) -> ieval letBody env (GState i) pStack
        | _ -> failwith "eval Call: not an integer"
      end
  | GVar -> begin match g with
      | GState(i) -> (Int(i), g)
    end;;
   
   
type state = int;;

type symbol = iexpr;;

(* (s0, s1, delta, msg) *)
type nfa = state * state * (state * symbol -> state option) * string;;

(* type 'a option = None | Some of 'a;; *)


let inlineNfa (s0, s1, delta, msg) e = 
  If(Prim("=", GVar, CstI s0), 
     begin match (delta(s0,e)) with 
       | Some s -> GLet(CstI s, e)
       | None -> Abort(msg)
     end, 
     begin match (delta(s1,e)) with 
       | Some s -> GLet(CstI s, e)
       | None -> Abort(msg)
     end)


let rec comp (sa : nfa) (p : expr) : iexpr = match p with
  | CstI i -> CstI i
  | CstB b -> CstB b
  | Var x -> inlineNfa sa (Var x)
  | Prim(ope, e1, e2) -> inlineNfa sa (Prim(ope, (comp sa e1), (comp sa e2)))
  | Let(x, e1, e2) -> Let(x, (comp sa e1), (comp sa e2))
  | If(e1, e2, e3) -> inlineNfa sa (If((comp sa e1), (comp sa e2), (comp sa e3)))
  | Fun(x, e, pStack) -> Fun(x, (comp sa e), pStack)
  | Call(f, a) -> inlineNfa sa (Call((comp sa f), (comp sa a)))
  | Read s -> inlineNfa sa (Read s)
  | Write s -> inlineNfa sa (Write s)
  | Send(e, s) -> inlineNfa sa (Send((comp sa e), s));;


let eval (e : expr) (env : ivalue env) (sa : nfa) (pStack: permissionStack): ivalue = match sa with 
  | (initialState, _, _, _) -> let (result, _) = ieval (comp sa e) env (GState initialState) pStack in result;;

(* We won't be implementing the EM again. This is simply here to show the whole mechanism is still around *)


let myDelta (s, e) = match (s, e) with
	| (0, Read _) -> Some 1
	| (0, _) -> Some 0
	| (1, Send(_, _)) -> None 
	| (1, _) -> Some 1
	| _ -> None;;
	

let mySa = (0, 1, myDelta, "send after read detected");;
  

(* our test cases *) 
let goodTest : expr = Let("f", Fun("x", Let("g", Fun("y",Read("test"),[P_Write;P_Read]), Call(Var "g", Write("test"))), [P_Write;P_Read]), Call(Var "f", CstI(0)));;


(* always returns 0 *)
eval goodTest [] mySa [];;


(* counterexample *)
let badTest : expr = Let("f", Fun("x", Let("g", Fun("y",Read("test"),[P_Write;P_Read]), Call(Var "g", Write("test"))), [P_Read]), Call(Var "f", CstI(0)));;


(* always fails *)
eval badTest [] mySa [];;

