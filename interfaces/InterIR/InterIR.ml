(* Global types *)

type vtype =
  | Int of int
  | Unknown
  (* | Array of vtype *)
  | Record of string

type variable= (string * vtype)
type lvalue =
  | Var of variable
  | Undef
  | FieldAccess of lvalue * string

type binop =
  | Add
  | Sub
  | Mult
  | Div
  | Rem
  | LShift
  | RShift
  | BXor
  | BAnd
  | BOr
  | And
  | Or
  | GTE
  | GT
  | LTE
  | LT
  | NE
  | EQ

type unop=
  | UNeg
  | LNeg

type rexpr =
  | Constant of int * int
  | LVal of lvalue
  | BExpr of rexpr * binop * rexpr
  | UExpr of unop * rexpr
  | Multiple of rexpr list

type cond = Cond of rexpr | NonDet | Jmp


(* Control flow graphs for CS IR *)

type branch =
  | Branch of int list
  | Return of variable list

type inst =
  | Assign of lvalue * rexpr
  | Call of lvalue list * string * rexpr list
  | Tick of rexpr
  | Assume of cond

type bblock =
  { bpreds: int list
  ; binsts: inst list
  ; btype: branch
  ; bcond: cond option
  }


(* Functions *)

type func =
  { funname: string
  ; fargs: variable list
  ; flocs: variable list
  ; fbody: bblock array
  ; frets: variable list
  }

exception Unexpected_value of string

let is_relational_op =function
  | GTE | GT| LTE | LT| NE | EQ -> true
  | _ ->false

let is_logical_op =function
  | And | Or -> true
  | _ ->false

let rec rexpr_has_boolean_type rexpr=
  match rexpr with
    BExpr(lhs,op,rhs)-> if(is_relational_op op) then
                          true
                        else
                          if(is_logical_op op) then
                            (rexpr_has_boolean_type lhs) && (rexpr_has_boolean_type rhs)
                          else
                            false
  | _ -> false

let check_rexpr_type rexpr=
  match rexpr with
    BExpr(lhs,op,rhs) -> if(is_logical_op op) then
                           rexpr_has_boolean_type rexpr
                         else
                           true
  | _ -> true
