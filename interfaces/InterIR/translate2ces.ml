

module MM = Map.Make(String);;


type arithop=
   | Add
   | Sub
   | Mult
type relop=
  | GTE
  | GT
  | LTE
  | LT
  | NE
  | EQ
    
type expr=
  Var of string
| Constant of int
| Aexpr of expr * arithop  * expr

type constr=
  | Constr of expr * relop * expr

type nonflatconstr=
  | Atom of constr
  | And of nonflatconstr * nonflatconstr
  | Or of  nonflatconstr * nonflatconstr
  | Not of nonflatconstr
type call=
  { cname: string;
    cargs: expr list;
    crets: expr list
  }
             
type rule=
  { head: call;
   calls: call list;
   constraints: constr list;
   cost: int                     
  }
let print_arithop oc op=
  match op with
   | Add -> Printf.fprintf oc "+"
   | Sub -> Printf.fprintf oc "-"
   | Mult -> Printf.fprintf oc "*"
let print_relop oc op=
  match op with
  | GTE -> Printf.fprintf oc ">="
  | GT -> Printf.fprintf oc ">"
  | LTE -> Printf.fprintf oc "=<"
  | LT -> Printf.fprintf oc "<"
  | NE -> raise (InterIR.Unexpected_value "found neq when printing")
  | EQ -> Printf.fprintf oc "="

let print_name oc name=
  Printf.fprintf oc "'%s'" name

let rec print_with_comma f oc l=
  match l with
    [x] -> f oc x
  | x::xs -> f oc x;
             Printf.fprintf oc ", ";
             print_with_comma f oc xs
  | [] -> ()
let print_list f oc ls=
  Printf.fprintf oc "[";
  print_with_comma f oc ls;
  Printf.fprintf oc "]"

let fix_var_name name=
  Str.global_replace (Str.regexp "[<,>,:,/,(,),\$]") "_" name
let rec print_expr oc expr=
  match expr with
      Var(name) ->Printf.fprintf oc "V%s" (fix_var_name name)
    | Constant(n) -> if(n<0) then
                       Printf.fprintf oc "(0%s)" (string_of_int n)
                     else
                       Printf.fprintf oc "%s" (string_of_int n)
    | Aexpr(lexpr,arithop,rexpr) ->Printf.fprintf oc "(" ;
                                   print_expr oc lexpr;
                                   print_arithop oc arithop;
                                   print_expr oc rexpr;
                                   Printf.fprintf oc ")" 
let print_constr oc constr=
  match constr with
    Constr(lexpr,relop,rexpr)->print_expr oc lexpr;
                               print_relop oc relop;
                               print_expr oc rexpr
                               
let print_head oc {cname; cargs; crets}=  print_name oc cname;
                                          Printf.fprintf oc "(";
                                          print_list print_expr oc cargs;
                                          Printf.fprintf oc ":";
                                          print_list print_expr oc crets;
                                          Printf.fprintf oc ")"
let print_rule oc { head; calls; constraints;cost}=
  Printf.fprintf oc "eq(";
  print_head oc head;
  Printf.fprintf oc ", ";
  Printf.fprintf oc "%d" cost;
  Printf.fprintf oc ", ";
  print_list print_head oc calls;
  Printf.fprintf oc ", ";
  print_list print_constr oc constraints;
  Printf.fprintf oc ")\n "
  
                       
    
let get_block_name funname num=
  funname^(string_of_int num)
            
let get_arith_op op=
  match op with
  | InterIR.Add -> Some(Add)
  | InterIR.Sub -> Some(Sub)
  | InterIR.Mult-> Some(Mult)
  | _->  None


let get_relop cop =
  match cop with
  | InterIR.GTE -> GTE
  | InterIR.GT-> GT
  | InterIR.LTE-> LTE
  | InterIR.LT-> LT
  | InterIR.NE-> NE
  | InterIR.EQ-> EQ
  | _ ->raise (InterIR.Unexpected_value "non-boolean expression in condition")
             

             
let create_initial_map  args=
  let add_initial map arg= MM.add arg 0 map in
  List.fold_left add_initial MM.empty args

let get_map_val map var=
  if(MM.mem var map) then
    (
    let index=MM.find var map in
    if(index=0) then
      var
    else
      var^"_v"^(string_of_int index)
    )else
    var

let increment_map_val map var=
  if(MM.mem var map) then
    let index=MM.find var map in
    MM.add  var (index+1) map
  else
    MM.add  var 0 map

let increment_map_and_return map var=
  if(MM.mem var map) then
    let index=MM.find var map in
    ((MM.add var (index+1)) map, Var(var^"_v"^(string_of_int (index+1))))
  else
    ((MM.add var 0) map, Var(var))
    
let get_var (name,_) =name
let get_var_expr (name,_) =Var(name)
                         
let get_left_side map l=
    match l with
    | InterIR.Var(name,_) -> increment_map_and_return map name
    | _ -> raise (InterIR.Unexpected_value "found something other than a variable on the left side of an assigment")
                  
let get_variable map (name,_)=Var(get_map_val map name)
                                           
let get_lvalue map var=
  match var with
  | InterIR.Var(name,_)-> Var(get_map_val map name)
  | InterIR.Undef ->Var("_")
  | InterIR.FieldAccess(lvalue,field) -> raise (InterIR.Unexpected_value ("Unexpected field access: "^field))

let rec get_rexpr map rexpr =
  match rexpr with
  | InterIR.Constant(value,_) -> Constant(value)
  | InterIR.LVal(lval) -> get_lvalue map lval
  | InterIR.BExpr(lhs,op,rhs)-> (match get_arith_op op with
                          Some(arith_op) -> Aexpr(get_rexpr map lhs,arith_op, get_rexpr map rhs)
                         |None -> Var("_")
                        )
  | InterIR.UExpr(InterIR.UNeg,r) -> Aexpr(Constant(0),Sub,get_rexpr map r)
  | InterIR.UExpr(InterIR.LNeg,_) -> Var("_")
  | InterIR.Multiple(_) -> raise (InterIR.Unexpected_value "Unexpected multiple rexpr ")
                         
let rec get_logical_rexpr map rexpr=
  match rexpr with
  | InterIR.BExpr(lhs,op,rhs)->( match op with
                          InterIR.GTE| InterIR.GT| InterIR.LTE |InterIR.LT |InterIR.NE |InterIR.EQ ->
                                Atom(Constr(get_rexpr map lhs,get_relop op,get_rexpr map rhs))
                          | InterIR.And ->
                             And(get_logical_rexpr map lhs,get_logical_rexpr map rhs)
                          | InterIR.Or ->
                             Or(get_logical_rexpr map lhs,get_logical_rexpr map rhs)
                          | _ ->raise (InterIR.Unexpected_value "Found non-boolean expression in condition")
                       )
  | InterIR.UExpr(InterIR.LNeg,rhs) -> Not (get_logical_rexpr map rhs)
  | _ -> raise (InterIR.Unexpected_value "Found non-boolean expression in condition")

let switch_op cop =
  match cop with
    GTE -> LT
  | GT -> LTE
  | LTE -> GT
  | LT -> GTE
  | NE -> EQ
  | EQ -> NE

let rec negate_logical nonflatexpr=
  match nonflatexpr with
  | Atom(Constr(lhs,op,rhs)) ->Atom(Constr(lhs,switch_op op,rhs))
  | And(lhs,rhs) ->Or(negate_logical lhs,negate_logical rhs)
  | Or(lhs,rhs) ->And(negate_logical lhs,negate_logical rhs)
  | Not(r)-> r

let rec remove_nots nonflatexpr=
    match nonflatexpr with
  | Atom(Constr(lhs,op,rhs)) ->nonflatexpr
  | And(lhs,rhs) ->Or(remove_nots lhs,remove_nots rhs)
  | Or(lhs,rhs) ->And(remove_nots lhs,remove_nots rhs)
  | Not(r)-> negate_logical (remove_nots r)

let combine1 ls r: constr list list=
  List.map (List.append r) ls
let combine ls rs: constr list list=
  List.fold_left combine1 ls  rs 
  
let rec flatten_logical nonflatexpr: constr list list=
  match nonflatexpr with
  | Atom(Constr(lhs,op,rhs)) ->if (op=NE) then
                         [[Constr(lhs,GT,rhs)];[Constr(lhs,LT,rhs)]]
                          else
                            [[Constr(lhs,op,rhs)]]
  | And(lhs,rhs) ->let lsides=flatten_logical lhs in
                   let rsides=flatten_logical rhs in
                   combine lsides rsides
  | Or(lhs,rhs) ->(flatten_logical lhs)@(flatten_logical rhs)
  | _-> raise (InterIR.Unexpected_value "Nots should have gone away by now")
    
let get_cond_constr map cond negate=
  match cond with
    InterIR.Cond(rexpr) ->let nonflat=get_logical_rexpr map rexpr in
                  if negate then 
                    flatten_logical (remove_nots (negate_logical nonflat))
                  else
                    flatten_logical (remove_nots  nonflat)
                    
   |InterIR.NonDet -> [[]]
   |InterIR.Jmp-> [[]]
      
let get_left_side_ls  lhs (map,ls)=
  let map1,var=get_left_side map lhs in
  (map1,var::ls)
        
let  accum_constraints glos (map,calls,constraints,cost) inst=
  match inst with
  | InterIR.Assign(l,r) ->
     let map1,var=get_left_side map l in
     let right= get_rexpr map r in
     (map1,calls, (Constr(var,EQ,right))::constraints,cost)
  | InterIR.Assume(cond) ->(match (get_cond_constr map cond false) with
                      [one] -> (map,calls,one@constraints,cost)
                    | _ -> (map,calls,constraints,cost)
                   )
  | InterIR.Call(rets,f,args) ->let map1,ret_vars=List.fold_right get_left_side_ls  rets (map,[]) in
                        let icall_args=(List.map (get_rexpr map) args)@ (List.map (get_variable map) glos) in
                        (map1,calls@[{cname=f;cargs=icall_args;crets=ret_vars}],constraints,cost)
  | InterIR.Tick(r) ->match get_rexpr map r with
                 Constant(n) ->(map,calls,constraints,cost+n)
               | _ ->raise (InterIR.Unexpected_value "Found non-constant tick")
              

let get_block_if_name funname n=
  "if_"^funname^(string_of_int n)
                  
let create_internal_call map fname args rets=
  let call_args=List.map (fun x-> Var(get_map_val map x)) args in
  {cname=fname;cargs=call_args;crets=rets}

let generate_rule head call constrs=
  {head=head;calls=[call];constraints=constrs;cost=0}
    
let create_if funname ifname args rets dest bcond map=
  let pos_constrs,neg_constrs=match bcond with
      Some(cond) ->(get_cond_constr map cond false,get_cond_constr map cond true)
    | None -> ([[]],[[]])
  in
  let if_head= {cname=ifname;cargs=args;crets=rets} in
  match dest with
    [if_dest;else_dest] ->let call1={cname=get_block_name funname if_dest;cargs=args;crets=rets} in
                          let call2={cname=get_block_name funname else_dest;cargs=args;crets=rets} in
                          (List.map (generate_rule if_head call1) pos_constrs) @ (List.map (generate_rule if_head call2) neg_constrs)
                         
  |  _ ->[]
  

        
let accum_block_rules args rets glos funname (rules,n) { InterIR.bpreds ; InterIR.binsts ; InterIR.btype  ; InterIR.bcond }=
  let initial_map=create_initial_map args in
  let block_name=get_block_name funname n in
  let args_exprs=List.map (fun x ->Var(x)) args in
  let rets_exprs=List.map (fun x ->Var(x)) rets in
  let head= {cname=block_name;cargs=args_exprs;crets=rets_exprs} in
  let final_map,calls,constraints,cost=List.fold_left (accum_constraints glos) (initial_map,[],[],0) binsts in
  match btype with
    InterIR.Branch(dest)->  if (List.length dest)> 1 then
                      let block_if_name=get_block_if_name funname n in
                      let if_rules = create_if funname block_if_name args_exprs rets_exprs dest bcond initial_map in
                      let if_call= create_internal_call final_map block_if_name args rets_exprs in
                      ((({head;calls=(calls@[if_call]);constraints;cost} :: if_rules)@ rules),n+1)
                    else
                      let block_name=get_block_name funname (List.hd dest) in
                      let block_call= create_internal_call final_map block_name args rets_exprs in
                      (({head;calls=(calls@[block_call]);constraints;cost} :: rules),n+1)
  | InterIR.Return(vars) ->({head;calls;constraints=constraints;cost}:: rules, n+1)
let get_expr name=Var(name)

let generate_cfg oc glos { InterIR.funname ; InterIR.fargs  ; InterIR.flocs ; InterIR.fbody  ; InterIR.frets } =
  Printf.fprintf oc "%s%s\n cfg(\n" "%" funname;
  let ret_vars=List.map get_var frets in
  let head_args=(List.map get_var (fargs @ glos))  in
  let flocs_wo_rets= List.filter (fun x ->not (List.mem x frets)) flocs in
  let ext_args=(List.map get_var  (fargs @ flocs_wo_rets @ glos ))  in
  let first_block_name=get_block_name funname 0 in
  let rets_exprs=List.map (fun x ->Var(x)) ret_vars in
  let head={cname=funname;cargs=(List.map get_expr head_args);crets=rets_exprs} in
  let first_call={cname=first_block_name;cargs=(List.map get_expr ext_args);crets=rets_exprs} in
  let (rules,_)=(List.fold_left (accum_block_rules ext_args ret_vars glos funname) ([{head;calls=[first_call];constraints=[];cost=0}],0) (Array.to_list fbody)) in
  print_list print_rule oc  (List.rev rules);
  Printf.fprintf oc ").\n\n"    


                 
let init fname =
  
  let chan = open_in fname in
  let cs_list = Marshal.from_channel chan in
  close_in chan;
  match cs_list with
    [func_list,glos,main] -> List.iter (generate_cfg stdout glos)  func_list
  | _ -> ()

let main () =
  let len = (Array.length Sys.argv) in
  let argv = (Array.sub Sys.argv 1 (len-1)) in (* skip argv0 *)
   init  (Array.get  argv 0)

let _ = main ()
