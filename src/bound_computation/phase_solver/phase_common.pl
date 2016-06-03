:- module(phase_common,[
	is_zero/1,
	get_difference_version/4,
	get_difference_version_aux/4,
	le_print_int/3,
	get_constr_op/2,
	select_important_variables/3,
	put_inside_mult/2,
	is_head_expression/2,
	print_lin_exp_in_phase/3
	]).
	
:- use_module(stdlib(linear_expression),[
			integrate_le/3,
			write_le/2,
			multiply_le/3,
			semi_normalize_le/3,
			subtract_le/3,
			negate_le/2]).	
:- use_module(stdlib(set_list)).
:-use_module(library(apply_macros)).
:-use_module(library(lists)).				
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% general auxiliary predicates

is_zero(0).
is_zero(0/1).

get_difference_version_aux(Head,Rf,Call,Rf_diff):-
	copy_term((Head,Rf),(Call,Rfp)),
	subtract_le(Rf,Rfp,Rf_diff).
	
get_difference_version(Head,Call,Rf,Rf_diff):-
	copy_term((Head,Rf),(Call,Rfp)),
	subtract_le(Rf,Rfp,Rf_diff).		
	
le_print_int(Lin_exp,Exp,Den):-
		integrate_le(Lin_exp,Den,Lin_exp_nat),
		write_le(Lin_exp_nat,Exp).
get_constr_op(max,ub).
get_constr_op(min,lb).	

select_important_variables(Vars_head,Lin_exp,Vars_of_Interest):-
	from_list_sl(Vars_head,Vars_head_set),
	term_variables(Lin_exp,Vars_exp),
	from_list_sl(Vars_exp,Vars_exp_set),
	difference_sl(Vars_head_set,Vars_exp_set,Vars_of_Interest).
	
put_inside_mult(Factor,mult([Factor])).

				
is_head_expression(Head,Exp):-
	copy_term((Head,Exp),(Head2,Exp2)),
	numbervars(Head2,0,_),
	ground(Exp2).
	
% debugging predicates 
print_lin_exp_in_phase(Head,Calls,Exp):-
	copy_term((Head,Calls,Exp),(Head2,Calls2,Exp2)),
	write_le(Exp2,Exp_print),
	numbervars((Head2,Calls2),0,_),
	format('~p -> ~p : ~p ~n',[Head2,Calls2,Exp_print]).

