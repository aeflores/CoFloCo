/*
    Copyright (C) 2009  E.Albert, P.Arenas, S.Genaim, G.Puebla, and D.Zanardini
                        https://costa.ls.fi.upm.es

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
*/
:- module(ppl,
[
        ppl_version_major/1,
        ppl_version_minor/1,
        ppl_version_revision/1,
        ppl_version_beta/1,
        ppl_version/1,
        ppl_banner/1,
        ppl_max_space_dimension/1,
        ppl_Coefficient_is_bounded/0,
        ppl_Coefficient_max/1,
        ppl_Coefficient_min/1,
        ppl_initialize/0,
        ppl_finalize/0,
        ppl_set_timeout_exception_atom/1,
        ppl_timeout_exception_atom/1,
        ppl_set_timeout/1,
        ppl_reset_timeout/0,
	ppl_new_C_Polyhedron_from_space_dimension/3,
	ppl_new_NNC_Polyhedron_from_space_dimension/3,
	ppl_new_C_Polyhedron_from_C_Polyhedron/2,
	ppl_new_C_Polyhedron_from_NNC_Polyhedron/2,
	ppl_new_NNC_Polyhedron_from_C_Polyhedron/2,
	ppl_new_NNC_Polyhedron_from_NNC_Polyhedron/2,
	ppl_new_C_Polyhedron_from_constraints/2,
	ppl_new_NNC_Polyhedron_from_constraints/2,
	ppl_new_C_Polyhedron_from_generators/2,
	ppl_new_NNC_Polyhedron_from_generators/2,
	ppl_new_C_Polyhedron_from_bounding_box/2,
	ppl_new_NNC_Polyhedron_from_bounding_box/2,
        ppl_Polyhedron_swap/2,
        ppl_delete_Polyhedron/1,
        ppl_Polyhedron_space_dimension/2,
        ppl_Polyhedron_affine_dimension/2,
        ppl_Polyhedron_get_constraints/2,
        ppl_Polyhedron_get_minimized_constraints/2,
        ppl_Polyhedron_get_generators/2,
        ppl_Polyhedron_get_minimized_generators/2,
        ppl_Polyhedron_relation_with_constraint/3,
        ppl_Polyhedron_relation_with_generator/3,
        ppl_Polyhedron_get_bounding_box/3,
        ppl_Polyhedron_is_empty/1,
        ppl_Polyhedron_is_universe/1,
        ppl_Polyhedron_is_bounded/1,
        ppl_Polyhedron_bounds_from_above/2,
        ppl_Polyhedron_bounds_from_below/2,
        ppl_Polyhedron_maximize/5,
        ppl_Polyhedron_maximize_with_point/6,
        ppl_Polyhedron_minimize/5,
        ppl_Polyhedron_minimize_with_point/6,
        ppl_Polyhedron_is_topologically_closed/1,
        ppl_Polyhedron_contains_Polyhedron/2,
        ppl_Polyhedron_strictly_contains_Polyhedron/2,
        ppl_Polyhedron_is_disjoint_from_Polyhedron/2,
        ppl_Polyhedron_equals_Polyhedron/2,
        ppl_Polyhedron_OK/1,
        ppl_Polyhedron_add_constraint/2,
        ppl_Polyhedron_add_constraint_and_minimize/2,
        ppl_Polyhedron_add_generator/2,
        ppl_Polyhedron_add_generator_and_minimize/2,
        ppl_Polyhedron_add_constraints/2,
        ppl_Polyhedron_add_constraints_and_minimize/2,
        ppl_Polyhedron_add_generators/2,
        ppl_Polyhedron_add_generators_and_minimize/2,
        ppl_Polyhedron_intersection_assign/2,
        ppl_Polyhedron_intersection_assign_and_minimize/2,
        ppl_Polyhedron_poly_hull_assign/2,
        ppl_Polyhedron_poly_hull_assign_and_minimize/2,
        ppl_Polyhedron_poly_difference_assign/2,
        ppl_Polyhedron_affine_image/4,
        ppl_Polyhedron_affine_preimage/4,
        ppl_Polyhedron_bounded_affine_image/5,
        ppl_Polyhedron_bounded_affine_preimage/5,
        ppl_Polyhedron_generalized_affine_image/5,
        ppl_Polyhedron_generalized_affine_preimage/5,
        ppl_Polyhedron_generalized_affine_image_lhs_rhs/4,
        ppl_Polyhedron_generalized_affine_preimage_lhs_rhs/4,
        ppl_Polyhedron_time_elapse_assign/2,
        ppl_Polyhedron_topological_closure_assign/1,
        ppl_Polyhedron_BHRZ03_widening_assign_with_tokens/4,
        ppl_Polyhedron_BHRZ03_widening_assign/2,
        ppl_Polyhedron_limited_BHRZ03_extrapolation_assign_with_tokens/5,
        ppl_Polyhedron_limited_BHRZ03_extrapolation_assign/3,
        ppl_Polyhedron_bounded_BHRZ03_extrapolation_assign_with_tokens/5,
        ppl_Polyhedron_bounded_BHRZ03_extrapolation_assign/3,
        ppl_Polyhedron_H79_widening_assign_with_tokens/4,
        ppl_Polyhedron_H79_widening_assign/2,
        ppl_Polyhedron_limited_H79_extrapolation_assign_with_tokens/5,
        ppl_Polyhedron_limited_H79_extrapolation_assign/3,
        ppl_Polyhedron_bounded_H79_extrapolation_assign_with_tokens/5,
        ppl_Polyhedron_bounded_H79_extrapolation_assign/3,
        ppl_Polyhedron_add_space_dimensions_and_project/2,
        ppl_Polyhedron_add_space_dimensions_and_embed/2,
        ppl_Polyhedron_concatenate_assign/2,
        ppl_Polyhedron_remove_space_dimensions/2,
        ppl_Polyhedron_remove_higher_space_dimensions/2,
        ppl_Polyhedron_expand_space_dimension/3,
        ppl_Polyhedron_fold_space_dimensions/3,
        ppl_Polyhedron_map_space_dimensions/2,
	ppl_new_LP_Problem_trivial/1,
	ppl_new_LP_Problem/4,
	ppl_new_LP_Problem_from_LP_Problem/2,
	ppl_LP_Problem_swap/2,
	ppl_delete_LP_Problem/1,
	ppl_LP_Problem_space_dimension/2,
	ppl_LP_Problem_constraints/2,
	ppl_LP_Problem_objective_function/2,
	ppl_LP_Problem_optimization_mode/2,
	ppl_LP_Problem_clear/1,
	ppl_LP_Problem_add_constraint/2,
	ppl_LP_Problem_add_constraints/2,
	ppl_LP_Problem_set_objective_function/2,
	ppl_LP_Problem_set_optimization_mode/2,
	ppl_LP_Problem_is_satisfiable/1,
	ppl_LP_Problem_solve/2,
	ppl_LP_Problem_feasible_point/2,
	ppl_LP_Problem_optimizing_point/2,
	ppl_LP_Problem_optimal_value/3,
	ppl_LP_Problem_evaluate_objective_function/4,
	ppl_LP_Problem_OK/1
]).

        ppl_version_major(_) :- fail.
        ppl_version_minor(_) :- fail.
        ppl_version_revision(_) :- fail.
        ppl_version_beta(_) :- fail.
        ppl_version(_) :- fail.
        ppl_banner(_) :- fail.
        ppl_max_space_dimension(_) :- fail.
        ppl_Coefficient_is_bounded :- fail.
        ppl_Coefficient_max(_) :- fail.
        ppl_Coefficient_min(_) :- fail.
        ppl_initialize :- fail.
        ppl_finalize :- fail.
        ppl_set_timeout_exception_atom(_) :- fail.
        ppl_timeout_exception_atom(_) :- fail.
        ppl_set_timeout(_) :- fail.
        ppl_reset_timeout :- fail.
	ppl_new_C_Polyhedron_from_space_dimension(_,_,_) :- fail.
	ppl_new_NNC_Polyhedron_from_space_dimension(_,_,_) :- fail.
	ppl_new_C_Polyhedron_from_C_Polyhedron(_,_) :- fail.
	ppl_new_C_Polyhedron_from_NNC_Polyhedron(_,_) :- fail.
	ppl_new_NNC_Polyhedron_from_C_Polyhedron(_,_) :- fail.
	ppl_new_NNC_Polyhedron_from_NNC_Polyhedron(_,_) :- fail.
	ppl_new_C_Polyhedron_from_constraints(_,_) :- fail.
	ppl_new_NNC_Polyhedron_from_constraints(_,_) :- fail.
	ppl_new_C_Polyhedron_from_generators(_,_) :- fail.
	ppl_new_NNC_Polyhedron_from_generators(_,_) :- fail.
	ppl_new_C_Polyhedron_from_bounding_box(_,_) :- fail.
	ppl_new_NNC_Polyhedron_from_bounding_box(_,_) :- fail.
        ppl_Polyhedron_swap(_,_) :- fail.
        ppl_delete_Polyhedron(_) :- fail.
        ppl_Polyhedron_space_dimension(_,_) :- fail.
        ppl_Polyhedron_affine_dimension(_,_) :- fail.
        ppl_Polyhedron_get_constraints(_,_) :- fail.
        ppl_Polyhedron_get_minimized_constraints(_,_) :- fail.
        ppl_Polyhedron_get_generators(_,_) :- fail.
        ppl_Polyhedron_get_minimized_generators(_,_) :- fail.
        ppl_Polyhedron_relation_with_constraint(_,_,_) :- fail.
        ppl_Polyhedron_relation_with_generator(_,_,_) :- fail.
        ppl_Polyhedron_get_bounding_box(_,_,_) :- fail.
        ppl_Polyhedron_is_empty(_) :- fail.
        ppl_Polyhedron_is_universe(_) :- fail.
        ppl_Polyhedron_is_bounded(_) :- fail.
        ppl_Polyhedron_bounds_from_above(_,_) :- fail.
        ppl_Polyhedron_bounds_from_below(_,_) :- fail.
        ppl_Polyhedron_maximize(_,_,_,_,_) :- fail.
        ppl_Polyhedron_maximize_with_point(_,_,_,_,_,_) :- fail.
        ppl_Polyhedron_minimize(_,_,_,_,_) :- fail.
        ppl_Polyhedron_minimize_with_point(_,_,_,_,_,_) :- fail.
        ppl_Polyhedron_is_topologically_closed(_) :- fail.
        ppl_Polyhedron_contains_Polyhedron(_,_) :- fail.
        ppl_Polyhedron_strictly_contains_Polyhedron(_,_) :- fail.
        ppl_Polyhedron_is_disjoint_from_Polyhedron(_,_) :- fail.
        ppl_Polyhedron_equals_Polyhedron(_,_) :- fail.
        ppl_Polyhedron_OK(_) :- fail.
        ppl_Polyhedron_add_constraint(_,_) :- fail.
        ppl_Polyhedron_add_constraint_and_minimize(_,_) :- fail.
        ppl_Polyhedron_add_generator(_,_) :- fail.
        ppl_Polyhedron_add_generator_and_minimize(_,_) :- fail.
        ppl_Polyhedron_add_constraints(_,_) :- fail.
        ppl_Polyhedron_add_constraints_and_minimize(_,_) :- fail.
        ppl_Polyhedron_add_generators(_,_) :- fail.
        ppl_Polyhedron_add_generators_and_minimize(_,_) :- fail.
        ppl_Polyhedron_intersection_assign(_,_) :- fail.
        ppl_Polyhedron_intersection_assign_and_minimize(_,_) :- fail.
        ppl_Polyhedron_poly_hull_assign(_,_) :- fail.
        ppl_Polyhedron_poly_hull_assign_and_minimize(_,_) :- fail.
        ppl_Polyhedron_poly_difference_assign(_,_) :- fail.
        ppl_Polyhedron_affine_image(_,_,_,_) :- fail.
        ppl_Polyhedron_affine_preimage(_,_,_,_) :- fail.
        ppl_Polyhedron_bounded_affine_image(_,_,_,_,_) :- fail.
        ppl_Polyhedron_bounded_affine_preimage(_,_,_,_,_) :- fail.
        ppl_Polyhedron_generalized_affine_image(_,_,_,_,_) :- fail.
        ppl_Polyhedron_generalized_affine_preimage(_,_,_,_,_) :- fail.
        ppl_Polyhedron_generalized_affine_image_lhs_rhs(_,_,_,_) :- fail.
        ppl_Polyhedron_generalized_affine_preimage_lhs_rhs(_,_,_,_) :- fail.
        ppl_Polyhedron_time_elapse_assign(_,_) :- fail.
        ppl_Polyhedron_topological_closure_assign(_) :- fail.
        ppl_Polyhedron_BHRZ03_widening_assign_with_tokens(_,_,_,_) :- fail.
        ppl_Polyhedron_BHRZ03_widening_assign(_,_) :- fail.
        ppl_Polyhedron_limited_BHRZ03_extrapolation_assign_with_tokens(_,_,_,_,_) :- fail.
        ppl_Polyhedron_limited_BHRZ03_extrapolation_assign(_,_,_) :- fail.
        ppl_Polyhedron_bounded_BHRZ03_extrapolation_assign_with_tokens(_,_,_,_,_) :- fail.
        ppl_Polyhedron_bounded_BHRZ03_extrapolation_assign(_,_,_) :- fail.
        ppl_Polyhedron_H79_widening_assign_with_tokens(_,_,_,_) :- fail.
        ppl_Polyhedron_H79_widening_assign(_,_) :- fail.
        ppl_Polyhedron_limited_H79_extrapolation_assign_with_tokens(_,_,_,_,_) :- fail.
        ppl_Polyhedron_limited_H79_extrapolation_assign(_,_,_) :- fail.
        ppl_Polyhedron_bounded_H79_extrapolation_assign_with_tokens(_,_,_,_,_) :- fail.
        ppl_Polyhedron_bounded_H79_extrapolation_assign(_,_,_) :- fail.
        ppl_Polyhedron_add_space_dimensions_and_project(_,_) :- fail.
        ppl_Polyhedron_add_space_dimensions_and_embed(_,_) :- fail.
        ppl_Polyhedron_concatenate_assign(_,_) :- fail.
        ppl_Polyhedron_remove_space_dimensions(_,_) :- fail.
        ppl_Polyhedron_remove_higher_space_dimensions(_,_) :- fail.
        ppl_Polyhedron_expand_space_dimension(_,_,_) :- fail.
        ppl_Polyhedron_fold_space_dimensions(_,_,_) :- fail.
        ppl_Polyhedron_map_space_dimensions(_,_) :- fail.
	ppl_new_LP_Problem_trivial(_) :- fail.
	ppl_new_LP_Problem(_,_,_,_) :- fail.
	ppl_new_LP_Problem_from_LP_Problem(_,_) :- fail.
	ppl_LP_Problem_swap(_,_) :- fail.
	ppl_delete_LP_Problem(_) :- fail.
	ppl_LP_Problem_space_dimension(_,_) :- fail.
	ppl_LP_Problem_constraints(_,_) :- fail.
	ppl_LP_Problem_objective_function(_,_) :- fail.
	ppl_LP_Problem_optimization_mode(_,_) :- fail.
	ppl_LP_Problem_clear(_) :- fail.
	ppl_LP_Problem_add_constraint(_,_) :- fail.
	ppl_LP_Problem_add_constraints(_,_) :- fail.
	ppl_LP_Problem_set_objective_function(_,_) :- fail.
	ppl_LP_Problem_set_optimization_mode(_,_) :- fail.
	ppl_LP_Problem_is_satisfiable(_) :- fail.
	ppl_LP_Problem_solve(_,_) :- fail.
	ppl_LP_Problem_feasible_point(_,_) :- fail.
	ppl_LP_Problem_optimizing_point(_,_) :- fail.
	ppl_LP_Problem_optimal_value(_,_,_) :- fail.
	ppl_LP_Problem_evaluate_objective_function(_,_,_,_) :- fail.
	ppl_LP_Problem_OK(_) :- fail.


