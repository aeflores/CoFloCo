/* Loader for the SWI-Prolog interface.
   Copyright (C) 2001-2010 Roberto Bagnara <bagnara@cs.unipr.it>

This file is part of the Parma Polyhedra Library (PPL).

The PPL is free software; you can redistribute it and/or modify it
under the terms of the GNU General Public License as published by the
Free Software Foundation; either version 3 of the License, or (at your
option) any later version.

The PPL is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
for more details.

You should have received a copy of the GNU General Public License
along with this program; if not, write to the Free Software Foundation,
Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02111-1307, USA.

For the most up-to-date information see the Parma Polyhedra Library
site: http://www.cs.unipr.it/ppl/ . */

:- module(ppl,
[
	  ppl_version_major/1,
	  ppl_version_minor/1,
	  ppl_version_revision/1,
	  ppl_version_beta/1,
	  ppl_version/1,
	  ppl_banner/1,
	  ppl_max_space_dimension/1,
	  ppl_Coefficient_bits/1,
	  ppl_Coefficient_is_bounded/0,
	  ppl_Coefficient_max/1,
	  ppl_Coefficient_min/1,
	  ppl_initialize/0,
	  ppl_finalize/0,
	  ppl_set_rounding_for_PPL/0,
	  ppl_restore_pre_PPL_rounding/0,
	  ppl_irrational_precision/1,
	  ppl_set_irrational_precision/1,
	  ppl_set_timeout_exception_atom/1,
	  ppl_timeout_exception_atom/1,
	  ppl_set_timeout/1,
	  ppl_reset_timeout/0,
	  ppl_reset_deterministic_timeout/0,
	  ppl_new_MIP_Problem_from_space_dimension/2,
	  ppl_new_MIP_Problem/5,
	  ppl_new_MIP_Problem_from_MIP_Problem/2,
	  ppl_MIP_Problem_swap/2,
	  ppl_delete_MIP_Problem/1,
	  ppl_MIP_Problem_space_dimension/2,
	  ppl_MIP_Problem_integer_space_dimensions/2,
	  ppl_MIP_Problem_constraints/2,
	  ppl_MIP_Problem_objective_function/2,
	  ppl_MIP_Problem_optimization_mode/2,
	  ppl_MIP_Problem_clear/1,
	  ppl_MIP_Problem_add_space_dimensions_and_embed/2,
	  ppl_MIP_Problem_add_to_integer_space_dimensions/2,
	  ppl_MIP_Problem_add_constraint/2,
	  ppl_MIP_Problem_add_constraints/2,
	  ppl_MIP_Problem_set_objective_function/2,
	  ppl_MIP_Problem_set_optimization_mode/2,
	  ppl_MIP_Problem_set_control_parameter/2,
	  ppl_MIP_Problem_get_control_parameter/3,
	  ppl_MIP_Problem_is_satisfiable/1,
	  ppl_MIP_Problem_solve/2,
	  ppl_MIP_Problem_feasible_point/2,
	  ppl_MIP_Problem_optimizing_point/2,
	  ppl_MIP_Problem_optimal_value/3,
	  ppl_MIP_Problem_evaluate_objective_function/4,
	  ppl_MIP_Problem_OK/1
,
	  ppl_MIP_Problem_ascii_dump/1,
	  ppl_new_PIP_Problem_from_space_dimension/2,
	  ppl_new_PIP_Problem/4,
	  ppl_new_PIP_Problem_from_PIP_Problem/2,
	  ppl_PIP_Problem_swap/2,
	  ppl_delete_PIP_Problem/1,
	  ppl_PIP_Problem_space_dimension/2,
	  ppl_PIP_Problem_parameter_space_dimensions/2,
	  ppl_PIP_Problem_constraints/2,
	  ppl_PIP_Problem_clear/1,
	  ppl_PIP_Problem_add_space_dimensions_and_embed/3,
	  ppl_PIP_Problem_add_to_parameter_space_dimensions/2,
	  ppl_PIP_Problem_add_constraint/2,
	  ppl_PIP_Problem_add_constraints/2,
	  ppl_PIP_Problem_set_control_parameter/2,
	  ppl_PIP_Problem_get_control_parameter/3,
	  ppl_PIP_Problem_has_big_parameter_dimension/2,
	  ppl_PIP_Problem_set_big_parameter_dimension/2,
	  ppl_PIP_Problem_is_satisfiable/1,
	  ppl_PIP_Problem_solve/2,
	  ppl_PIP_Problem_solution/2,
	  ppl_PIP_Problem_optimizing_solution/2,
	  ppl_PIP_Problem_OK/1,
	  ppl_PIP_Problem_ascii_dump/1,
	  ppl_PIP_Tree_Node_constraints/2,
	  ppl_PIP_Tree_Node_is_solution/1,
	  ppl_PIP_Tree_Node_is_decision/1,
	  ppl_PIP_Tree_Node_is_bottom/1,
	  ppl_PIP_Tree_Node_artificials/2,
	  ppl_PIP_Tree_Node_OK/1,
	  ppl_PIP_Tree_Node_parametric_values/3,
	  ppl_PIP_Tree_Node_true_child/2,
	  ppl_PIP_Tree_Node_false_child/2,
	  ppl_delete_Polyhedron/1


,
	  ppl_new_C_Polyhedron_from_space_dimension/3,
	  ppl_new_NNC_Polyhedron_from_space_dimension/3



,
	  ppl_new_C_Polyhedron_from_C_Polyhedron/2,
	  ppl_new_NNC_Polyhedron_from_C_Polyhedron/2,
	  ppl_new_C_Polyhedron_from_NNC_Polyhedron/2,
	  ppl_new_NNC_Polyhedron_from_NNC_Polyhedron/2,
	  ppl_new_C_Polyhedron_from_Grid/2,
	  ppl_new_NNC_Polyhedron_from_Grid/2,
	  ppl_new_C_Polyhedron_from_Rational_Box/2,
	  ppl_new_NNC_Polyhedron_from_Rational_Box/2,
	  ppl_new_C_Polyhedron_from_BD_Shape_mpz_class/2,
	  ppl_new_NNC_Polyhedron_from_BD_Shape_mpz_class/2,
	  ppl_new_C_Polyhedron_from_BD_Shape_mpq_class/2,
	  ppl_new_NNC_Polyhedron_from_BD_Shape_mpq_class/2,
	  ppl_new_C_Polyhedron_from_Octagonal_Shape_mpz_class/2,
	  ppl_new_NNC_Polyhedron_from_Octagonal_Shape_mpz_class/2,
	  ppl_new_C_Polyhedron_from_Octagonal_Shape_mpq_class/2,
	  ppl_new_NNC_Polyhedron_from_Octagonal_Shape_mpq_class/2,
	  ppl_new_C_Polyhedron_from_Double_Box/2,
	  ppl_new_NNC_Polyhedron_from_Double_Box/2,
	  ppl_new_C_Polyhedron_from_BD_Shape_double/2,
	  ppl_new_NNC_Polyhedron_from_BD_Shape_double/2,
	  ppl_new_C_Polyhedron_from_Octagonal_Shape_double/2,
	  ppl_new_NNC_Polyhedron_from_Octagonal_Shape_double/2




,
	  ppl_new_C_Polyhedron_from_C_Polyhedron_with_complexity/3,
	  ppl_new_NNC_Polyhedron_from_C_Polyhedron_with_complexity/3,
	  ppl_new_C_Polyhedron_from_NNC_Polyhedron_with_complexity/3,
	  ppl_new_NNC_Polyhedron_from_NNC_Polyhedron_with_complexity/3,
	  ppl_new_C_Polyhedron_from_Grid_with_complexity/3,
	  ppl_new_NNC_Polyhedron_from_Grid_with_complexity/3,
	  ppl_new_C_Polyhedron_from_Rational_Box_with_complexity/3,
	  ppl_new_NNC_Polyhedron_from_Rational_Box_with_complexity/3,
	  ppl_new_C_Polyhedron_from_BD_Shape_mpz_class_with_complexity/3,
	  ppl_new_NNC_Polyhedron_from_BD_Shape_mpz_class_with_complexity/3,
	  ppl_new_C_Polyhedron_from_BD_Shape_mpq_class_with_complexity/3,
	  ppl_new_NNC_Polyhedron_from_BD_Shape_mpq_class_with_complexity/3,
	  ppl_new_C_Polyhedron_from_Octagonal_Shape_mpz_class_with_complexity/3,
	  ppl_new_NNC_Polyhedron_from_Octagonal_Shape_mpz_class_with_complexity/3,
	  ppl_new_C_Polyhedron_from_Octagonal_Shape_mpq_class_with_complexity/3,
	  ppl_new_NNC_Polyhedron_from_Octagonal_Shape_mpq_class_with_complexity/3,
	  ppl_new_C_Polyhedron_from_Double_Box_with_complexity/3,
	  ppl_new_NNC_Polyhedron_from_Double_Box_with_complexity/3,
	  ppl_new_C_Polyhedron_from_BD_Shape_double_with_complexity/3,
	  ppl_new_NNC_Polyhedron_from_BD_Shape_double_with_complexity/3,
	  ppl_new_C_Polyhedron_from_Octagonal_Shape_double_with_complexity/3,
	  ppl_new_NNC_Polyhedron_from_Octagonal_Shape_double_with_complexity/3




,
	  ppl_new_C_Polyhedron_from_constraints/2,
	  ppl_new_NNC_Polyhedron_from_constraints/2,
	  ppl_new_C_Polyhedron_from_congruences/2,
	  ppl_new_NNC_Polyhedron_from_congruences/2,
	  ppl_new_C_Polyhedron_from_generators/2,
	  ppl_new_NNC_Polyhedron_from_generators/2




,
	  ppl_Polyhedron_swap/2


,
	  ppl_Polyhedron_space_dimension/2,
	  ppl_Polyhedron_affine_dimension/2



,
	  ppl_Polyhedron_relation_with_constraint/3,
	  ppl_Polyhedron_relation_with_generator/3,
	  ppl_Polyhedron_relation_with_congruence/3



,
	  ppl_Polyhedron_get_constraints/2,
	  ppl_Polyhedron_get_congruences/2,
	  ppl_Polyhedron_get_generators/2



,
	  ppl_Polyhedron_get_minimized_constraints/2,
	  ppl_Polyhedron_get_minimized_congruences/2,
	  ppl_Polyhedron_get_minimized_generators/2



,
	  ppl_Polyhedron_is_empty/1,
	  ppl_Polyhedron_is_universe/1,
	  ppl_Polyhedron_is_bounded/1,
	  ppl_Polyhedron_contains_integer_point/1,
	  ppl_Polyhedron_is_topologically_closed/1,
	  ppl_Polyhedron_is_discrete/1



,
	  ppl_Polyhedron_topological_closure_assign/1



,
	  ppl_Polyhedron_bounds_from_above/2,
	  ppl_Polyhedron_bounds_from_below/2



,
	  ppl_Polyhedron_maximize/5,
	  ppl_Polyhedron_minimize/5



,
	  ppl_Polyhedron_maximize_with_point/6,
	  ppl_Polyhedron_minimize_with_point/6



,
	  ppl_Polyhedron_frequency/6


,
	  ppl_Polyhedron_contains_Polyhedron/2,
	  ppl_Polyhedron_strictly_contains_Polyhedron/2,
	  ppl_Polyhedron_is_disjoint_from_Polyhedron/2



,
	  ppl_Polyhedron_equals_Polyhedron/2


,
	  ppl_Polyhedron_OK/1


,
	  ppl_Polyhedron_add_constraint/2,
	  ppl_Polyhedron_add_congruence/2,
	  ppl_Polyhedron_add_generator/2



,
	  ppl_Polyhedron_add_constraints/2,
	  ppl_Polyhedron_add_congruences/2,
	  ppl_Polyhedron_add_generators/2



,
	  ppl_Polyhedron_refine_with_constraint/2,
	  ppl_Polyhedron_refine_with_congruence/2



,
	  ppl_Polyhedron_refine_with_constraints/2,
	  ppl_Polyhedron_refine_with_congruences/2



,
	  ppl_Polyhedron_intersection_assign/2,
	  ppl_Polyhedron_upper_bound_assign/2,
	  ppl_Polyhedron_difference_assign/2,
	  ppl_Polyhedron_concatenate_assign/2,
	  ppl_Polyhedron_time_elapse_assign/2,
	  ppl_Polyhedron_poly_hull_assign/2,
	  ppl_Polyhedron_poly_difference_assign/2



,
	  ppl_Polyhedron_upper_bound_assign_if_exact/2,
	  ppl_Polyhedron_poly_hull_assign_if_exact/2



,
	  ppl_Polyhedron_simplify_using_context_assign/3


,
	  ppl_Polyhedron_constrains/2


,
	  ppl_Polyhedron_unconstrain_space_dimension/2


,
	  ppl_Polyhedron_unconstrain_space_dimensions/2


,
	  ppl_Polyhedron_affine_image/4,
	  ppl_Polyhedron_affine_preimage/4



,
	  ppl_Polyhedron_bounded_affine_image/5,
	  ppl_Polyhedron_bounded_affine_preimage/5



,
	  ppl_Polyhedron_generalized_affine_image/5,
	  ppl_Polyhedron_generalized_affine_preimage/5



,
	  ppl_Polyhedron_generalized_affine_image_lhs_rhs/4,
	  ppl_Polyhedron_generalized_affine_preimage_lhs_rhs/4



,
	  ppl_Polyhedron_add_space_dimensions_and_embed/2,
	  ppl_Polyhedron_add_space_dimensions_and_project/2



,
	  ppl_Polyhedron_remove_space_dimensions/2


,
	  ppl_Polyhedron_remove_higher_space_dimensions/2


,
	  ppl_Polyhedron_expand_space_dimension/3


,
	  ppl_Polyhedron_fold_space_dimensions/3


,
	  ppl_Polyhedron_map_space_dimensions/2


,
	  ppl_Polyhedron_drop_some_non_integer_points/2


,
	  ppl_Polyhedron_drop_some_non_integer_points_2/3


,
	  ppl_Polyhedron_ascii_dump/1


,
	  ppl_Polyhedron_external_memory_in_bytes/2,
	  ppl_Polyhedron_total_memory_in_bytes/2



,
	  ppl_Polyhedron_BHRZ03_widening_assign_with_tokens/4,
	  ppl_Polyhedron_H79_widening_assign_with_tokens/4



,
	  ppl_Polyhedron_BHRZ03_widening_assign/2,
	  ppl_Polyhedron_H79_widening_assign/2



,
	  ppl_Polyhedron_widening_assign_with_tokens/4


,
	  ppl_Polyhedron_widening_assign/2


,
	  ppl_Polyhedron_limited_BHRZ03_extrapolation_assign_with_tokens/5,
	  ppl_Polyhedron_bounded_BHRZ03_extrapolation_assign_with_tokens/5,
	  ppl_Polyhedron_limited_H79_extrapolation_assign_with_tokens/5,
	  ppl_Polyhedron_bounded_H79_extrapolation_assign_with_tokens/5




,
	  ppl_Polyhedron_limited_BHRZ03_extrapolation_assign/3,
	  ppl_Polyhedron_bounded_BHRZ03_extrapolation_assign/3,
	  ppl_Polyhedron_limited_H79_extrapolation_assign/3,
	  ppl_Polyhedron_bounded_H79_extrapolation_assign/3




,
	  ppl_Polyhedron_linear_partition/4



,
	  ppl_Polyhedron_wrap_assign/8


,
	  ppl_termination_test_MS_C_Polyhedron/1,
	  ppl_termination_test_PR_C_Polyhedron/1,
	  ppl_termination_test_MS_NNC_Polyhedron/1,
	  ppl_termination_test_PR_NNC_Polyhedron/1




,
	  ppl_one_affine_ranking_function_MS_C_Polyhedron/2,
	  ppl_one_affine_ranking_function_PR_C_Polyhedron/2,
	  ppl_one_affine_ranking_function_MS_NNC_Polyhedron/2,
	  ppl_one_affine_ranking_function_PR_NNC_Polyhedron/2




,
	  ppl_all_affine_ranking_functions_MS_C_Polyhedron/2,
	  ppl_all_affine_ranking_functions_PR_C_Polyhedron/2,
	  ppl_all_affine_ranking_functions_MS_NNC_Polyhedron/2,
	  ppl_all_affine_ranking_functions_PR_NNC_Polyhedron/2




,
	  ppl_all_affine_quasi_ranking_functions_MS_C_Polyhedron/3,
	  ppl_all_affine_quasi_ranking_functions_MS_NNC_Polyhedron/3



,
	  ppl_termination_test_MS_C_Polyhedron_2/2,
	  ppl_termination_test_PR_C_Polyhedron_2/2,
	  ppl_termination_test_MS_NNC_Polyhedron_2/2,
	  ppl_termination_test_PR_NNC_Polyhedron_2/2




,
	  ppl_one_affine_ranking_function_MS_C_Polyhedron_2/3,
	  ppl_one_affine_ranking_function_PR_C_Polyhedron_2/3,
	  ppl_one_affine_ranking_function_MS_NNC_Polyhedron_2/3,
	  ppl_one_affine_ranking_function_PR_NNC_Polyhedron_2/3




,
	  ppl_all_affine_ranking_functions_MS_C_Polyhedron_2/3,
	  ppl_all_affine_ranking_functions_PR_C_Polyhedron_2/3,
	  ppl_all_affine_ranking_functions_MS_NNC_Polyhedron_2/3,
	  ppl_all_affine_ranking_functions_PR_NNC_Polyhedron_2/3




,
	  ppl_all_affine_quasi_ranking_functions_MS_C_Polyhedron_2/4,
	  ppl_all_affine_quasi_ranking_functions_MS_NNC_Polyhedron_2/4




,
	  ppl_delete_Grid/1


,
	  ppl_new_Grid_from_space_dimension/3



,
	  ppl_new_Grid_from_C_Polyhedron/2,
	  ppl_new_Grid_from_NNC_Polyhedron/2,
	  ppl_new_Grid_from_Grid/2,
	  ppl_new_Grid_from_Rational_Box/2,
	  ppl_new_Grid_from_BD_Shape_mpz_class/2,
	  ppl_new_Grid_from_BD_Shape_mpq_class/2,
	  ppl_new_Grid_from_Octagonal_Shape_mpz_class/2,
	  ppl_new_Grid_from_Octagonal_Shape_mpq_class/2,
	  ppl_new_Grid_from_Double_Box/2,
	  ppl_new_Grid_from_BD_Shape_double/2,
	  ppl_new_Grid_from_Octagonal_Shape_double/2




,
	  ppl_new_Grid_from_C_Polyhedron_with_complexity/3,
	  ppl_new_Grid_from_NNC_Polyhedron_with_complexity/3,
	  ppl_new_Grid_from_Grid_with_complexity/3,
	  ppl_new_Grid_from_Rational_Box_with_complexity/3,
	  ppl_new_Grid_from_BD_Shape_mpz_class_with_complexity/3,
	  ppl_new_Grid_from_BD_Shape_mpq_class_with_complexity/3,
	  ppl_new_Grid_from_Octagonal_Shape_mpz_class_with_complexity/3,
	  ppl_new_Grid_from_Octagonal_Shape_mpq_class_with_complexity/3,
	  ppl_new_Grid_from_Double_Box_with_complexity/3,
	  ppl_new_Grid_from_BD_Shape_double_with_complexity/3,
	  ppl_new_Grid_from_Octagonal_Shape_double_with_complexity/3




,
	  ppl_new_Grid_from_constraints/2,
	  ppl_new_Grid_from_congruences/2,
	  ppl_new_Grid_from_grid_generators/2




,
	  ppl_Grid_swap/2


,
	  ppl_Grid_space_dimension/2,
	  ppl_Grid_affine_dimension/2



,
	  ppl_Grid_relation_with_constraint/3,
	  ppl_Grid_relation_with_generator/3,
	  ppl_Grid_relation_with_congruence/3,
	  ppl_Grid_relation_with_grid_generator/3



,
	  ppl_Grid_get_constraints/2,
	  ppl_Grid_get_congruences/2,
	  ppl_Grid_get_grid_generators/2



,
	  ppl_Grid_get_minimized_constraints/2,
	  ppl_Grid_get_minimized_congruences/2,
	  ppl_Grid_get_minimized_grid_generators/2



,
	  ppl_Grid_is_empty/1,
	  ppl_Grid_is_universe/1,
	  ppl_Grid_is_bounded/1,
	  ppl_Grid_contains_integer_point/1,
	  ppl_Grid_is_topologically_closed/1,
	  ppl_Grid_is_discrete/1



,
	  ppl_Grid_topological_closure_assign/1



,
	  ppl_Grid_bounds_from_above/2,
	  ppl_Grid_bounds_from_below/2



,
	  ppl_Grid_maximize/5,
	  ppl_Grid_minimize/5



,
	  ppl_Grid_maximize_with_point/6,
	  ppl_Grid_minimize_with_point/6



,
	  ppl_Grid_frequency/6


,
	  ppl_Grid_contains_Grid/2,
	  ppl_Grid_strictly_contains_Grid/2,
	  ppl_Grid_is_disjoint_from_Grid/2



,
	  ppl_Grid_equals_Grid/2


,
	  ppl_Grid_OK/1


,
	  ppl_Grid_add_constraint/2,
	  ppl_Grid_add_congruence/2,
	  ppl_Grid_add_grid_generator/2



,
	  ppl_Grid_add_constraints/2,
	  ppl_Grid_add_congruences/2,
	  ppl_Grid_add_grid_generators/2



,
	  ppl_Grid_refine_with_constraint/2,
	  ppl_Grid_refine_with_congruence/2



,
	  ppl_Grid_refine_with_constraints/2,
	  ppl_Grid_refine_with_congruences/2



,
	  ppl_Grid_intersection_assign/2,
	  ppl_Grid_upper_bound_assign/2,
	  ppl_Grid_difference_assign/2,
	  ppl_Grid_concatenate_assign/2,
	  ppl_Grid_time_elapse_assign/2



,
	  ppl_Grid_upper_bound_assign_if_exact/2



,
	  ppl_Grid_simplify_using_context_assign/3


,
	  ppl_Grid_constrains/2


,
	  ppl_Grid_unconstrain_space_dimension/2


,
	  ppl_Grid_unconstrain_space_dimensions/2


,
	  ppl_Grid_affine_image/4,
	  ppl_Grid_affine_preimage/4



,
	  ppl_Grid_bounded_affine_image/5,
	  ppl_Grid_bounded_affine_preimage/5



,
	  ppl_Grid_generalized_affine_image/5,
	  ppl_Grid_generalized_affine_preimage/5



,
	  ppl_Grid_generalized_affine_image_lhs_rhs/4,
	  ppl_Grid_generalized_affine_preimage_lhs_rhs/4



,
	  ppl_Grid_generalized_affine_image_with_congruence/6,
	  ppl_Grid_generalized_affine_preimage_with_congruence/6



,
	  ppl_Grid_generalized_affine_image_lhs_rhs_with_congruence/5,
	  ppl_Grid_generalized_affine_preimage_lhs_rhs_with_congruence/5



,
	  ppl_Grid_add_space_dimensions_and_embed/2,
	  ppl_Grid_add_space_dimensions_and_project/2



,
	  ppl_Grid_remove_space_dimensions/2


,
	  ppl_Grid_remove_higher_space_dimensions/2


,
	  ppl_Grid_expand_space_dimension/3


,
	  ppl_Grid_fold_space_dimensions/3


,
	  ppl_Grid_map_space_dimensions/2


,
	  ppl_Grid_drop_some_non_integer_points/2


,
	  ppl_Grid_drop_some_non_integer_points_2/3


,
	  ppl_Grid_ascii_dump/1


,
	  ppl_Grid_external_memory_in_bytes/2,
	  ppl_Grid_total_memory_in_bytes/2



,
	  ppl_Grid_congruence_widening_assign_with_tokens/4,
	  ppl_Grid_generator_widening_assign_with_tokens/4



,
	  ppl_Grid_congruence_widening_assign/2,
	  ppl_Grid_generator_widening_assign/2



,
	  ppl_Grid_widening_assign_with_tokens/4


,
	  ppl_Grid_widening_assign/2


,
	  ppl_Grid_limited_congruence_extrapolation_assign_with_tokens/5,
	  ppl_Grid_limited_generator_extrapolation_assign_with_tokens/5




,
	  ppl_Grid_limited_congruence_extrapolation_assign/3,
	  ppl_Grid_limited_generator_extrapolation_assign/3








,
	  ppl_Grid_wrap_assign/8


,
	  ppl_termination_test_MS_Grid/1,
	  ppl_termination_test_PR_Grid/1




,
	  ppl_one_affine_ranking_function_MS_Grid/2,
	  ppl_one_affine_ranking_function_PR_Grid/2




,
	  ppl_all_affine_ranking_functions_MS_Grid/2,
	  ppl_all_affine_ranking_functions_PR_Grid/2




,
	  ppl_all_affine_quasi_ranking_functions_MS_Grid/3



,
	  ppl_termination_test_MS_Grid_2/2,
	  ppl_termination_test_PR_Grid_2/2




,
	  ppl_one_affine_ranking_function_MS_Grid_2/3,
	  ppl_one_affine_ranking_function_PR_Grid_2/3




,
	  ppl_all_affine_ranking_functions_MS_Grid_2/3,
	  ppl_all_affine_ranking_functions_PR_Grid_2/3




,
	  ppl_all_affine_quasi_ranking_functions_MS_Grid_2/4




,
	  ppl_delete_Rational_Box/1


,
	  ppl_new_Rational_Box_from_space_dimension/3



,
	  ppl_new_Rational_Box_from_C_Polyhedron/2,
	  ppl_new_Rational_Box_from_NNC_Polyhedron/2,
	  ppl_new_Rational_Box_from_Grid/2,
	  ppl_new_Rational_Box_from_Rational_Box/2,
	  ppl_new_Rational_Box_from_BD_Shape_mpz_class/2,
	  ppl_new_Rational_Box_from_BD_Shape_mpq_class/2,
	  ppl_new_Rational_Box_from_Octagonal_Shape_mpz_class/2,
	  ppl_new_Rational_Box_from_Octagonal_Shape_mpq_class/2,
	  ppl_new_Rational_Box_from_Double_Box/2,
	  ppl_new_Rational_Box_from_BD_Shape_double/2,
	  ppl_new_Rational_Box_from_Octagonal_Shape_double/2




,
	  ppl_new_Rational_Box_from_C_Polyhedron_with_complexity/3,
	  ppl_new_Rational_Box_from_NNC_Polyhedron_with_complexity/3,
	  ppl_new_Rational_Box_from_Grid_with_complexity/3,
	  ppl_new_Rational_Box_from_Rational_Box_with_complexity/3,
	  ppl_new_Rational_Box_from_BD_Shape_mpz_class_with_complexity/3,
	  ppl_new_Rational_Box_from_BD_Shape_mpq_class_with_complexity/3,
	  ppl_new_Rational_Box_from_Octagonal_Shape_mpz_class_with_complexity/3,
	  ppl_new_Rational_Box_from_Octagonal_Shape_mpq_class_with_complexity/3,
	  ppl_new_Rational_Box_from_Double_Box_with_complexity/3,
	  ppl_new_Rational_Box_from_BD_Shape_double_with_complexity/3,
	  ppl_new_Rational_Box_from_Octagonal_Shape_double_with_complexity/3




,
	  ppl_new_Rational_Box_from_constraints/2,
	  ppl_new_Rational_Box_from_congruences/2,
	  ppl_new_Rational_Box_from_generators/2




,
	  ppl_Rational_Box_swap/2


,
	  ppl_Rational_Box_space_dimension/2,
	  ppl_Rational_Box_affine_dimension/2



,
	  ppl_Rational_Box_relation_with_constraint/3,
	  ppl_Rational_Box_relation_with_generator/3,
	  ppl_Rational_Box_relation_with_congruence/3



,
	  ppl_Rational_Box_get_constraints/2,
	  ppl_Rational_Box_get_congruences/2



,
	  ppl_Rational_Box_get_minimized_constraints/2,
	  ppl_Rational_Box_get_minimized_congruences/2



,
	  ppl_Rational_Box_is_empty/1,
	  ppl_Rational_Box_is_universe/1,
	  ppl_Rational_Box_is_bounded/1,
	  ppl_Rational_Box_contains_integer_point/1,
	  ppl_Rational_Box_is_topologically_closed/1,
	  ppl_Rational_Box_is_discrete/1



,
	  ppl_Rational_Box_topological_closure_assign/1



,
	  ppl_Rational_Box_bounds_from_above/2,
	  ppl_Rational_Box_bounds_from_below/2



,
	  ppl_Rational_Box_maximize/5,
	  ppl_Rational_Box_minimize/5



,
	  ppl_Rational_Box_maximize_with_point/6,
	  ppl_Rational_Box_minimize_with_point/6



,
	  ppl_Rational_Box_frequency/6


,
	  ppl_Rational_Box_contains_Rational_Box/2,
	  ppl_Rational_Box_strictly_contains_Rational_Box/2,
	  ppl_Rational_Box_is_disjoint_from_Rational_Box/2



,
	  ppl_Rational_Box_equals_Rational_Box/2


,
	  ppl_Rational_Box_OK/1


,
	  ppl_Rational_Box_add_constraint/2,
	  ppl_Rational_Box_add_congruence/2



,
	  ppl_Rational_Box_add_constraints/2,
	  ppl_Rational_Box_add_congruences/2



,
	  ppl_Rational_Box_refine_with_constraint/2,
	  ppl_Rational_Box_refine_with_congruence/2



,
	  ppl_Rational_Box_refine_with_constraints/2,
	  ppl_Rational_Box_refine_with_congruences/2



,
	  ppl_Rational_Box_intersection_assign/2,
	  ppl_Rational_Box_upper_bound_assign/2,
	  ppl_Rational_Box_difference_assign/2,
	  ppl_Rational_Box_concatenate_assign/2,
	  ppl_Rational_Box_time_elapse_assign/2



,
	  ppl_Rational_Box_upper_bound_assign_if_exact/2



,
	  ppl_Rational_Box_simplify_using_context_assign/3


,
	  ppl_Rational_Box_constrains/2


,
	  ppl_Rational_Box_unconstrain_space_dimension/2


,
	  ppl_Rational_Box_unconstrain_space_dimensions/2


,
	  ppl_Rational_Box_affine_image/4,
	  ppl_Rational_Box_affine_preimage/4



,
	  ppl_Rational_Box_bounded_affine_image/5,
	  ppl_Rational_Box_bounded_affine_preimage/5



,
	  ppl_Rational_Box_generalized_affine_image/5,
	  ppl_Rational_Box_generalized_affine_preimage/5



,
	  ppl_Rational_Box_generalized_affine_image_lhs_rhs/4,
	  ppl_Rational_Box_generalized_affine_preimage_lhs_rhs/4



,
	  ppl_Rational_Box_add_space_dimensions_and_embed/2,
	  ppl_Rational_Box_add_space_dimensions_and_project/2



,
	  ppl_Rational_Box_remove_space_dimensions/2


,
	  ppl_Rational_Box_remove_higher_space_dimensions/2


,
	  ppl_Rational_Box_expand_space_dimension/3


,
	  ppl_Rational_Box_fold_space_dimensions/3


,
	  ppl_Rational_Box_map_space_dimensions/2


,
	  ppl_Rational_Box_drop_some_non_integer_points/2


,
	  ppl_Rational_Box_drop_some_non_integer_points_2/3


,
	  ppl_Rational_Box_ascii_dump/1


,
	  ppl_Rational_Box_external_memory_in_bytes/2,
	  ppl_Rational_Box_total_memory_in_bytes/2



,
	  ppl_Rational_Box_CC76_widening_assign_with_tokens/4



,
	  ppl_Rational_Box_CC76_widening_assign/2



,
	  ppl_Rational_Box_widening_assign_with_tokens/4


,
	  ppl_Rational_Box_widening_assign/2


,
	  ppl_Rational_Box_limited_CC76_extrapolation_assign_with_tokens/5




,
	  ppl_Rational_Box_limited_CC76_extrapolation_assign/3




,
	  ppl_Rational_Box_linear_partition/4



,
	  ppl_Rational_Box_wrap_assign/8


,
	  ppl_termination_test_MS_Rational_Box/1,
	  ppl_termination_test_PR_Rational_Box/1




,
	  ppl_one_affine_ranking_function_MS_Rational_Box/2,
	  ppl_one_affine_ranking_function_PR_Rational_Box/2




,
	  ppl_all_affine_ranking_functions_MS_Rational_Box/2,
	  ppl_all_affine_ranking_functions_PR_Rational_Box/2




,
	  ppl_all_affine_quasi_ranking_functions_MS_Rational_Box/3



,
	  ppl_termination_test_MS_Rational_Box_2/2,
	  ppl_termination_test_PR_Rational_Box_2/2




,
	  ppl_one_affine_ranking_function_MS_Rational_Box_2/3,
	  ppl_one_affine_ranking_function_PR_Rational_Box_2/3




,
	  ppl_all_affine_ranking_functions_MS_Rational_Box_2/3,
	  ppl_all_affine_ranking_functions_PR_Rational_Box_2/3




,
	  ppl_all_affine_quasi_ranking_functions_MS_Rational_Box_2/4


,
	  ppl_delete_BD_Shape_mpz_class/1


,
	  ppl_new_BD_Shape_mpz_class_from_space_dimension/3



,
	  ppl_new_BD_Shape_mpz_class_from_C_Polyhedron/2,
	  ppl_new_BD_Shape_mpz_class_from_NNC_Polyhedron/2,
	  ppl_new_BD_Shape_mpz_class_from_Grid/2,
	  ppl_new_BD_Shape_mpz_class_from_Rational_Box/2,
	  ppl_new_BD_Shape_mpz_class_from_BD_Shape_mpz_class/2,
	  ppl_new_BD_Shape_mpz_class_from_BD_Shape_mpq_class/2,
	  ppl_new_BD_Shape_mpz_class_from_Octagonal_Shape_mpz_class/2,
	  ppl_new_BD_Shape_mpz_class_from_Octagonal_Shape_mpq_class/2,
	  ppl_new_BD_Shape_mpz_class_from_Double_Box/2,
	  ppl_new_BD_Shape_mpz_class_from_BD_Shape_double/2,
	  ppl_new_BD_Shape_mpz_class_from_Octagonal_Shape_double/2




,
	  ppl_new_BD_Shape_mpz_class_from_C_Polyhedron_with_complexity/3,
	  ppl_new_BD_Shape_mpz_class_from_NNC_Polyhedron_with_complexity/3,
	  ppl_new_BD_Shape_mpz_class_from_Grid_with_complexity/3,
	  ppl_new_BD_Shape_mpz_class_from_Rational_Box_with_complexity/3,
	  ppl_new_BD_Shape_mpz_class_from_BD_Shape_mpz_class_with_complexity/3,
	  ppl_new_BD_Shape_mpz_class_from_BD_Shape_mpq_class_with_complexity/3,
	  ppl_new_BD_Shape_mpz_class_from_Octagonal_Shape_mpz_class_with_complexity/3,
	  ppl_new_BD_Shape_mpz_class_from_Octagonal_Shape_mpq_class_with_complexity/3,
	  ppl_new_BD_Shape_mpz_class_from_Double_Box_with_complexity/3,
	  ppl_new_BD_Shape_mpz_class_from_BD_Shape_double_with_complexity/3,
	  ppl_new_BD_Shape_mpz_class_from_Octagonal_Shape_double_with_complexity/3




,
	  ppl_new_BD_Shape_mpz_class_from_constraints/2,
	  ppl_new_BD_Shape_mpz_class_from_congruences/2,
	  ppl_new_BD_Shape_mpz_class_from_generators/2




,
	  ppl_BD_Shape_mpz_class_swap/2


,
	  ppl_BD_Shape_mpz_class_space_dimension/2,
	  ppl_BD_Shape_mpz_class_affine_dimension/2



,
	  ppl_BD_Shape_mpz_class_relation_with_constraint/3,
	  ppl_BD_Shape_mpz_class_relation_with_generator/3,
	  ppl_BD_Shape_mpz_class_relation_with_congruence/3



,
	  ppl_BD_Shape_mpz_class_get_constraints/2,
	  ppl_BD_Shape_mpz_class_get_congruences/2



,
	  ppl_BD_Shape_mpz_class_get_minimized_constraints/2,
	  ppl_BD_Shape_mpz_class_get_minimized_congruences/2



,
	  ppl_BD_Shape_mpz_class_is_empty/1,
	  ppl_BD_Shape_mpz_class_is_universe/1,
	  ppl_BD_Shape_mpz_class_is_bounded/1,
	  ppl_BD_Shape_mpz_class_contains_integer_point/1,
	  ppl_BD_Shape_mpz_class_is_topologically_closed/1,
	  ppl_BD_Shape_mpz_class_is_discrete/1



,
	  ppl_BD_Shape_mpz_class_topological_closure_assign/1



,
	  ppl_BD_Shape_mpz_class_bounds_from_above/2,
	  ppl_BD_Shape_mpz_class_bounds_from_below/2



,
	  ppl_BD_Shape_mpz_class_maximize/5,
	  ppl_BD_Shape_mpz_class_minimize/5



,
	  ppl_BD_Shape_mpz_class_maximize_with_point/6,
	  ppl_BD_Shape_mpz_class_minimize_with_point/6



,
	  ppl_BD_Shape_mpz_class_frequency/6


,
	  ppl_BD_Shape_mpz_class_contains_BD_Shape_mpz_class/2,
	  ppl_BD_Shape_mpz_class_strictly_contains_BD_Shape_mpz_class/2,
	  ppl_BD_Shape_mpz_class_is_disjoint_from_BD_Shape_mpz_class/2



,
	  ppl_BD_Shape_mpz_class_equals_BD_Shape_mpz_class/2


,
	  ppl_BD_Shape_mpz_class_OK/1


,
	  ppl_BD_Shape_mpz_class_add_constraint/2,
	  ppl_BD_Shape_mpz_class_add_congruence/2



,
	  ppl_BD_Shape_mpz_class_add_constraints/2,
	  ppl_BD_Shape_mpz_class_add_congruences/2



,
	  ppl_BD_Shape_mpz_class_refine_with_constraint/2,
	  ppl_BD_Shape_mpz_class_refine_with_congruence/2



,
	  ppl_BD_Shape_mpz_class_refine_with_constraints/2,
	  ppl_BD_Shape_mpz_class_refine_with_congruences/2



,
	  ppl_BD_Shape_mpz_class_intersection_assign/2,
	  ppl_BD_Shape_mpz_class_upper_bound_assign/2,
	  ppl_BD_Shape_mpz_class_difference_assign/2,
	  ppl_BD_Shape_mpz_class_concatenate_assign/2,
	  ppl_BD_Shape_mpz_class_time_elapse_assign/2



,
	  ppl_BD_Shape_mpz_class_upper_bound_assign_if_exact/2



,
	  ppl_BD_Shape_mpz_class_simplify_using_context_assign/3


,
	  ppl_BD_Shape_mpz_class_constrains/2


,
	  ppl_BD_Shape_mpz_class_unconstrain_space_dimension/2


,
	  ppl_BD_Shape_mpz_class_unconstrain_space_dimensions/2


,
	  ppl_BD_Shape_mpz_class_affine_image/4,
	  ppl_BD_Shape_mpz_class_affine_preimage/4



,
	  ppl_BD_Shape_mpz_class_bounded_affine_image/5,
	  ppl_BD_Shape_mpz_class_bounded_affine_preimage/5



,
	  ppl_BD_Shape_mpz_class_generalized_affine_image/5,
	  ppl_BD_Shape_mpz_class_generalized_affine_preimage/5



,
	  ppl_BD_Shape_mpz_class_generalized_affine_image_lhs_rhs/4,
	  ppl_BD_Shape_mpz_class_generalized_affine_preimage_lhs_rhs/4



,
	  ppl_BD_Shape_mpz_class_add_space_dimensions_and_embed/2,
	  ppl_BD_Shape_mpz_class_add_space_dimensions_and_project/2



,
	  ppl_BD_Shape_mpz_class_remove_space_dimensions/2


,
	  ppl_BD_Shape_mpz_class_remove_higher_space_dimensions/2


,
	  ppl_BD_Shape_mpz_class_expand_space_dimension/3


,
	  ppl_BD_Shape_mpz_class_fold_space_dimensions/3


,
	  ppl_BD_Shape_mpz_class_map_space_dimensions/2


,
	  ppl_BD_Shape_mpz_class_drop_some_non_integer_points/2


,
	  ppl_BD_Shape_mpz_class_drop_some_non_integer_points_2/3


,
	  ppl_BD_Shape_mpz_class_ascii_dump/1


,
	  ppl_BD_Shape_mpz_class_external_memory_in_bytes/2,
	  ppl_BD_Shape_mpz_class_total_memory_in_bytes/2



,
	  ppl_BD_Shape_mpz_class_BHMZ05_widening_assign_with_tokens/4,
	  ppl_BD_Shape_mpz_class_H79_widening_assign_with_tokens/4



,
	  ppl_BD_Shape_mpz_class_BHMZ05_widening_assign/2,
	  ppl_BD_Shape_mpz_class_H79_widening_assign/2



,
	  ppl_BD_Shape_mpz_class_widening_assign_with_tokens/4


,
	  ppl_BD_Shape_mpz_class_widening_assign/2


,
	  ppl_BD_Shape_mpz_class_limited_BHMZ05_extrapolation_assign_with_tokens/5,
	  ppl_BD_Shape_mpz_class_limited_H79_extrapolation_assign_with_tokens/5,
	  ppl_BD_Shape_mpz_class_limited_CC76_extrapolation_assign_with_tokens/5




,
	  ppl_BD_Shape_mpz_class_limited_BHMZ05_extrapolation_assign/3,
	  ppl_BD_Shape_mpz_class_limited_H79_extrapolation_assign/3,
	  ppl_BD_Shape_mpz_class_limited_CC76_extrapolation_assign/3




,
	  ppl_BD_Shape_mpz_class_CC76_extrapolation_assign_with_tokens/4



,
	  ppl_BD_Shape_mpz_class_CC76_extrapolation_assign/2



,
	  ppl_BD_Shape_mpz_class_CC76_narrowing_assign/2



,
	  ppl_BD_Shape_mpz_class_linear_partition/4



,
	  ppl_BD_Shape_mpz_class_wrap_assign/8


,
	  ppl_termination_test_MS_BD_Shape_mpz_class/1,
	  ppl_termination_test_PR_BD_Shape_mpz_class/1




,
	  ppl_one_affine_ranking_function_MS_BD_Shape_mpz_class/2,
	  ppl_one_affine_ranking_function_PR_BD_Shape_mpz_class/2




,
	  ppl_all_affine_ranking_functions_MS_BD_Shape_mpz_class/2,
	  ppl_all_affine_ranking_functions_PR_BD_Shape_mpz_class/2




,
	  ppl_all_affine_quasi_ranking_functions_MS_BD_Shape_mpz_class/3



,
	  ppl_termination_test_MS_BD_Shape_mpz_class_2/2,
	  ppl_termination_test_PR_BD_Shape_mpz_class_2/2




,
	  ppl_one_affine_ranking_function_MS_BD_Shape_mpz_class_2/3,
	  ppl_one_affine_ranking_function_PR_BD_Shape_mpz_class_2/3




,
	  ppl_all_affine_ranking_functions_MS_BD_Shape_mpz_class_2/3,
	  ppl_all_affine_ranking_functions_PR_BD_Shape_mpz_class_2/3




,
	  ppl_all_affine_quasi_ranking_functions_MS_BD_Shape_mpz_class_2/4




,
	  ppl_delete_BD_Shape_mpq_class/1


,
	  ppl_new_BD_Shape_mpq_class_from_space_dimension/3



,
	  ppl_new_BD_Shape_mpq_class_from_C_Polyhedron/2,
	  ppl_new_BD_Shape_mpq_class_from_NNC_Polyhedron/2,
	  ppl_new_BD_Shape_mpq_class_from_Grid/2,
	  ppl_new_BD_Shape_mpq_class_from_Rational_Box/2,
	  ppl_new_BD_Shape_mpq_class_from_BD_Shape_mpz_class/2,
	  ppl_new_BD_Shape_mpq_class_from_BD_Shape_mpq_class/2,
	  ppl_new_BD_Shape_mpq_class_from_Octagonal_Shape_mpz_class/2,
	  ppl_new_BD_Shape_mpq_class_from_Octagonal_Shape_mpq_class/2,
	  ppl_new_BD_Shape_mpq_class_from_Double_Box/2,
	  ppl_new_BD_Shape_mpq_class_from_BD_Shape_double/2,
	  ppl_new_BD_Shape_mpq_class_from_Octagonal_Shape_double/2




,
	  ppl_new_BD_Shape_mpq_class_from_C_Polyhedron_with_complexity/3,
	  ppl_new_BD_Shape_mpq_class_from_NNC_Polyhedron_with_complexity/3,
	  ppl_new_BD_Shape_mpq_class_from_Grid_with_complexity/3,
	  ppl_new_BD_Shape_mpq_class_from_Rational_Box_with_complexity/3,
	  ppl_new_BD_Shape_mpq_class_from_BD_Shape_mpz_class_with_complexity/3,
	  ppl_new_BD_Shape_mpq_class_from_BD_Shape_mpq_class_with_complexity/3,
	  ppl_new_BD_Shape_mpq_class_from_Octagonal_Shape_mpz_class_with_complexity/3,
	  ppl_new_BD_Shape_mpq_class_from_Octagonal_Shape_mpq_class_with_complexity/3,
	  ppl_new_BD_Shape_mpq_class_from_Double_Box_with_complexity/3,
	  ppl_new_BD_Shape_mpq_class_from_BD_Shape_double_with_complexity/3,
	  ppl_new_BD_Shape_mpq_class_from_Octagonal_Shape_double_with_complexity/3




,
	  ppl_new_BD_Shape_mpq_class_from_constraints/2,
	  ppl_new_BD_Shape_mpq_class_from_congruences/2,
	  ppl_new_BD_Shape_mpq_class_from_generators/2




,
	  ppl_BD_Shape_mpq_class_swap/2


,
	  ppl_BD_Shape_mpq_class_space_dimension/2,
	  ppl_BD_Shape_mpq_class_affine_dimension/2



,
	  ppl_BD_Shape_mpq_class_relation_with_constraint/3,
	  ppl_BD_Shape_mpq_class_relation_with_generator/3,
	  ppl_BD_Shape_mpq_class_relation_with_congruence/3



,
	  ppl_BD_Shape_mpq_class_get_constraints/2,
	  ppl_BD_Shape_mpq_class_get_congruences/2



,
	  ppl_BD_Shape_mpq_class_get_minimized_constraints/2,
	  ppl_BD_Shape_mpq_class_get_minimized_congruences/2



,
	  ppl_BD_Shape_mpq_class_is_empty/1,
	  ppl_BD_Shape_mpq_class_is_universe/1,
	  ppl_BD_Shape_mpq_class_is_bounded/1,
	  ppl_BD_Shape_mpq_class_contains_integer_point/1,
	  ppl_BD_Shape_mpq_class_is_topologically_closed/1,
	  ppl_BD_Shape_mpq_class_is_discrete/1



,
	  ppl_BD_Shape_mpq_class_topological_closure_assign/1



,
	  ppl_BD_Shape_mpq_class_bounds_from_above/2,
	  ppl_BD_Shape_mpq_class_bounds_from_below/2



,
	  ppl_BD_Shape_mpq_class_maximize/5,
	  ppl_BD_Shape_mpq_class_minimize/5



,
	  ppl_BD_Shape_mpq_class_maximize_with_point/6,
	  ppl_BD_Shape_mpq_class_minimize_with_point/6



,
	  ppl_BD_Shape_mpq_class_frequency/6


,
	  ppl_BD_Shape_mpq_class_contains_BD_Shape_mpq_class/2,
	  ppl_BD_Shape_mpq_class_strictly_contains_BD_Shape_mpq_class/2,
	  ppl_BD_Shape_mpq_class_is_disjoint_from_BD_Shape_mpq_class/2



,
	  ppl_BD_Shape_mpq_class_equals_BD_Shape_mpq_class/2


,
	  ppl_BD_Shape_mpq_class_OK/1


,
	  ppl_BD_Shape_mpq_class_add_constraint/2,
	  ppl_BD_Shape_mpq_class_add_congruence/2



,
	  ppl_BD_Shape_mpq_class_add_constraints/2,
	  ppl_BD_Shape_mpq_class_add_congruences/2



,
	  ppl_BD_Shape_mpq_class_refine_with_constraint/2,
	  ppl_BD_Shape_mpq_class_refine_with_congruence/2



,
	  ppl_BD_Shape_mpq_class_refine_with_constraints/2,
	  ppl_BD_Shape_mpq_class_refine_with_congruences/2



,
	  ppl_BD_Shape_mpq_class_intersection_assign/2,
	  ppl_BD_Shape_mpq_class_upper_bound_assign/2,
	  ppl_BD_Shape_mpq_class_difference_assign/2,
	  ppl_BD_Shape_mpq_class_concatenate_assign/2,
	  ppl_BD_Shape_mpq_class_time_elapse_assign/2



,
	  ppl_BD_Shape_mpq_class_upper_bound_assign_if_exact/2



,
	  ppl_BD_Shape_mpq_class_simplify_using_context_assign/3


,
	  ppl_BD_Shape_mpq_class_constrains/2


,
	  ppl_BD_Shape_mpq_class_unconstrain_space_dimension/2


,
	  ppl_BD_Shape_mpq_class_unconstrain_space_dimensions/2


,
	  ppl_BD_Shape_mpq_class_affine_image/4,
	  ppl_BD_Shape_mpq_class_affine_preimage/4



,
	  ppl_BD_Shape_mpq_class_bounded_affine_image/5,
	  ppl_BD_Shape_mpq_class_bounded_affine_preimage/5



,
	  ppl_BD_Shape_mpq_class_generalized_affine_image/5,
	  ppl_BD_Shape_mpq_class_generalized_affine_preimage/5



,
	  ppl_BD_Shape_mpq_class_generalized_affine_image_lhs_rhs/4,
	  ppl_BD_Shape_mpq_class_generalized_affine_preimage_lhs_rhs/4



,
	  ppl_BD_Shape_mpq_class_add_space_dimensions_and_embed/2,
	  ppl_BD_Shape_mpq_class_add_space_dimensions_and_project/2



,
	  ppl_BD_Shape_mpq_class_remove_space_dimensions/2


,
	  ppl_BD_Shape_mpq_class_remove_higher_space_dimensions/2


,
	  ppl_BD_Shape_mpq_class_expand_space_dimension/3


,
	  ppl_BD_Shape_mpq_class_fold_space_dimensions/3


,
	  ppl_BD_Shape_mpq_class_map_space_dimensions/2


,
	  ppl_BD_Shape_mpq_class_drop_some_non_integer_points/2


,
	  ppl_BD_Shape_mpq_class_drop_some_non_integer_points_2/3


,
	  ppl_BD_Shape_mpq_class_ascii_dump/1


,
	  ppl_BD_Shape_mpq_class_external_memory_in_bytes/2,
	  ppl_BD_Shape_mpq_class_total_memory_in_bytes/2



,
	  ppl_BD_Shape_mpq_class_BHMZ05_widening_assign_with_tokens/4,
	  ppl_BD_Shape_mpq_class_H79_widening_assign_with_tokens/4



,
	  ppl_BD_Shape_mpq_class_BHMZ05_widening_assign/2,
	  ppl_BD_Shape_mpq_class_H79_widening_assign/2



,
	  ppl_BD_Shape_mpq_class_widening_assign_with_tokens/4


,
	  ppl_BD_Shape_mpq_class_widening_assign/2


,
	  ppl_BD_Shape_mpq_class_limited_BHMZ05_extrapolation_assign_with_tokens/5,
	  ppl_BD_Shape_mpq_class_limited_H79_extrapolation_assign_with_tokens/5,
	  ppl_BD_Shape_mpq_class_limited_CC76_extrapolation_assign_with_tokens/5




,
	  ppl_BD_Shape_mpq_class_limited_BHMZ05_extrapolation_assign/3,
	  ppl_BD_Shape_mpq_class_limited_H79_extrapolation_assign/3,
	  ppl_BD_Shape_mpq_class_limited_CC76_extrapolation_assign/3




,
	  ppl_BD_Shape_mpq_class_CC76_extrapolation_assign_with_tokens/4



,
	  ppl_BD_Shape_mpq_class_CC76_extrapolation_assign/2



,
	  ppl_BD_Shape_mpq_class_CC76_narrowing_assign/2



,
	  ppl_BD_Shape_mpq_class_linear_partition/4



,
	  ppl_BD_Shape_mpq_class_wrap_assign/8


,
	  ppl_termination_test_MS_BD_Shape_mpq_class/1,
	  ppl_termination_test_PR_BD_Shape_mpq_class/1




,
	  ppl_one_affine_ranking_function_MS_BD_Shape_mpq_class/2,
	  ppl_one_affine_ranking_function_PR_BD_Shape_mpq_class/2




,
	  ppl_all_affine_ranking_functions_MS_BD_Shape_mpq_class/2,
	  ppl_all_affine_ranking_functions_PR_BD_Shape_mpq_class/2




,
	  ppl_all_affine_quasi_ranking_functions_MS_BD_Shape_mpq_class/3



,
	  ppl_termination_test_MS_BD_Shape_mpq_class_2/2,
	  ppl_termination_test_PR_BD_Shape_mpq_class_2/2




,
	  ppl_one_affine_ranking_function_MS_BD_Shape_mpq_class_2/3,
	  ppl_one_affine_ranking_function_PR_BD_Shape_mpq_class_2/3




,
	  ppl_all_affine_ranking_functions_MS_BD_Shape_mpq_class_2/3,
	  ppl_all_affine_ranking_functions_PR_BD_Shape_mpq_class_2/3




,
	  ppl_all_affine_quasi_ranking_functions_MS_BD_Shape_mpq_class_2/4




,
	  ppl_delete_Octagonal_Shape_mpz_class/1


,
	  ppl_new_Octagonal_Shape_mpz_class_from_space_dimension/3



,
	  ppl_new_Octagonal_Shape_mpz_class_from_C_Polyhedron/2,
	  ppl_new_Octagonal_Shape_mpz_class_from_NNC_Polyhedron/2,
	  ppl_new_Octagonal_Shape_mpz_class_from_Grid/2,
	  ppl_new_Octagonal_Shape_mpz_class_from_Rational_Box/2,
	  ppl_new_Octagonal_Shape_mpz_class_from_BD_Shape_mpz_class/2,
	  ppl_new_Octagonal_Shape_mpz_class_from_BD_Shape_mpq_class/2,
	  ppl_new_Octagonal_Shape_mpz_class_from_Octagonal_Shape_mpz_class/2,
	  ppl_new_Octagonal_Shape_mpz_class_from_Octagonal_Shape_mpq_class/2,
	  ppl_new_Octagonal_Shape_mpz_class_from_Double_Box/2,
	  ppl_new_Octagonal_Shape_mpz_class_from_BD_Shape_double/2,
	  ppl_new_Octagonal_Shape_mpz_class_from_Octagonal_Shape_double/2




,
	  ppl_new_Octagonal_Shape_mpz_class_from_C_Polyhedron_with_complexity/3,
	  ppl_new_Octagonal_Shape_mpz_class_from_NNC_Polyhedron_with_complexity/3,
	  ppl_new_Octagonal_Shape_mpz_class_from_Grid_with_complexity/3,
	  ppl_new_Octagonal_Shape_mpz_class_from_Rational_Box_with_complexity/3,
	  ppl_new_Octagonal_Shape_mpz_class_from_BD_Shape_mpz_class_with_complexity/3,
	  ppl_new_Octagonal_Shape_mpz_class_from_BD_Shape_mpq_class_with_complexity/3,
	  ppl_new_Octagonal_Shape_mpz_class_from_Octagonal_Shape_mpz_class_with_complexity/3,
	  ppl_new_Octagonal_Shape_mpz_class_from_Octagonal_Shape_mpq_class_with_complexity/3,
	  ppl_new_Octagonal_Shape_mpz_class_from_Double_Box_with_complexity/3,
	  ppl_new_Octagonal_Shape_mpz_class_from_BD_Shape_double_with_complexity/3,
	  ppl_new_Octagonal_Shape_mpz_class_from_Octagonal_Shape_double_with_complexity/3




,
	  ppl_new_Octagonal_Shape_mpz_class_from_constraints/2,
	  ppl_new_Octagonal_Shape_mpz_class_from_congruences/2,
	  ppl_new_Octagonal_Shape_mpz_class_from_generators/2




,
	  ppl_Octagonal_Shape_mpz_class_swap/2


,
	  ppl_Octagonal_Shape_mpz_class_space_dimension/2,
	  ppl_Octagonal_Shape_mpz_class_affine_dimension/2



,
	  ppl_Octagonal_Shape_mpz_class_relation_with_constraint/3,
	  ppl_Octagonal_Shape_mpz_class_relation_with_generator/3,
	  ppl_Octagonal_Shape_mpz_class_relation_with_congruence/3



,
	  ppl_Octagonal_Shape_mpz_class_get_constraints/2,
	  ppl_Octagonal_Shape_mpz_class_get_congruences/2



,
	  ppl_Octagonal_Shape_mpz_class_get_minimized_constraints/2,
	  ppl_Octagonal_Shape_mpz_class_get_minimized_congruences/2



,
	  ppl_Octagonal_Shape_mpz_class_is_empty/1,
	  ppl_Octagonal_Shape_mpz_class_is_universe/1,
	  ppl_Octagonal_Shape_mpz_class_is_bounded/1,
	  ppl_Octagonal_Shape_mpz_class_contains_integer_point/1,
	  ppl_Octagonal_Shape_mpz_class_is_topologically_closed/1,
	  ppl_Octagonal_Shape_mpz_class_is_discrete/1



,
	  ppl_Octagonal_Shape_mpz_class_topological_closure_assign/1



,
	  ppl_Octagonal_Shape_mpz_class_bounds_from_above/2,
	  ppl_Octagonal_Shape_mpz_class_bounds_from_below/2



,
	  ppl_Octagonal_Shape_mpz_class_maximize/5,
	  ppl_Octagonal_Shape_mpz_class_minimize/5



,
	  ppl_Octagonal_Shape_mpz_class_maximize_with_point/6,
	  ppl_Octagonal_Shape_mpz_class_minimize_with_point/6



,
	  ppl_Octagonal_Shape_mpz_class_frequency/6


,
	  ppl_Octagonal_Shape_mpz_class_contains_Octagonal_Shape_mpz_class/2,
	  ppl_Octagonal_Shape_mpz_class_strictly_contains_Octagonal_Shape_mpz_class/2,
	  ppl_Octagonal_Shape_mpz_class_is_disjoint_from_Octagonal_Shape_mpz_class/2



,
	  ppl_Octagonal_Shape_mpz_class_equals_Octagonal_Shape_mpz_class/2


,
	  ppl_Octagonal_Shape_mpz_class_OK/1


,
	  ppl_Octagonal_Shape_mpz_class_add_constraint/2,
	  ppl_Octagonal_Shape_mpz_class_add_congruence/2



,
	  ppl_Octagonal_Shape_mpz_class_add_constraints/2,
	  ppl_Octagonal_Shape_mpz_class_add_congruences/2



,
	  ppl_Octagonal_Shape_mpz_class_refine_with_constraint/2,
	  ppl_Octagonal_Shape_mpz_class_refine_with_congruence/2



,
	  ppl_Octagonal_Shape_mpz_class_refine_with_constraints/2,
	  ppl_Octagonal_Shape_mpz_class_refine_with_congruences/2



,
	  ppl_Octagonal_Shape_mpz_class_intersection_assign/2,
	  ppl_Octagonal_Shape_mpz_class_upper_bound_assign/2,
	  ppl_Octagonal_Shape_mpz_class_difference_assign/2,
	  ppl_Octagonal_Shape_mpz_class_concatenate_assign/2,
	  ppl_Octagonal_Shape_mpz_class_time_elapse_assign/2



,
	  ppl_Octagonal_Shape_mpz_class_upper_bound_assign_if_exact/2



,
	  ppl_Octagonal_Shape_mpz_class_simplify_using_context_assign/3


,
	  ppl_Octagonal_Shape_mpz_class_constrains/2


,
	  ppl_Octagonal_Shape_mpz_class_unconstrain_space_dimension/2


,
	  ppl_Octagonal_Shape_mpz_class_unconstrain_space_dimensions/2


,
	  ppl_Octagonal_Shape_mpz_class_affine_image/4,
	  ppl_Octagonal_Shape_mpz_class_affine_preimage/4



,
	  ppl_Octagonal_Shape_mpz_class_bounded_affine_image/5,
	  ppl_Octagonal_Shape_mpz_class_bounded_affine_preimage/5



,
	  ppl_Octagonal_Shape_mpz_class_generalized_affine_image/5,
	  ppl_Octagonal_Shape_mpz_class_generalized_affine_preimage/5



,
	  ppl_Octagonal_Shape_mpz_class_generalized_affine_image_lhs_rhs/4,
	  ppl_Octagonal_Shape_mpz_class_generalized_affine_preimage_lhs_rhs/4



,
	  ppl_Octagonal_Shape_mpz_class_add_space_dimensions_and_embed/2,
	  ppl_Octagonal_Shape_mpz_class_add_space_dimensions_and_project/2



,
	  ppl_Octagonal_Shape_mpz_class_remove_space_dimensions/2


,
	  ppl_Octagonal_Shape_mpz_class_remove_higher_space_dimensions/2


,
	  ppl_Octagonal_Shape_mpz_class_expand_space_dimension/3


,
	  ppl_Octagonal_Shape_mpz_class_fold_space_dimensions/3


,
	  ppl_Octagonal_Shape_mpz_class_map_space_dimensions/2


,
	  ppl_Octagonal_Shape_mpz_class_drop_some_non_integer_points/2


,
	  ppl_Octagonal_Shape_mpz_class_drop_some_non_integer_points_2/3


,
	  ppl_Octagonal_Shape_mpz_class_ascii_dump/1


,
	  ppl_Octagonal_Shape_mpz_class_external_memory_in_bytes/2,
	  ppl_Octagonal_Shape_mpz_class_total_memory_in_bytes/2



,
	  ppl_Octagonal_Shape_mpz_class_BHMZ05_widening_assign_with_tokens/4



,
	  ppl_Octagonal_Shape_mpz_class_BHMZ05_widening_assign/2



,
	  ppl_Octagonal_Shape_mpz_class_widening_assign_with_tokens/4


,
	  ppl_Octagonal_Shape_mpz_class_widening_assign/2


,
	  ppl_Octagonal_Shape_mpz_class_limited_BHMZ05_extrapolation_assign_with_tokens/5,
	  ppl_Octagonal_Shape_mpz_class_limited_CC76_extrapolation_assign_with_tokens/5




,
	  ppl_Octagonal_Shape_mpz_class_limited_BHMZ05_extrapolation_assign/3,
	  ppl_Octagonal_Shape_mpz_class_limited_CC76_extrapolation_assign/3




,
	  ppl_Octagonal_Shape_mpz_class_CC76_extrapolation_assign_with_tokens/4



,
	  ppl_Octagonal_Shape_mpz_class_CC76_extrapolation_assign/2



,
	  ppl_Octagonal_Shape_mpz_class_CC76_narrowing_assign/2



,
	  ppl_Octagonal_Shape_mpz_class_linear_partition/4



,
	  ppl_Octagonal_Shape_mpz_class_wrap_assign/8


,
	  ppl_termination_test_MS_Octagonal_Shape_mpz_class/1,
	  ppl_termination_test_PR_Octagonal_Shape_mpz_class/1




,
	  ppl_one_affine_ranking_function_MS_Octagonal_Shape_mpz_class/2,
	  ppl_one_affine_ranking_function_PR_Octagonal_Shape_mpz_class/2




,
	  ppl_all_affine_ranking_functions_MS_Octagonal_Shape_mpz_class/2,
	  ppl_all_affine_ranking_functions_PR_Octagonal_Shape_mpz_class/2




,
	  ppl_all_affine_quasi_ranking_functions_MS_Octagonal_Shape_mpz_class/3



,
	  ppl_termination_test_MS_Octagonal_Shape_mpz_class_2/2,
	  ppl_termination_test_PR_Octagonal_Shape_mpz_class_2/2




,
	  ppl_one_affine_ranking_function_MS_Octagonal_Shape_mpz_class_2/3,
	  ppl_one_affine_ranking_function_PR_Octagonal_Shape_mpz_class_2/3




,
	  ppl_all_affine_ranking_functions_MS_Octagonal_Shape_mpz_class_2/3,
	  ppl_all_affine_ranking_functions_PR_Octagonal_Shape_mpz_class_2/3




,
	  ppl_all_affine_quasi_ranking_functions_MS_Octagonal_Shape_mpz_class_2/4




,
	  ppl_delete_Octagonal_Shape_mpq_class/1


,
	  ppl_new_Octagonal_Shape_mpq_class_from_space_dimension/3



,
	  ppl_new_Octagonal_Shape_mpq_class_from_C_Polyhedron/2,
	  ppl_new_Octagonal_Shape_mpq_class_from_NNC_Polyhedron/2,
	  ppl_new_Octagonal_Shape_mpq_class_from_Grid/2,
	  ppl_new_Octagonal_Shape_mpq_class_from_Rational_Box/2,
	  ppl_new_Octagonal_Shape_mpq_class_from_BD_Shape_mpz_class/2,
	  ppl_new_Octagonal_Shape_mpq_class_from_BD_Shape_mpq_class/2,
	  ppl_new_Octagonal_Shape_mpq_class_from_Octagonal_Shape_mpz_class/2,
	  ppl_new_Octagonal_Shape_mpq_class_from_Octagonal_Shape_mpq_class/2,
	  ppl_new_Octagonal_Shape_mpq_class_from_Double_Box/2,
	  ppl_new_Octagonal_Shape_mpq_class_from_BD_Shape_double/2,
	  ppl_new_Octagonal_Shape_mpq_class_from_Octagonal_Shape_double/2




,
	  ppl_new_Octagonal_Shape_mpq_class_from_C_Polyhedron_with_complexity/3,
	  ppl_new_Octagonal_Shape_mpq_class_from_NNC_Polyhedron_with_complexity/3,
	  ppl_new_Octagonal_Shape_mpq_class_from_Grid_with_complexity/3,
	  ppl_new_Octagonal_Shape_mpq_class_from_Rational_Box_with_complexity/3,
	  ppl_new_Octagonal_Shape_mpq_class_from_BD_Shape_mpz_class_with_complexity/3,
	  ppl_new_Octagonal_Shape_mpq_class_from_BD_Shape_mpq_class_with_complexity/3,
	  ppl_new_Octagonal_Shape_mpq_class_from_Octagonal_Shape_mpz_class_with_complexity/3,
	  ppl_new_Octagonal_Shape_mpq_class_from_Octagonal_Shape_mpq_class_with_complexity/3,
	  ppl_new_Octagonal_Shape_mpq_class_from_Double_Box_with_complexity/3,
	  ppl_new_Octagonal_Shape_mpq_class_from_BD_Shape_double_with_complexity/3,
	  ppl_new_Octagonal_Shape_mpq_class_from_Octagonal_Shape_double_with_complexity/3




,
	  ppl_new_Octagonal_Shape_mpq_class_from_constraints/2,
	  ppl_new_Octagonal_Shape_mpq_class_from_congruences/2,
	  ppl_new_Octagonal_Shape_mpq_class_from_generators/2




,
	  ppl_Octagonal_Shape_mpq_class_swap/2


,
	  ppl_Octagonal_Shape_mpq_class_space_dimension/2,
	  ppl_Octagonal_Shape_mpq_class_affine_dimension/2



,
	  ppl_Octagonal_Shape_mpq_class_relation_with_constraint/3,
	  ppl_Octagonal_Shape_mpq_class_relation_with_generator/3,
	  ppl_Octagonal_Shape_mpq_class_relation_with_congruence/3



,
	  ppl_Octagonal_Shape_mpq_class_get_constraints/2,
	  ppl_Octagonal_Shape_mpq_class_get_congruences/2



,
	  ppl_Octagonal_Shape_mpq_class_get_minimized_constraints/2,
	  ppl_Octagonal_Shape_mpq_class_get_minimized_congruences/2



,
	  ppl_Octagonal_Shape_mpq_class_is_empty/1,
	  ppl_Octagonal_Shape_mpq_class_is_universe/1,
	  ppl_Octagonal_Shape_mpq_class_is_bounded/1,
	  ppl_Octagonal_Shape_mpq_class_contains_integer_point/1,
	  ppl_Octagonal_Shape_mpq_class_is_topologically_closed/1,
	  ppl_Octagonal_Shape_mpq_class_is_discrete/1



,
	  ppl_Octagonal_Shape_mpq_class_topological_closure_assign/1



,
	  ppl_Octagonal_Shape_mpq_class_bounds_from_above/2,
	  ppl_Octagonal_Shape_mpq_class_bounds_from_below/2



,
	  ppl_Octagonal_Shape_mpq_class_maximize/5,
	  ppl_Octagonal_Shape_mpq_class_minimize/5



,
	  ppl_Octagonal_Shape_mpq_class_maximize_with_point/6,
	  ppl_Octagonal_Shape_mpq_class_minimize_with_point/6



,
	  ppl_Octagonal_Shape_mpq_class_frequency/6


,
	  ppl_Octagonal_Shape_mpq_class_contains_Octagonal_Shape_mpq_class/2,
	  ppl_Octagonal_Shape_mpq_class_strictly_contains_Octagonal_Shape_mpq_class/2,
	  ppl_Octagonal_Shape_mpq_class_is_disjoint_from_Octagonal_Shape_mpq_class/2



,
	  ppl_Octagonal_Shape_mpq_class_equals_Octagonal_Shape_mpq_class/2


,
	  ppl_Octagonal_Shape_mpq_class_OK/1


,
	  ppl_Octagonal_Shape_mpq_class_add_constraint/2,
	  ppl_Octagonal_Shape_mpq_class_add_congruence/2



,
	  ppl_Octagonal_Shape_mpq_class_add_constraints/2,
	  ppl_Octagonal_Shape_mpq_class_add_congruences/2



,
	  ppl_Octagonal_Shape_mpq_class_refine_with_constraint/2,
	  ppl_Octagonal_Shape_mpq_class_refine_with_congruence/2



,
	  ppl_Octagonal_Shape_mpq_class_refine_with_constraints/2,
	  ppl_Octagonal_Shape_mpq_class_refine_with_congruences/2



,
	  ppl_Octagonal_Shape_mpq_class_intersection_assign/2,
	  ppl_Octagonal_Shape_mpq_class_upper_bound_assign/2,
	  ppl_Octagonal_Shape_mpq_class_difference_assign/2,
	  ppl_Octagonal_Shape_mpq_class_concatenate_assign/2,
	  ppl_Octagonal_Shape_mpq_class_time_elapse_assign/2



,
	  ppl_Octagonal_Shape_mpq_class_upper_bound_assign_if_exact/2



,
	  ppl_Octagonal_Shape_mpq_class_simplify_using_context_assign/3


,
	  ppl_Octagonal_Shape_mpq_class_constrains/2


,
	  ppl_Octagonal_Shape_mpq_class_unconstrain_space_dimension/2


,
	  ppl_Octagonal_Shape_mpq_class_unconstrain_space_dimensions/2


,
	  ppl_Octagonal_Shape_mpq_class_affine_image/4,
	  ppl_Octagonal_Shape_mpq_class_affine_preimage/4



,
	  ppl_Octagonal_Shape_mpq_class_bounded_affine_image/5,
	  ppl_Octagonal_Shape_mpq_class_bounded_affine_preimage/5



,
	  ppl_Octagonal_Shape_mpq_class_generalized_affine_image/5,
	  ppl_Octagonal_Shape_mpq_class_generalized_affine_preimage/5



,
	  ppl_Octagonal_Shape_mpq_class_generalized_affine_image_lhs_rhs/4,
	  ppl_Octagonal_Shape_mpq_class_generalized_affine_preimage_lhs_rhs/4



,
	  ppl_Octagonal_Shape_mpq_class_add_space_dimensions_and_embed/2,
	  ppl_Octagonal_Shape_mpq_class_add_space_dimensions_and_project/2



,
	  ppl_Octagonal_Shape_mpq_class_remove_space_dimensions/2


,
	  ppl_Octagonal_Shape_mpq_class_remove_higher_space_dimensions/2


,
	  ppl_Octagonal_Shape_mpq_class_expand_space_dimension/3


,
	  ppl_Octagonal_Shape_mpq_class_fold_space_dimensions/3


,
	  ppl_Octagonal_Shape_mpq_class_map_space_dimensions/2


,
	  ppl_Octagonal_Shape_mpq_class_drop_some_non_integer_points/2


,
	  ppl_Octagonal_Shape_mpq_class_drop_some_non_integer_points_2/3


,
	  ppl_Octagonal_Shape_mpq_class_ascii_dump/1


,
	  ppl_Octagonal_Shape_mpq_class_external_memory_in_bytes/2,
	  ppl_Octagonal_Shape_mpq_class_total_memory_in_bytes/2



,
	  ppl_Octagonal_Shape_mpq_class_BHMZ05_widening_assign_with_tokens/4



,
	  ppl_Octagonal_Shape_mpq_class_BHMZ05_widening_assign/2



,
	  ppl_Octagonal_Shape_mpq_class_widening_assign_with_tokens/4


,
	  ppl_Octagonal_Shape_mpq_class_widening_assign/2


,
	  ppl_Octagonal_Shape_mpq_class_limited_BHMZ05_extrapolation_assign_with_tokens/5,
	  ppl_Octagonal_Shape_mpq_class_limited_CC76_extrapolation_assign_with_tokens/5




,
	  ppl_Octagonal_Shape_mpq_class_limited_BHMZ05_extrapolation_assign/3,
	  ppl_Octagonal_Shape_mpq_class_limited_CC76_extrapolation_assign/3




,
	  ppl_Octagonal_Shape_mpq_class_CC76_extrapolation_assign_with_tokens/4



,
	  ppl_Octagonal_Shape_mpq_class_CC76_extrapolation_assign/2



,
	  ppl_Octagonal_Shape_mpq_class_CC76_narrowing_assign/2



,
	  ppl_Octagonal_Shape_mpq_class_linear_partition/4



,
	  ppl_Octagonal_Shape_mpq_class_wrap_assign/8


,
	  ppl_termination_test_MS_Octagonal_Shape_mpq_class/1,
	  ppl_termination_test_PR_Octagonal_Shape_mpq_class/1




,
	  ppl_one_affine_ranking_function_MS_Octagonal_Shape_mpq_class/2,
	  ppl_one_affine_ranking_function_PR_Octagonal_Shape_mpq_class/2




,
	  ppl_all_affine_ranking_functions_MS_Octagonal_Shape_mpq_class/2,
	  ppl_all_affine_ranking_functions_PR_Octagonal_Shape_mpq_class/2




,
	  ppl_all_affine_quasi_ranking_functions_MS_Octagonal_Shape_mpq_class/3



,
	  ppl_termination_test_MS_Octagonal_Shape_mpq_class_2/2,
	  ppl_termination_test_PR_Octagonal_Shape_mpq_class_2/2




,
	  ppl_one_affine_ranking_function_MS_Octagonal_Shape_mpq_class_2/3,
	  ppl_one_affine_ranking_function_PR_Octagonal_Shape_mpq_class_2/3




,
	  ppl_all_affine_ranking_functions_MS_Octagonal_Shape_mpq_class_2/3,
	  ppl_all_affine_ranking_functions_PR_Octagonal_Shape_mpq_class_2/3




,
	  ppl_all_affine_quasi_ranking_functions_MS_Octagonal_Shape_mpq_class_2/4




,
	  ppl_delete_Constraints_Product_C_Polyhedron_Grid/1


,
	  ppl_new_Constraints_Product_C_Polyhedron_Grid_from_space_dimension/3



,
	  ppl_new_Constraints_Product_C_Polyhedron_Grid_from_C_Polyhedron/2,
	  ppl_new_Constraints_Product_C_Polyhedron_Grid_from_NNC_Polyhedron/2,
	  ppl_new_Constraints_Product_C_Polyhedron_Grid_from_Grid/2,
	  ppl_new_Constraints_Product_C_Polyhedron_Grid_from_Rational_Box/2,
	  ppl_new_Constraints_Product_C_Polyhedron_Grid_from_BD_Shape_mpz_class/2,
	  ppl_new_Constraints_Product_C_Polyhedron_Grid_from_BD_Shape_mpq_class/2,
	  ppl_new_Constraints_Product_C_Polyhedron_Grid_from_Octagonal_Shape_mpz_class/2,
	  ppl_new_Constraints_Product_C_Polyhedron_Grid_from_Octagonal_Shape_mpq_class/2,
	  ppl_new_Constraints_Product_C_Polyhedron_Grid_from_Double_Box/2,
	  ppl_new_Constraints_Product_C_Polyhedron_Grid_from_BD_Shape_double/2,
	  ppl_new_Constraints_Product_C_Polyhedron_Grid_from_Octagonal_Shape_double/2,
	  ppl_new_Constraints_Product_C_Polyhedron_Grid_from_Constraints_Product_C_Polyhedron_Grid/2




,
	  ppl_new_Constraints_Product_C_Polyhedron_Grid_from_C_Polyhedron_with_complexity/3,
	  ppl_new_Constraints_Product_C_Polyhedron_Grid_from_NNC_Polyhedron_with_complexity/3,
	  ppl_new_Constraints_Product_C_Polyhedron_Grid_from_Grid_with_complexity/3,
	  ppl_new_Constraints_Product_C_Polyhedron_Grid_from_Rational_Box_with_complexity/3,
	  ppl_new_Constraints_Product_C_Polyhedron_Grid_from_BD_Shape_mpz_class_with_complexity/3,
	  ppl_new_Constraints_Product_C_Polyhedron_Grid_from_BD_Shape_mpq_class_with_complexity/3,
	  ppl_new_Constraints_Product_C_Polyhedron_Grid_from_Octagonal_Shape_mpz_class_with_complexity/3,
	  ppl_new_Constraints_Product_C_Polyhedron_Grid_from_Octagonal_Shape_mpq_class_with_complexity/3,
	  ppl_new_Constraints_Product_C_Polyhedron_Grid_from_Double_Box_with_complexity/3,
	  ppl_new_Constraints_Product_C_Polyhedron_Grid_from_BD_Shape_double_with_complexity/3,
	  ppl_new_Constraints_Product_C_Polyhedron_Grid_from_Octagonal_Shape_double_with_complexity/3,
	  ppl_new_Constraints_Product_C_Polyhedron_Grid_from_Constraints_Product_C_Polyhedron_Grid_with_complexity/3




,
	  ppl_new_Constraints_Product_C_Polyhedron_Grid_from_constraints/2,
	  ppl_new_Constraints_Product_C_Polyhedron_Grid_from_congruences/2




,
	  ppl_Constraints_Product_C_Polyhedron_Grid_swap/2


,
	  ppl_Constraints_Product_C_Polyhedron_Grid_space_dimension/2,
	  ppl_Constraints_Product_C_Polyhedron_Grid_affine_dimension/2



,
	  ppl_Constraints_Product_C_Polyhedron_Grid_relation_with_constraint/3,
	  ppl_Constraints_Product_C_Polyhedron_Grid_relation_with_generator/3,
	  ppl_Constraints_Product_C_Polyhedron_Grid_relation_with_congruence/3



,
	  ppl_Constraints_Product_C_Polyhedron_Grid_is_empty/1,
	  ppl_Constraints_Product_C_Polyhedron_Grid_is_universe/1,
	  ppl_Constraints_Product_C_Polyhedron_Grid_is_bounded/1,
	  ppl_Constraints_Product_C_Polyhedron_Grid_is_topologically_closed/1,
	  ppl_Constraints_Product_C_Polyhedron_Grid_is_discrete/1



,
	  ppl_Constraints_Product_C_Polyhedron_Grid_topological_closure_assign/1



,
	  ppl_Constraints_Product_C_Polyhedron_Grid_bounds_from_above/2,
	  ppl_Constraints_Product_C_Polyhedron_Grid_bounds_from_below/2



,
	  ppl_Constraints_Product_C_Polyhedron_Grid_maximize/5,
	  ppl_Constraints_Product_C_Polyhedron_Grid_minimize/5



,
	  ppl_Constraints_Product_C_Polyhedron_Grid_maximize_with_point/6,
	  ppl_Constraints_Product_C_Polyhedron_Grid_minimize_with_point/6



,
	  ppl_Constraints_Product_C_Polyhedron_Grid_contains_Constraints_Product_C_Polyhedron_Grid/2,
	  ppl_Constraints_Product_C_Polyhedron_Grid_strictly_contains_Constraints_Product_C_Polyhedron_Grid/2,
	  ppl_Constraints_Product_C_Polyhedron_Grid_is_disjoint_from_Constraints_Product_C_Polyhedron_Grid/2



,
	  ppl_Constraints_Product_C_Polyhedron_Grid_equals_Constraints_Product_C_Polyhedron_Grid/2


,
	  ppl_Constraints_Product_C_Polyhedron_Grid_OK/1


,
	  ppl_Constraints_Product_C_Polyhedron_Grid_add_constraint/2,
	  ppl_Constraints_Product_C_Polyhedron_Grid_add_congruence/2



,
	  ppl_Constraints_Product_C_Polyhedron_Grid_add_constraints/2,
	  ppl_Constraints_Product_C_Polyhedron_Grid_add_congruences/2



,
	  ppl_Constraints_Product_C_Polyhedron_Grid_refine_with_constraint/2,
	  ppl_Constraints_Product_C_Polyhedron_Grid_refine_with_congruence/2



,
	  ppl_Constraints_Product_C_Polyhedron_Grid_refine_with_constraints/2,
	  ppl_Constraints_Product_C_Polyhedron_Grid_refine_with_congruences/2



,
	  ppl_Constraints_Product_C_Polyhedron_Grid_intersection_assign/2,
	  ppl_Constraints_Product_C_Polyhedron_Grid_upper_bound_assign/2,
	  ppl_Constraints_Product_C_Polyhedron_Grid_difference_assign/2,
	  ppl_Constraints_Product_C_Polyhedron_Grid_concatenate_assign/2,
	  ppl_Constraints_Product_C_Polyhedron_Grid_time_elapse_assign/2



,
	  ppl_Constraints_Product_C_Polyhedron_Grid_upper_bound_assign_if_exact/2



,
	  ppl_Constraints_Product_C_Polyhedron_Grid_constrains/2


,
	  ppl_Constraints_Product_C_Polyhedron_Grid_unconstrain_space_dimension/2


,
	  ppl_Constraints_Product_C_Polyhedron_Grid_unconstrain_space_dimensions/2


,
	  ppl_Constraints_Product_C_Polyhedron_Grid_affine_image/4,
	  ppl_Constraints_Product_C_Polyhedron_Grid_affine_preimage/4



,
	  ppl_Constraints_Product_C_Polyhedron_Grid_bounded_affine_image/5,
	  ppl_Constraints_Product_C_Polyhedron_Grid_bounded_affine_preimage/5



,
	  ppl_Constraints_Product_C_Polyhedron_Grid_generalized_affine_image/5,
	  ppl_Constraints_Product_C_Polyhedron_Grid_generalized_affine_preimage/5



,
	  ppl_Constraints_Product_C_Polyhedron_Grid_generalized_affine_image_lhs_rhs/4,
	  ppl_Constraints_Product_C_Polyhedron_Grid_generalized_affine_preimage_lhs_rhs/4



,
	  ppl_Constraints_Product_C_Polyhedron_Grid_add_space_dimensions_and_embed/2,
	  ppl_Constraints_Product_C_Polyhedron_Grid_add_space_dimensions_and_project/2



,
	  ppl_Constraints_Product_C_Polyhedron_Grid_remove_space_dimensions/2


,
	  ppl_Constraints_Product_C_Polyhedron_Grid_remove_higher_space_dimensions/2


,
	  ppl_Constraints_Product_C_Polyhedron_Grid_expand_space_dimension/3


,
	  ppl_Constraints_Product_C_Polyhedron_Grid_fold_space_dimensions/3


,
	  ppl_Constraints_Product_C_Polyhedron_Grid_map_space_dimensions/2


,
	  ppl_Constraints_Product_C_Polyhedron_Grid_drop_some_non_integer_points/2


,
	  ppl_Constraints_Product_C_Polyhedron_Grid_drop_some_non_integer_points_2/3


,
	  ppl_Constraints_Product_C_Polyhedron_Grid_ascii_dump/1


,
	  ppl_Constraints_Product_C_Polyhedron_Grid_external_memory_in_bytes/2,
	  ppl_Constraints_Product_C_Polyhedron_Grid_total_memory_in_bytes/2



,
	  ppl_Constraints_Product_C_Polyhedron_Grid_widening_assign_with_tokens/4


,
	  ppl_Constraints_Product_C_Polyhedron_Grid_widening_assign/2



,
	  ppl_delete_Pointset_Powerset_C_Polyhedron/1


,
	  ppl_new_Pointset_Powerset_C_Polyhedron_from_space_dimension/3



,
	  ppl_new_Pointset_Powerset_C_Polyhedron_from_Pointset_Powerset_C_Polyhedron/2,
	  ppl_new_Pointset_Powerset_C_Polyhedron_from_C_Polyhedron/2




,
	  ppl_new_Pointset_Powerset_C_Polyhedron_from_Pointset_Powerset_C_Polyhedron_with_complexity/3,
	  ppl_new_Pointset_Powerset_C_Polyhedron_from_C_Polyhedron_with_complexity/3




,
	  ppl_new_Pointset_Powerset_C_Polyhedron_from_constraints/2,
	  ppl_new_Pointset_Powerset_C_Polyhedron_from_congruences/2




,
	  ppl_Pointset_Powerset_C_Polyhedron_swap/2


,
	  ppl_Pointset_Powerset_C_Polyhedron_space_dimension/2,
	  ppl_Pointset_Powerset_C_Polyhedron_affine_dimension/2



,
	  ppl_Pointset_Powerset_C_Polyhedron_relation_with_constraint/3,
	  ppl_Pointset_Powerset_C_Polyhedron_relation_with_generator/3,
	  ppl_Pointset_Powerset_C_Polyhedron_relation_with_congruence/3



,
	  ppl_Pointset_Powerset_C_Polyhedron_is_empty/1,
	  ppl_Pointset_Powerset_C_Polyhedron_is_universe/1,
	  ppl_Pointset_Powerset_C_Polyhedron_is_bounded/1,
	  ppl_Pointset_Powerset_C_Polyhedron_contains_integer_point/1,
	  ppl_Pointset_Powerset_C_Polyhedron_is_topologically_closed/1,
	  ppl_Pointset_Powerset_C_Polyhedron_is_discrete/1



,
	  ppl_Pointset_Powerset_C_Polyhedron_topological_closure_assign/1,
	  ppl_Pointset_Powerset_C_Polyhedron_pairwise_reduce/1,
	  ppl_Pointset_Powerset_C_Polyhedron_omega_reduce/1



,
	  ppl_Pointset_Powerset_C_Polyhedron_bounds_from_above/2,
	  ppl_Pointset_Powerset_C_Polyhedron_bounds_from_below/2



,
	  ppl_Pointset_Powerset_C_Polyhedron_maximize/5,
	  ppl_Pointset_Powerset_C_Polyhedron_minimize/5



,
	  ppl_Pointset_Powerset_C_Polyhedron_maximize_with_point/6,
	  ppl_Pointset_Powerset_C_Polyhedron_minimize_with_point/6



,
	  ppl_Pointset_Powerset_C_Polyhedron_contains_Pointset_Powerset_C_Polyhedron/2,
	  ppl_Pointset_Powerset_C_Polyhedron_strictly_contains_Pointset_Powerset_C_Polyhedron/2,
	  ppl_Pointset_Powerset_C_Polyhedron_is_disjoint_from_Pointset_Powerset_C_Polyhedron/2,
	  ppl_Pointset_Powerset_C_Polyhedron_geometrically_covers_Pointset_Powerset_C_Polyhedron/2,
	  ppl_Pointset_Powerset_C_Polyhedron_geometrically_equals_Pointset_Powerset_C_Polyhedron/2



,
	  ppl_Pointset_Powerset_C_Polyhedron_equals_Pointset_Powerset_C_Polyhedron/2


,
	  ppl_Pointset_Powerset_C_Polyhedron_OK/1


,
	  ppl_Pointset_Powerset_C_Polyhedron_add_constraint/2,
	  ppl_Pointset_Powerset_C_Polyhedron_add_congruence/2



,
	  ppl_Pointset_Powerset_C_Polyhedron_add_constraints/2,
	  ppl_Pointset_Powerset_C_Polyhedron_add_congruences/2



,
	  ppl_Pointset_Powerset_C_Polyhedron_refine_with_constraint/2,
	  ppl_Pointset_Powerset_C_Polyhedron_refine_with_congruence/2



,
	  ppl_Pointset_Powerset_C_Polyhedron_refine_with_constraints/2,
	  ppl_Pointset_Powerset_C_Polyhedron_refine_with_congruences/2



,
	  ppl_Pointset_Powerset_C_Polyhedron_intersection_assign/2,
	  ppl_Pointset_Powerset_C_Polyhedron_upper_bound_assign/2,
	  ppl_Pointset_Powerset_C_Polyhedron_difference_assign/2,
	  ppl_Pointset_Powerset_C_Polyhedron_concatenate_assign/2,
	  ppl_Pointset_Powerset_C_Polyhedron_time_elapse_assign/2



,
	  ppl_Pointset_Powerset_C_Polyhedron_upper_bound_assign_if_exact/2



,
	  ppl_Pointset_Powerset_C_Polyhedron_simplify_using_context_assign/3


,
	  ppl_Pointset_Powerset_C_Polyhedron_constrains/2


,
	  ppl_Pointset_Powerset_C_Polyhedron_unconstrain_space_dimension/2


,
	  ppl_Pointset_Powerset_C_Polyhedron_unconstrain_space_dimensions/2


,
	  ppl_Pointset_Powerset_C_Polyhedron_affine_image/4,
	  ppl_Pointset_Powerset_C_Polyhedron_affine_preimage/4



,
	  ppl_Pointset_Powerset_C_Polyhedron_bounded_affine_image/5,
	  ppl_Pointset_Powerset_C_Polyhedron_bounded_affine_preimage/5



,
	  ppl_Pointset_Powerset_C_Polyhedron_generalized_affine_image/5,
	  ppl_Pointset_Powerset_C_Polyhedron_generalized_affine_preimage/5



,
	  ppl_Pointset_Powerset_C_Polyhedron_generalized_affine_image_lhs_rhs/4,
	  ppl_Pointset_Powerset_C_Polyhedron_generalized_affine_preimage_lhs_rhs/4



,
	  ppl_Pointset_Powerset_C_Polyhedron_add_space_dimensions_and_embed/2,
	  ppl_Pointset_Powerset_C_Polyhedron_add_space_dimensions_and_project/2



,
	  ppl_Pointset_Powerset_C_Polyhedron_remove_space_dimensions/2


,
	  ppl_Pointset_Powerset_C_Polyhedron_remove_higher_space_dimensions/2


,
	  ppl_Pointset_Powerset_C_Polyhedron_expand_space_dimension/3


,
	  ppl_Pointset_Powerset_C_Polyhedron_fold_space_dimensions/3


,
	  ppl_Pointset_Powerset_C_Polyhedron_map_space_dimensions/2


,
	  ppl_Pointset_Powerset_C_Polyhedron_drop_some_non_integer_points/2


,
	  ppl_Pointset_Powerset_C_Polyhedron_drop_some_non_integer_points_2/3


,
	  ppl_Pointset_Powerset_C_Polyhedron_ascii_dump/1


,
	  ppl_Pointset_Powerset_C_Polyhedron_external_memory_in_bytes/2,
	  ppl_Pointset_Powerset_C_Polyhedron_total_memory_in_bytes/2,
	  ppl_Pointset_Powerset_C_Polyhedron_size/2



,
	  ppl_new_Pointset_Powerset_C_Polyhedron_iterator_from_iterator/2


,
	  ppl_Pointset_Powerset_C_Polyhedron_begin_iterator/2,
	  ppl_Pointset_Powerset_C_Polyhedron_end_iterator/2



,
	  ppl_Pointset_Powerset_C_Polyhedron_iterator_equals_iterator/2


,
	  ppl_Pointset_Powerset_C_Polyhedron_increment_iterator/1,
	  ppl_Pointset_Powerset_C_Polyhedron_decrement_iterator/1



,
	  ppl_Pointset_Powerset_C_Polyhedron_get_disjunct/2


,
	  ppl_delete_Pointset_Powerset_C_Polyhedron_iterator/1


,
	  ppl_Pointset_Powerset_C_Polyhedron_add_disjunct/2


,
	  ppl_Pointset_Powerset_C_Polyhedron_drop_disjunct/2


,
	  ppl_Pointset_Powerset_C_Polyhedron_drop_disjuncts/3


,
	  ppl_Pointset_Powerset_C_Polyhedron_BHZ03_BHRZ03_BHRZ03_widening_assign/2,
	  ppl_Pointset_Powerset_C_Polyhedron_BHZ03_H79_H79_widening_assign/2



,
	  ppl_Pointset_Powerset_C_Polyhedron_BGP99_BHRZ03_extrapolation_assign/3,
	  ppl_Pointset_Powerset_C_Polyhedron_BGP99_H79_extrapolation_assign/3




,
	  ppl_delete_Pointset_Powerset_NNC_Polyhedron/1


,
	  ppl_new_Pointset_Powerset_NNC_Polyhedron_from_space_dimension/3



,
	  ppl_new_Pointset_Powerset_NNC_Polyhedron_from_Pointset_Powerset_NNC_Polyhedron/2,
	  ppl_new_Pointset_Powerset_NNC_Polyhedron_from_NNC_Polyhedron/2




,
	  ppl_new_Pointset_Powerset_NNC_Polyhedron_from_Pointset_Powerset_NNC_Polyhedron_with_complexity/3,
	  ppl_new_Pointset_Powerset_NNC_Polyhedron_from_NNC_Polyhedron_with_complexity/3




,
	  ppl_new_Pointset_Powerset_NNC_Polyhedron_from_constraints/2,
	  ppl_new_Pointset_Powerset_NNC_Polyhedron_from_congruences/2




,
	  ppl_Pointset_Powerset_NNC_Polyhedron_swap/2


,
	  ppl_Pointset_Powerset_NNC_Polyhedron_space_dimension/2,
	  ppl_Pointset_Powerset_NNC_Polyhedron_affine_dimension/2



,
	  ppl_Pointset_Powerset_NNC_Polyhedron_relation_with_constraint/3,
	  ppl_Pointset_Powerset_NNC_Polyhedron_relation_with_generator/3,
	  ppl_Pointset_Powerset_NNC_Polyhedron_relation_with_congruence/3



,
	  ppl_Pointset_Powerset_NNC_Polyhedron_is_empty/1,
	  ppl_Pointset_Powerset_NNC_Polyhedron_is_universe/1,
	  ppl_Pointset_Powerset_NNC_Polyhedron_is_bounded/1,
	  ppl_Pointset_Powerset_NNC_Polyhedron_contains_integer_point/1,
	  ppl_Pointset_Powerset_NNC_Polyhedron_is_topologically_closed/1,
	  ppl_Pointset_Powerset_NNC_Polyhedron_is_discrete/1



,
	  ppl_Pointset_Powerset_NNC_Polyhedron_topological_closure_assign/1,
	  ppl_Pointset_Powerset_NNC_Polyhedron_pairwise_reduce/1,
	  ppl_Pointset_Powerset_NNC_Polyhedron_omega_reduce/1



,
	  ppl_Pointset_Powerset_NNC_Polyhedron_bounds_from_above/2,
	  ppl_Pointset_Powerset_NNC_Polyhedron_bounds_from_below/2



,
	  ppl_Pointset_Powerset_NNC_Polyhedron_maximize/5,
	  ppl_Pointset_Powerset_NNC_Polyhedron_minimize/5



,
	  ppl_Pointset_Powerset_NNC_Polyhedron_maximize_with_point/6,
	  ppl_Pointset_Powerset_NNC_Polyhedron_minimize_with_point/6



,
	  ppl_Pointset_Powerset_NNC_Polyhedron_contains_Pointset_Powerset_NNC_Polyhedron/2,
	  ppl_Pointset_Powerset_NNC_Polyhedron_strictly_contains_Pointset_Powerset_NNC_Polyhedron/2,
	  ppl_Pointset_Powerset_NNC_Polyhedron_is_disjoint_from_Pointset_Powerset_NNC_Polyhedron/2,
	  ppl_Pointset_Powerset_NNC_Polyhedron_geometrically_covers_Pointset_Powerset_NNC_Polyhedron/2,
	  ppl_Pointset_Powerset_NNC_Polyhedron_geometrically_equals_Pointset_Powerset_NNC_Polyhedron/2



,
	  ppl_Pointset_Powerset_NNC_Polyhedron_equals_Pointset_Powerset_NNC_Polyhedron/2


,
	  ppl_Pointset_Powerset_NNC_Polyhedron_OK/1


,
	  ppl_Pointset_Powerset_NNC_Polyhedron_add_constraint/2,
	  ppl_Pointset_Powerset_NNC_Polyhedron_add_congruence/2



,
	  ppl_Pointset_Powerset_NNC_Polyhedron_add_constraints/2,
	  ppl_Pointset_Powerset_NNC_Polyhedron_add_congruences/2



,
	  ppl_Pointset_Powerset_NNC_Polyhedron_refine_with_constraint/2,
	  ppl_Pointset_Powerset_NNC_Polyhedron_refine_with_congruence/2



,
	  ppl_Pointset_Powerset_NNC_Polyhedron_refine_with_constraints/2,
	  ppl_Pointset_Powerset_NNC_Polyhedron_refine_with_congruences/2



,
	  ppl_Pointset_Powerset_NNC_Polyhedron_intersection_assign/2,
	  ppl_Pointset_Powerset_NNC_Polyhedron_upper_bound_assign/2,
	  ppl_Pointset_Powerset_NNC_Polyhedron_difference_assign/2,
	  ppl_Pointset_Powerset_NNC_Polyhedron_concatenate_assign/2,
	  ppl_Pointset_Powerset_NNC_Polyhedron_time_elapse_assign/2



,
	  ppl_Pointset_Powerset_NNC_Polyhedron_upper_bound_assign_if_exact/2



,
	  ppl_Pointset_Powerset_NNC_Polyhedron_simplify_using_context_assign/3


,
	  ppl_Pointset_Powerset_NNC_Polyhedron_constrains/2


,
	  ppl_Pointset_Powerset_NNC_Polyhedron_unconstrain_space_dimension/2


,
	  ppl_Pointset_Powerset_NNC_Polyhedron_unconstrain_space_dimensions/2


,
	  ppl_Pointset_Powerset_NNC_Polyhedron_affine_image/4,
	  ppl_Pointset_Powerset_NNC_Polyhedron_affine_preimage/4



,
	  ppl_Pointset_Powerset_NNC_Polyhedron_bounded_affine_image/5,
	  ppl_Pointset_Powerset_NNC_Polyhedron_bounded_affine_preimage/5



,
	  ppl_Pointset_Powerset_NNC_Polyhedron_generalized_affine_image/5,
	  ppl_Pointset_Powerset_NNC_Polyhedron_generalized_affine_preimage/5



,
	  ppl_Pointset_Powerset_NNC_Polyhedron_generalized_affine_image_lhs_rhs/4,
	  ppl_Pointset_Powerset_NNC_Polyhedron_generalized_affine_preimage_lhs_rhs/4



,
	  ppl_Pointset_Powerset_NNC_Polyhedron_add_space_dimensions_and_embed/2,
	  ppl_Pointset_Powerset_NNC_Polyhedron_add_space_dimensions_and_project/2



,
	  ppl_Pointset_Powerset_NNC_Polyhedron_remove_space_dimensions/2


,
	  ppl_Pointset_Powerset_NNC_Polyhedron_remove_higher_space_dimensions/2


,
	  ppl_Pointset_Powerset_NNC_Polyhedron_expand_space_dimension/3


,
	  ppl_Pointset_Powerset_NNC_Polyhedron_fold_space_dimensions/3


,
	  ppl_Pointset_Powerset_NNC_Polyhedron_map_space_dimensions/2


,
	  ppl_Pointset_Powerset_NNC_Polyhedron_drop_some_non_integer_points/2


,
	  ppl_Pointset_Powerset_NNC_Polyhedron_drop_some_non_integer_points_2/3


,
	  ppl_Pointset_Powerset_NNC_Polyhedron_ascii_dump/1


,
	  ppl_Pointset_Powerset_NNC_Polyhedron_external_memory_in_bytes/2,
	  ppl_Pointset_Powerset_NNC_Polyhedron_total_memory_in_bytes/2,
	  ppl_Pointset_Powerset_NNC_Polyhedron_size/2



,
	  ppl_new_Pointset_Powerset_NNC_Polyhedron_iterator_from_iterator/2


,
	  ppl_Pointset_Powerset_NNC_Polyhedron_begin_iterator/2,
	  ppl_Pointset_Powerset_NNC_Polyhedron_end_iterator/2



,
	  ppl_Pointset_Powerset_NNC_Polyhedron_iterator_equals_iterator/2


,
	  ppl_Pointset_Powerset_NNC_Polyhedron_increment_iterator/1,
	  ppl_Pointset_Powerset_NNC_Polyhedron_decrement_iterator/1



,
	  ppl_Pointset_Powerset_NNC_Polyhedron_get_disjunct/2


,
	  ppl_delete_Pointset_Powerset_NNC_Polyhedron_iterator/1


,
	  ppl_Pointset_Powerset_NNC_Polyhedron_add_disjunct/2


,
	  ppl_Pointset_Powerset_NNC_Polyhedron_drop_disjunct/2


,
	  ppl_Pointset_Powerset_NNC_Polyhedron_drop_disjuncts/3


,
	  ppl_Pointset_Powerset_NNC_Polyhedron_BHZ03_BHRZ03_BHRZ03_widening_assign/2,
	  ppl_Pointset_Powerset_NNC_Polyhedron_BHZ03_H79_H79_widening_assign/2



,
	  ppl_Pointset_Powerset_NNC_Polyhedron_BGP99_BHRZ03_extrapolation_assign/3,
	  ppl_Pointset_Powerset_NNC_Polyhedron_BGP99_H79_extrapolation_assign/3




,
	  ppl_delete_Double_Box/1


,
	  ppl_new_Double_Box_from_space_dimension/3



,
	  ppl_new_Double_Box_from_C_Polyhedron/2,
	  ppl_new_Double_Box_from_NNC_Polyhedron/2,
	  ppl_new_Double_Box_from_Grid/2,
	  ppl_new_Double_Box_from_Rational_Box/2,
	  ppl_new_Double_Box_from_BD_Shape_mpz_class/2,
	  ppl_new_Double_Box_from_BD_Shape_mpq_class/2,
	  ppl_new_Double_Box_from_Octagonal_Shape_mpz_class/2,
	  ppl_new_Double_Box_from_Octagonal_Shape_mpq_class/2,
	  ppl_new_Double_Box_from_Double_Box/2,
	  ppl_new_Double_Box_from_BD_Shape_double/2,
	  ppl_new_Double_Box_from_Octagonal_Shape_double/2




,
	  ppl_new_Double_Box_from_C_Polyhedron_with_complexity/3,
	  ppl_new_Double_Box_from_NNC_Polyhedron_with_complexity/3,
	  ppl_new_Double_Box_from_Grid_with_complexity/3,
	  ppl_new_Double_Box_from_Rational_Box_with_complexity/3,
	  ppl_new_Double_Box_from_BD_Shape_mpz_class_with_complexity/3,
	  ppl_new_Double_Box_from_BD_Shape_mpq_class_with_complexity/3,
	  ppl_new_Double_Box_from_Octagonal_Shape_mpz_class_with_complexity/3,
	  ppl_new_Double_Box_from_Octagonal_Shape_mpq_class_with_complexity/3,
	  ppl_new_Double_Box_from_Double_Box_with_complexity/3,
	  ppl_new_Double_Box_from_BD_Shape_double_with_complexity/3,
	  ppl_new_Double_Box_from_Octagonal_Shape_double_with_complexity/3




,
	  ppl_new_Double_Box_from_constraints/2,
	  ppl_new_Double_Box_from_congruences/2,
	  ppl_new_Double_Box_from_generators/2




,
	  ppl_Double_Box_swap/2


,
	  ppl_Double_Box_space_dimension/2,
	  ppl_Double_Box_affine_dimension/2



,
	  ppl_Double_Box_relation_with_constraint/3,
	  ppl_Double_Box_relation_with_generator/3,
	  ppl_Double_Box_relation_with_congruence/3



,
	  ppl_Double_Box_get_constraints/2,
	  ppl_Double_Box_get_congruences/2



,
	  ppl_Double_Box_get_minimized_constraints/2,
	  ppl_Double_Box_get_minimized_congruences/2



,
	  ppl_Double_Box_is_empty/1,
	  ppl_Double_Box_is_universe/1,
	  ppl_Double_Box_is_bounded/1,
	  ppl_Double_Box_contains_integer_point/1,
	  ppl_Double_Box_is_topologically_closed/1,
	  ppl_Double_Box_is_discrete/1



,
	  ppl_Double_Box_topological_closure_assign/1



,
	  ppl_Double_Box_bounds_from_above/2,
	  ppl_Double_Box_bounds_from_below/2



,
	  ppl_Double_Box_maximize/5,
	  ppl_Double_Box_minimize/5



,
	  ppl_Double_Box_maximize_with_point/6,
	  ppl_Double_Box_minimize_with_point/6



,
	  ppl_Double_Box_frequency/6


,
	  ppl_Double_Box_contains_Double_Box/2,
	  ppl_Double_Box_strictly_contains_Double_Box/2,
	  ppl_Double_Box_is_disjoint_from_Double_Box/2



,
	  ppl_Double_Box_equals_Double_Box/2


,
	  ppl_Double_Box_OK/1


,
	  ppl_Double_Box_add_constraint/2,
	  ppl_Double_Box_add_congruence/2



,
	  ppl_Double_Box_add_constraints/2,
	  ppl_Double_Box_add_congruences/2



,
	  ppl_Double_Box_refine_with_constraint/2,
	  ppl_Double_Box_refine_with_congruence/2



,
	  ppl_Double_Box_refine_with_constraints/2,
	  ppl_Double_Box_refine_with_congruences/2



,
	  ppl_Double_Box_intersection_assign/2,
	  ppl_Double_Box_upper_bound_assign/2,
	  ppl_Double_Box_difference_assign/2,
	  ppl_Double_Box_concatenate_assign/2,
	  ppl_Double_Box_time_elapse_assign/2



,
	  ppl_Double_Box_upper_bound_assign_if_exact/2



,
	  ppl_Double_Box_simplify_using_context_assign/3


,
	  ppl_Double_Box_constrains/2


,
	  ppl_Double_Box_unconstrain_space_dimension/2


,
	  ppl_Double_Box_unconstrain_space_dimensions/2


,
	  ppl_Double_Box_affine_image/4,
	  ppl_Double_Box_affine_preimage/4



,
	  ppl_Double_Box_bounded_affine_image/5,
	  ppl_Double_Box_bounded_affine_preimage/5



,
	  ppl_Double_Box_generalized_affine_image/5,
	  ppl_Double_Box_generalized_affine_preimage/5



,
	  ppl_Double_Box_generalized_affine_image_lhs_rhs/4,
	  ppl_Double_Box_generalized_affine_preimage_lhs_rhs/4



,
	  ppl_Double_Box_add_space_dimensions_and_embed/2,
	  ppl_Double_Box_add_space_dimensions_and_project/2



,
	  ppl_Double_Box_remove_space_dimensions/2


,
	  ppl_Double_Box_remove_higher_space_dimensions/2


,
	  ppl_Double_Box_expand_space_dimension/3


,
	  ppl_Double_Box_fold_space_dimensions/3


,
	  ppl_Double_Box_map_space_dimensions/2


,
	  ppl_Double_Box_drop_some_non_integer_points/2


,
	  ppl_Double_Box_drop_some_non_integer_points_2/3


,
	  ppl_Double_Box_ascii_dump/1


,
	  ppl_Double_Box_external_memory_in_bytes/2,
	  ppl_Double_Box_total_memory_in_bytes/2



,
	  ppl_Double_Box_CC76_widening_assign_with_tokens/4



,
	  ppl_Double_Box_CC76_widening_assign/2



,
	  ppl_Double_Box_widening_assign_with_tokens/4


,
	  ppl_Double_Box_widening_assign/2


,
	  ppl_Double_Box_limited_CC76_extrapolation_assign_with_tokens/5




,
	  ppl_Double_Box_limited_CC76_extrapolation_assign/3




,
	  ppl_Double_Box_linear_partition/4



,
	  ppl_Double_Box_wrap_assign/8


,
	  ppl_termination_test_MS_Double_Box/1,
	  ppl_termination_test_PR_Double_Box/1




,
	  ppl_one_affine_ranking_function_MS_Double_Box/2,
	  ppl_one_affine_ranking_function_PR_Double_Box/2




,
	  ppl_all_affine_ranking_functions_MS_Double_Box/2,
	  ppl_all_affine_ranking_functions_PR_Double_Box/2




,
	  ppl_all_affine_quasi_ranking_functions_MS_Double_Box/3



,
	  ppl_termination_test_MS_Double_Box_2/2,
	  ppl_termination_test_PR_Double_Box_2/2




,
	  ppl_one_affine_ranking_function_MS_Double_Box_2/3,
	  ppl_one_affine_ranking_function_PR_Double_Box_2/3




,
	  ppl_all_affine_ranking_functions_MS_Double_Box_2/3,
	  ppl_all_affine_ranking_functions_PR_Double_Box_2/3




,
	  ppl_all_affine_quasi_ranking_functions_MS_Double_Box_2/4




,
	  ppl_delete_BD_Shape_double/1


,
	  ppl_new_BD_Shape_double_from_space_dimension/3



,
	  ppl_new_BD_Shape_double_from_C_Polyhedron/2,
	  ppl_new_BD_Shape_double_from_NNC_Polyhedron/2,
	  ppl_new_BD_Shape_double_from_Grid/2,
	  ppl_new_BD_Shape_double_from_Rational_Box/2,
	  ppl_new_BD_Shape_double_from_BD_Shape_mpz_class/2,
	  ppl_new_BD_Shape_double_from_BD_Shape_mpq_class/2,
	  ppl_new_BD_Shape_double_from_Octagonal_Shape_mpz_class/2,
	  ppl_new_BD_Shape_double_from_Octagonal_Shape_mpq_class/2,
	  ppl_new_BD_Shape_double_from_Double_Box/2,
	  ppl_new_BD_Shape_double_from_BD_Shape_double/2,
	  ppl_new_BD_Shape_double_from_Octagonal_Shape_double/2




,
	  ppl_new_BD_Shape_double_from_C_Polyhedron_with_complexity/3,
	  ppl_new_BD_Shape_double_from_NNC_Polyhedron_with_complexity/3,
	  ppl_new_BD_Shape_double_from_Grid_with_complexity/3,
	  ppl_new_BD_Shape_double_from_Rational_Box_with_complexity/3,
	  ppl_new_BD_Shape_double_from_BD_Shape_mpz_class_with_complexity/3,
	  ppl_new_BD_Shape_double_from_BD_Shape_mpq_class_with_complexity/3,
	  ppl_new_BD_Shape_double_from_Octagonal_Shape_mpz_class_with_complexity/3,
	  ppl_new_BD_Shape_double_from_Octagonal_Shape_mpq_class_with_complexity/3,
	  ppl_new_BD_Shape_double_from_Double_Box_with_complexity/3,
	  ppl_new_BD_Shape_double_from_BD_Shape_double_with_complexity/3,
	  ppl_new_BD_Shape_double_from_Octagonal_Shape_double_with_complexity/3




,
	  ppl_new_BD_Shape_double_from_constraints/2,
	  ppl_new_BD_Shape_double_from_congruences/2,
	  ppl_new_BD_Shape_double_from_generators/2




,
	  ppl_BD_Shape_double_swap/2


,
	  ppl_BD_Shape_double_space_dimension/2,
	  ppl_BD_Shape_double_affine_dimension/2



,
	  ppl_BD_Shape_double_relation_with_constraint/3,
	  ppl_BD_Shape_double_relation_with_generator/3,
	  ppl_BD_Shape_double_relation_with_congruence/3



,
	  ppl_BD_Shape_double_get_constraints/2,
	  ppl_BD_Shape_double_get_congruences/2



,
	  ppl_BD_Shape_double_get_minimized_constraints/2,
	  ppl_BD_Shape_double_get_minimized_congruences/2



,
	  ppl_BD_Shape_double_is_empty/1,
	  ppl_BD_Shape_double_is_universe/1,
	  ppl_BD_Shape_double_is_bounded/1,
	  ppl_BD_Shape_double_contains_integer_point/1,
	  ppl_BD_Shape_double_is_topologically_closed/1,
	  ppl_BD_Shape_double_is_discrete/1



,
	  ppl_BD_Shape_double_topological_closure_assign/1



,
	  ppl_BD_Shape_double_bounds_from_above/2,
	  ppl_BD_Shape_double_bounds_from_below/2



,
	  ppl_BD_Shape_double_maximize/5,
	  ppl_BD_Shape_double_minimize/5



,
	  ppl_BD_Shape_double_maximize_with_point/6,
	  ppl_BD_Shape_double_minimize_with_point/6



,
	  ppl_BD_Shape_double_frequency/6


,
	  ppl_BD_Shape_double_contains_BD_Shape_double/2,
	  ppl_BD_Shape_double_strictly_contains_BD_Shape_double/2,
	  ppl_BD_Shape_double_is_disjoint_from_BD_Shape_double/2



,
	  ppl_BD_Shape_double_equals_BD_Shape_double/2


,
	  ppl_BD_Shape_double_OK/1


,
	  ppl_BD_Shape_double_add_constraint/2,
	  ppl_BD_Shape_double_add_congruence/2



,
	  ppl_BD_Shape_double_add_constraints/2,
	  ppl_BD_Shape_double_add_congruences/2



,
	  ppl_BD_Shape_double_refine_with_constraint/2,
	  ppl_BD_Shape_double_refine_with_congruence/2



,
	  ppl_BD_Shape_double_refine_with_constraints/2,
	  ppl_BD_Shape_double_refine_with_congruences/2



,
	  ppl_BD_Shape_double_intersection_assign/2,
	  ppl_BD_Shape_double_upper_bound_assign/2,
	  ppl_BD_Shape_double_difference_assign/2,
	  ppl_BD_Shape_double_concatenate_assign/2,
	  ppl_BD_Shape_double_time_elapse_assign/2



,
	  ppl_BD_Shape_double_upper_bound_assign_if_exact/2



,
	  ppl_BD_Shape_double_simplify_using_context_assign/3


,
	  ppl_BD_Shape_double_constrains/2


,
	  ppl_BD_Shape_double_unconstrain_space_dimension/2


,
	  ppl_BD_Shape_double_unconstrain_space_dimensions/2


,
	  ppl_BD_Shape_double_affine_image/4,
	  ppl_BD_Shape_double_affine_preimage/4



,
	  ppl_BD_Shape_double_bounded_affine_image/5,
	  ppl_BD_Shape_double_bounded_affine_preimage/5



,
	  ppl_BD_Shape_double_generalized_affine_image/5,
	  ppl_BD_Shape_double_generalized_affine_preimage/5



,
	  ppl_BD_Shape_double_generalized_affine_image_lhs_rhs/4,
	  ppl_BD_Shape_double_generalized_affine_preimage_lhs_rhs/4



,
	  ppl_BD_Shape_double_add_space_dimensions_and_embed/2,
	  ppl_BD_Shape_double_add_space_dimensions_and_project/2



,
	  ppl_BD_Shape_double_remove_space_dimensions/2


,
	  ppl_BD_Shape_double_remove_higher_space_dimensions/2


,
	  ppl_BD_Shape_double_expand_space_dimension/3


,
	  ppl_BD_Shape_double_fold_space_dimensions/3


,
	  ppl_BD_Shape_double_map_space_dimensions/2


,
	  ppl_BD_Shape_double_drop_some_non_integer_points/2


,
	  ppl_BD_Shape_double_drop_some_non_integer_points_2/3


,
	  ppl_BD_Shape_double_ascii_dump/1


,
	  ppl_BD_Shape_double_external_memory_in_bytes/2,
	  ppl_BD_Shape_double_total_memory_in_bytes/2



,
	  ppl_BD_Shape_double_BHMZ05_widening_assign_with_tokens/4,
	  ppl_BD_Shape_double_H79_widening_assign_with_tokens/4



,
	  ppl_BD_Shape_double_BHMZ05_widening_assign/2,
	  ppl_BD_Shape_double_H79_widening_assign/2



,
	  ppl_BD_Shape_double_widening_assign_with_tokens/4


,
	  ppl_BD_Shape_double_widening_assign/2


,
	  ppl_BD_Shape_double_limited_BHMZ05_extrapolation_assign_with_tokens/5,
	  ppl_BD_Shape_double_limited_H79_extrapolation_assign_with_tokens/5,
	  ppl_BD_Shape_double_limited_CC76_extrapolation_assign_with_tokens/5




,
	  ppl_BD_Shape_double_limited_BHMZ05_extrapolation_assign/3,
	  ppl_BD_Shape_double_limited_H79_extrapolation_assign/3,
	  ppl_BD_Shape_double_limited_CC76_extrapolation_assign/3




,
	  ppl_BD_Shape_double_CC76_extrapolation_assign_with_tokens/4



,
	  ppl_BD_Shape_double_CC76_extrapolation_assign/2



,
	  ppl_BD_Shape_double_CC76_narrowing_assign/2



,
	  ppl_BD_Shape_double_linear_partition/4



,
	  ppl_BD_Shape_double_wrap_assign/8


,
	  ppl_termination_test_MS_BD_Shape_double/1,
	  ppl_termination_test_PR_BD_Shape_double/1




,
	  ppl_one_affine_ranking_function_MS_BD_Shape_double/2,
	  ppl_one_affine_ranking_function_PR_BD_Shape_double/2




,
	  ppl_all_affine_ranking_functions_MS_BD_Shape_double/2,
	  ppl_all_affine_ranking_functions_PR_BD_Shape_double/2




,
	  ppl_all_affine_quasi_ranking_functions_MS_BD_Shape_double/3



,
	  ppl_termination_test_MS_BD_Shape_double_2/2,
	  ppl_termination_test_PR_BD_Shape_double_2/2




,
	  ppl_one_affine_ranking_function_MS_BD_Shape_double_2/3,
	  ppl_one_affine_ranking_function_PR_BD_Shape_double_2/3




,
	  ppl_all_affine_ranking_functions_MS_BD_Shape_double_2/3,
	  ppl_all_affine_ranking_functions_PR_BD_Shape_double_2/3




,
	  ppl_all_affine_quasi_ranking_functions_MS_BD_Shape_double_2/4




,
	  ppl_delete_Octagonal_Shape_double/1


,
	  ppl_new_Octagonal_Shape_double_from_space_dimension/3



,
	  ppl_new_Octagonal_Shape_double_from_C_Polyhedron/2,
	  ppl_new_Octagonal_Shape_double_from_NNC_Polyhedron/2,
	  ppl_new_Octagonal_Shape_double_from_Grid/2,
	  ppl_new_Octagonal_Shape_double_from_Rational_Box/2,
	  ppl_new_Octagonal_Shape_double_from_BD_Shape_mpz_class/2,
	  ppl_new_Octagonal_Shape_double_from_BD_Shape_mpq_class/2,
	  ppl_new_Octagonal_Shape_double_from_Octagonal_Shape_mpz_class/2,
	  ppl_new_Octagonal_Shape_double_from_Octagonal_Shape_mpq_class/2,
	  ppl_new_Octagonal_Shape_double_from_Double_Box/2,
	  ppl_new_Octagonal_Shape_double_from_BD_Shape_double/2,
	  ppl_new_Octagonal_Shape_double_from_Octagonal_Shape_double/2




,
	  ppl_new_Octagonal_Shape_double_from_C_Polyhedron_with_complexity/3,
	  ppl_new_Octagonal_Shape_double_from_NNC_Polyhedron_with_complexity/3,
	  ppl_new_Octagonal_Shape_double_from_Grid_with_complexity/3,
	  ppl_new_Octagonal_Shape_double_from_Rational_Box_with_complexity/3,
	  ppl_new_Octagonal_Shape_double_from_BD_Shape_mpz_class_with_complexity/3,
	  ppl_new_Octagonal_Shape_double_from_BD_Shape_mpq_class_with_complexity/3,
	  ppl_new_Octagonal_Shape_double_from_Octagonal_Shape_mpz_class_with_complexity/3,
	  ppl_new_Octagonal_Shape_double_from_Octagonal_Shape_mpq_class_with_complexity/3,
	  ppl_new_Octagonal_Shape_double_from_Double_Box_with_complexity/3,
	  ppl_new_Octagonal_Shape_double_from_BD_Shape_double_with_complexity/3,
	  ppl_new_Octagonal_Shape_double_from_Octagonal_Shape_double_with_complexity/3




,
	  ppl_new_Octagonal_Shape_double_from_constraints/2,
	  ppl_new_Octagonal_Shape_double_from_congruences/2,
	  ppl_new_Octagonal_Shape_double_from_generators/2




,
	  ppl_Octagonal_Shape_double_swap/2


,
	  ppl_Octagonal_Shape_double_space_dimension/2,
	  ppl_Octagonal_Shape_double_affine_dimension/2



,
	  ppl_Octagonal_Shape_double_relation_with_constraint/3,
	  ppl_Octagonal_Shape_double_relation_with_generator/3,
	  ppl_Octagonal_Shape_double_relation_with_congruence/3



,
	  ppl_Octagonal_Shape_double_get_constraints/2,
	  ppl_Octagonal_Shape_double_get_congruences/2



,
	  ppl_Octagonal_Shape_double_get_minimized_constraints/2,
	  ppl_Octagonal_Shape_double_get_minimized_congruences/2



,
	  ppl_Octagonal_Shape_double_is_empty/1,
	  ppl_Octagonal_Shape_double_is_universe/1,
	  ppl_Octagonal_Shape_double_is_bounded/1,
	  ppl_Octagonal_Shape_double_contains_integer_point/1,
	  ppl_Octagonal_Shape_double_is_topologically_closed/1,
	  ppl_Octagonal_Shape_double_is_discrete/1



,
	  ppl_Octagonal_Shape_double_topological_closure_assign/1



,
	  ppl_Octagonal_Shape_double_bounds_from_above/2,
	  ppl_Octagonal_Shape_double_bounds_from_below/2



,
	  ppl_Octagonal_Shape_double_maximize/5,
	  ppl_Octagonal_Shape_double_minimize/5



,
	  ppl_Octagonal_Shape_double_maximize_with_point/6,
	  ppl_Octagonal_Shape_double_minimize_with_point/6



,
	  ppl_Octagonal_Shape_double_frequency/6


,
	  ppl_Octagonal_Shape_double_contains_Octagonal_Shape_double/2,
	  ppl_Octagonal_Shape_double_strictly_contains_Octagonal_Shape_double/2,
	  ppl_Octagonal_Shape_double_is_disjoint_from_Octagonal_Shape_double/2



,
	  ppl_Octagonal_Shape_double_equals_Octagonal_Shape_double/2


,
	  ppl_Octagonal_Shape_double_OK/1


,
	  ppl_Octagonal_Shape_double_add_constraint/2,
	  ppl_Octagonal_Shape_double_add_congruence/2



,
	  ppl_Octagonal_Shape_double_add_constraints/2,
	  ppl_Octagonal_Shape_double_add_congruences/2



,
	  ppl_Octagonal_Shape_double_refine_with_constraint/2,
	  ppl_Octagonal_Shape_double_refine_with_congruence/2



,
	  ppl_Octagonal_Shape_double_refine_with_constraints/2,
	  ppl_Octagonal_Shape_double_refine_with_congruences/2



,
	  ppl_Octagonal_Shape_double_intersection_assign/2,
	  ppl_Octagonal_Shape_double_upper_bound_assign/2,
	  ppl_Octagonal_Shape_double_difference_assign/2,
	  ppl_Octagonal_Shape_double_concatenate_assign/2,
	  ppl_Octagonal_Shape_double_time_elapse_assign/2



,
	  ppl_Octagonal_Shape_double_upper_bound_assign_if_exact/2



,
	  ppl_Octagonal_Shape_double_simplify_using_context_assign/3


,
	  ppl_Octagonal_Shape_double_constrains/2


,
	  ppl_Octagonal_Shape_double_unconstrain_space_dimension/2


,
	  ppl_Octagonal_Shape_double_unconstrain_space_dimensions/2


,
	  ppl_Octagonal_Shape_double_affine_image/4,
	  ppl_Octagonal_Shape_double_affine_preimage/4



,
	  ppl_Octagonal_Shape_double_bounded_affine_image/5,
	  ppl_Octagonal_Shape_double_bounded_affine_preimage/5



,
	  ppl_Octagonal_Shape_double_generalized_affine_image/5,
	  ppl_Octagonal_Shape_double_generalized_affine_preimage/5



,
	  ppl_Octagonal_Shape_double_generalized_affine_image_lhs_rhs/4,
	  ppl_Octagonal_Shape_double_generalized_affine_preimage_lhs_rhs/4



,
	  ppl_Octagonal_Shape_double_add_space_dimensions_and_embed/2,
	  ppl_Octagonal_Shape_double_add_space_dimensions_and_project/2



,
	  ppl_Octagonal_Shape_double_remove_space_dimensions/2


,
	  ppl_Octagonal_Shape_double_remove_higher_space_dimensions/2


,
	  ppl_Octagonal_Shape_double_expand_space_dimension/3


,
	  ppl_Octagonal_Shape_double_fold_space_dimensions/3


,
	  ppl_Octagonal_Shape_double_map_space_dimensions/2


,
	  ppl_Octagonal_Shape_double_drop_some_non_integer_points/2


,
	  ppl_Octagonal_Shape_double_drop_some_non_integer_points_2/3


,
	  ppl_Octagonal_Shape_double_ascii_dump/1


,
	  ppl_Octagonal_Shape_double_external_memory_in_bytes/2,
	  ppl_Octagonal_Shape_double_total_memory_in_bytes/2



,
	  ppl_Octagonal_Shape_double_BHMZ05_widening_assign_with_tokens/4



,
	  ppl_Octagonal_Shape_double_BHMZ05_widening_assign/2



,
	  ppl_Octagonal_Shape_double_widening_assign_with_tokens/4


,
	  ppl_Octagonal_Shape_double_widening_assign/2


,
	  ppl_Octagonal_Shape_double_limited_BHMZ05_extrapolation_assign_with_tokens/5,
	  ppl_Octagonal_Shape_double_limited_CC76_extrapolation_assign_with_tokens/5




,
	  ppl_Octagonal_Shape_double_limited_BHMZ05_extrapolation_assign/3,
	  ppl_Octagonal_Shape_double_limited_CC76_extrapolation_assign/3




,
	  ppl_Octagonal_Shape_double_CC76_extrapolation_assign_with_tokens/4



,
	  ppl_Octagonal_Shape_double_CC76_extrapolation_assign/2



,
	  ppl_Octagonal_Shape_double_CC76_narrowing_assign/2



,
	  ppl_Octagonal_Shape_double_linear_partition/4



,
	  ppl_Octagonal_Shape_double_wrap_assign/8


,
	  ppl_termination_test_MS_Octagonal_Shape_double/1,
	  ppl_termination_test_PR_Octagonal_Shape_double/1




,
	  ppl_one_affine_ranking_function_MS_Octagonal_Shape_double/2,
	  ppl_one_affine_ranking_function_PR_Octagonal_Shape_double/2




,
	  ppl_all_affine_ranking_functions_MS_Octagonal_Shape_double/2,
	  ppl_all_affine_ranking_functions_PR_Octagonal_Shape_double/2




,
	  ppl_all_affine_quasi_ranking_functions_MS_Octagonal_Shape_double/3



,
	  ppl_termination_test_MS_Octagonal_Shape_double_2/2,
	  ppl_termination_test_PR_Octagonal_Shape_double_2/2




,
	  ppl_one_affine_ranking_function_MS_Octagonal_Shape_double_2/3,
	  ppl_one_affine_ranking_function_PR_Octagonal_Shape_double_2/3




,
	  ppl_all_affine_ranking_functions_MS_Octagonal_Shape_double_2/3,
	  ppl_all_affine_ranking_functions_PR_Octagonal_Shape_double_2/3




,
	  ppl_all_affine_quasi_ranking_functions_MS_Octagonal_Shape_double_2/4





]).


:- load_foreign_library(foreign('libppl_swiprolog')).
