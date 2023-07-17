import SphereEversion.Local.SphereEversion

open Set

-- #lint_sphere
/-
/- The `has_nonempty_instance` linter reports: -/
/- TYPES ARE MISSING NONEMPTY INSTANCES.
The following types should have an associated instance of the class
`nonempty`, or if computably possible `inhabited` or `unique`: -/
-- local/dual_pair.lean
#check @dual_pair /- nonempty/inhabited/unique instance missing -/

-- local/h_principle.lean
#check @landscape /- nonempty/inhabited/unique instance missing -/
#check @step_landscape /- nonempty/inhabited/unique instance missing -/

-- local/one_jet.lean
#check @one_jet /- nonempty/inhabited/unique instance missing -/
#check @jet_sec /- nonempty/inhabited/unique instance missing -/
#check @family_jet_sec /- nonempty/inhabited/unique instance missing -/

-- local/relation.lean
#check @rel_loc /- nonempty/inhabited/unique instance missing -/
#check @rel_loc.sol /- nonempty/inhabited/unique instance missing -/
#check @rel_loc.formal_sol /- nonempty/inhabited/unique instance missing -/
#check @rel_loc.family_formal_sol /- nonempty/inhabited/unique instance missing -/

-- loops/surrounding.lean
#check @loop_data /- nonempty/inhabited/unique instance missing -/

-- to_mathlib/equivariant.lean
#check @equivariant_map /- nonempty/inhabited/unique instance missing -/
#check @equivariant_equiv /- nonempty/inhabited/unique instance missing -/


/- The `unused_arguments` linter reports: -/
/- UNUSED ARGUMENTS. -/
-- loops/basic.lean
#check @loop.sub_apply /- argument 3: [_inst_4 : normed_space ℝ F] -/
#check @loop.norm_at_le_supr_norm_Icc /- argument 3: [_inst_4 : normed_space ℝ F] -/
#check @loop.support /- argument 4: [_inst_8 : topological_space X'] -/
#check @loop.average /- argument 5: [_inst_12 : borel_space F], argument 6: [_inst_13 : topological_space.second_countable_topology F] -/
#check @loop.is_const_of_not_mem_support /- argument 4: [_inst_4 : normed_space ℝ F], argument 7: [_inst_12 : borel_space F], argument 8: [_inst_13 : topological_space.second_countable_topology F], argument 9: [_inst_14 : complete_space F] -/

-- loops/delta_mollifier.lean
#check @loop.mollify /- argument 6: [_inst_5 : borel_space F] -/

-- to_mathlib/analysis/calculus.lean
#check @partial_deriv_fst /- argument 5: [_inst_11 : normed_space 𝕜 F] -/
#check @partial_deriv_snd /- argument 5: [_inst_3 : normed_space 𝕜 E] -/

-- to_mathlib/analysis/cont_diff.lean
#check @orthogonal_projection_singleton' /- argument 7: (hv : v ≠ 0) -/

-- to_mathlib/analysis/inner_product_space/orientation.lean
#check @orthonormal_basis.orthonormal_adjust_to_orientation /- argument 3: [_inst_2 : finite_dimensional ℝ E] -/
#check @orthonormal_basis.det_to_matrix_orthonormal_basis_of_same_orientation /- argument 3: [_inst_2 : finite_dimensional ℝ E] -/
#check @orientation.volume_form /- argument 3: [_inst_2 : finite_dimensional ℝ E] -/

-- to_mathlib/analysis/inner_product_space/projection.lean
#check @linear_isometry_equiv.apply_ne_zero /- argument 7: [_inst_7 : complete_space F] -/
#check @orthogonal_projection_eq_zero_of_mem /- argument 3: [_inst_2 : complete_space E] -/
#check @mem_orthogonal_span_singleton_iff /- argument 3: [_inst_2 : complete_space E] -/
#check @orthogonal_projection_comp_coe /- argument 3: [_inst_2 : complete_space E] -/

-- to_mathlib/analysis/normed_space/operator_norm.lean
#check @continuous.prodL' /- argument 16: [_inst_23 : has_continuous_const_smul R Fₗ], argument 17: [_inst_24 : has_continuous_const_smul R Gₗ], argument 18: [_inst_25 : smul_comm_class 𝕜 R Fₗ], argument 19: [_inst_26 : smul_comm_class 𝕜 R Gₗ] -/

-- to_mathlib/geometry/manifold/misc_manifold.lean
#check @mdifferentiable_at.prod_mk /- argument 30: [_inst_21 : smooth_manifold_with_corners I M], argument 31: [_inst_22 : smooth_manifold_with_corners I' M'], argument 32: [_inst_23 : smooth_manifold_with_corners J N] -/
#check @in_tangent_coordinates /- argument 22: [_inst_15 : topological_space N] -/

-- to_mathlib/measure_theory/basic.lean
#check @is_compact.integrable_const /- argument 6: [_inst_8 : measurable_space E] -/

-- to_mathlib/partition2.lean
#check @smooth_partition_of_unity.prod /- argument 18: [_inst_13 : sigma_compact_space M₁], argument 19: [_inst_14 : t2_space M₁] -/

-- to_mathlib/topology/path.lean
#check @continuous.path_strans /- argument 4: [_inst_6 : separated_space X] -/

-/
