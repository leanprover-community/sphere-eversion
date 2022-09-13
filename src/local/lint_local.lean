import local.sphere_eversion

open set

-- #lint_sphere

/-
/- Checking 1176 declarations (plus 1042 automatically generated ones) in the sphere eversion project (only in imported files) with 26 linters -/

/- The `fintype_finite` linter reports: -/
/- USES OF `fintype` SHOULD BE REPLACED WITH `casesI nonempty_fintype _` IN THE PROOF. -/
-- to_mathlib\analysis\inner_product_space\gram_schmidt.lean
#check @gram_schmidt_def'' /- The following `fintype` hypotheses should be replaced with
                      `casesI nonempty_fintype _` in the proof. argument 7: [_inst_4 : fintype ι] -/
#check @gram_schmidt_of_orthogonal /- The following `fintype` hypotheses should be replaced with
                      `casesI nonempty_fintype _` in the proof. argument 7: [_inst_4 : fintype ι] -/
#check @gram_schmidt_inv_triangular /- The following `fintype` hypotheses should be replaced with
                      `casesI nonempty_fintype _` in the proof. argument 7: [_inst_4 : fintype ι] -/
#check @gram_schmidt_normed_unit_length' /- The following `fintype` hypotheses should be replaced with
                      `casesI nonempty_fintype _` in the proof. argument 7: [_inst_4 : fintype ι] -/
#check @gram_schmidt_orthonormal' /- The following `fintype` hypotheses should be replaced with
                      `casesI nonempty_fintype _` in the proof. argument 7: [_inst_4 : fintype ι] -/
#check @gram_schmidt_orthonormal_basis'_apply /- The following `fintype` hypotheses should be replaced with
                      `casesI nonempty_fintype _` in the proof. argument 7: [_inst_4 : fintype ι] -/
#check @gram_schmidt_orthonormal_basis'_apply_of_orthogonal /- The following `fintype` hypotheses should be replaced with
                      `casesI nonempty_fintype _` in the proof. argument 7: [_inst_4 : fintype ι] -/
#check @inner_gram_schmidt_orthonormal_basis'_eq_zero /- The following `fintype` hypotheses should be replaced with
                      `casesI nonempty_fintype _` in the proof. argument 7: [_inst_4 : fintype ι] -/
#check @gram_schmidt_orthonormal_basis'_inv_triangular /- The following `fintype` hypotheses should be replaced with
                      `casesI nonempty_fintype _` in the proof. argument 7: [_inst_4 : fintype ι] -/
#check @gram_schmidt_orthonormal_basis'_inv_triangular' /- The following `fintype` hypotheses should be replaced with
                      `casesI nonempty_fintype _` in the proof. argument 7: [_inst_4 : fintype ι] -/
#check @gram_schmidt_orthonormal_basis'_inv_block_triangular /- The following `fintype` hypotheses should be replaced with
                      `casesI nonempty_fintype _` in the proof. argument 7: [_inst_4 : fintype ι] -/
#check @gram_schmidt_orthonormal_basis'_det /- The following `fintype` hypotheses should be replaced with
                      `casesI nonempty_fintype _` in the proof. argument 7: [_inst_4 : fintype ι] -/

-- to_mathlib\linear_algebra\determinant.lean
#check @basis.coord_units_smul /- The following `fintype` hypotheses should be replaced with
                      `casesI nonempty_fintype _` in the proof. argument 8: [_inst_5 : fintype ι] -/
#check @basis.repr_units_smul /- The following `fintype` hypotheses should be replaced with
                      `casesI nonempty_fintype _` in the proof. argument 8: [_inst_5 : fintype ι] -/

-- to_mathlib\topology\misc.lean
#check @is_open_affine_independent /- The following `fintype` hypotheses should be replaced with
                      `casesI nonempty_fintype _` in the proof. argument 8: [_inst_6 : fintype ι] -/


/- The `decidable_classical` linter reports: -/
/- USES OF `decidable` SHOULD BE REPLACED WITH `classical` IN THE PROOF. -/
-- to_mathlib\linear_algebra\determinant.lean
#check @basis.coord_units_smul /- The following `decidable` hypotheses should be replaced with
                      `classical` in the proof. argument 7: [_inst_4 : decidable_eq ι] -/
#check @basis.repr_units_smul /- The following `decidable` hypotheses should be replaced with
                      `classical` in the proof. argument 7: [_inst_4 : decidable_eq ι] -/

-- to_mathlib\smooth_barycentric.lean
#check @affine_bases_findim /- The following `decidable` hypotheses should be replaced with
                      `classical` in the proof. argument 8: [_inst_6 : decidable_eq ι] -/


/- The `has_nonempty_instance` linter reports: -/
/- TYPES ARE MISSING NONEMPTY INSTANCES.
The following types should have an associated instance of the class
`nonempty`, or if computably possible `inhabited` or `unique`: -/
-- local\dual_pair.lean
#check @dual_pair /- nonempty/inhabited/unique instance missing -/

-- local\h_principle.lean
#check @landscape /- nonempty/inhabited/unique instance missing -/
#check @step_landscape /- nonempty/inhabited/unique instance missing -/

-- local\relation.lean
#check @one_jet /- nonempty/inhabited/unique instance missing -/
#check @rel_loc /- nonempty/inhabited/unique instance missing -/
#check @rel_loc.sol /- nonempty/inhabited/unique instance missing -/
#check @rel_loc.jet_sec /- nonempty/inhabited/unique instance missing -/
#check @rel_loc.formal_sol /- nonempty/inhabited/unique instance missing -/
#check @family_jet_sec /- nonempty/inhabited/unique instance missing -/
#check @rel_loc.family_formal_sol /- nonempty/inhabited/unique instance missing -/

-- loops\reparametrization.lean
#check @smooth_surrounding_family /- nonempty/inhabited/unique instance missing -/

-- loops\surrounding.lean
#check @loop_data /- nonempty/inhabited/unique instance missing -/

-- to_mathlib\equivariant.lean
#check @equivariant_map /- nonempty/inhabited/unique instance missing -/
#check @equivariant_equiv /- nonempty/inhabited/unique instance missing -/


/- The `simp_nf` linter reports: -/
/- SOME SIMP LEMMAS ARE NOT IN SIMP-NORMAL FORM.
see note [simp-normal form] for tips how to debug this.
https://leanprover-community.github.io/mathlib_docs/notes.html#simp-normal%20form -/
-- local\h_principle.lean
#check @step_landscape.improve_step_of_support /- Left-hand side simplifies from
  ⇑(⇑(L.improve_step h N) t) x
to
  (↑𝓕.f x + (smooth_step t * L.ρ x) • corrugation L.π N (L.loop h t) x,
   L.p.update (↑𝓕.φ x) (⇑(L.loop h (smooth_step t * L.ρ x) x) (N * ⇑(L.π) x)) +
     (smooth_step t * L.ρ x) • corrugation.remainder ⇑(L.p.π) N (L.loop h 1) x)
using
  [rel_loc.formal_sol.to_jet_sec_eq_coe, step_landscape.improve_step_apply]
Try to change the left-hand side to the simplified term!
 -/

-- local\sphere_eversion.lean
#check @subtypeL_apply' /- simp can prove this:
  by simp only [submodule.coe_subtypeL, submodule.coe_subtype]
One of the lemmas above could be a duplicate.
If that's not the case try reordering lemmas or adding @[priority].
 -/

-- to_mathlib\analysis\inner_product_space\projection.lean
#check @coe_orthogonal_projection_orthogonal_singleton /- simp can prove this:
  by simp only [div_zero, mem_orthogonal_span_singleton_iff, submodule.mem_top, submodule.coe_mk, eq_self_iff_true, sub_zero, submodule.span_zero_singleton, inner_zero_left, mul_div_cancel, submodule.bot_orthogonal_eq_top, inner_zero_right, orthogonal_projection_orthogonal_singleton, smul_zero, sub_self, inner_self_eq_zero]
One of the lemmas above could be a duplicate.
If that's not the case try reordering lemmas or adding @[priority].
 -/

-- to_mathlib\linear_algebra\basis.lean
#check @basis.flag_span_succ /- Left-hand side simplifies from
  b.flag ↑k ⊔ submodule.span R {⇑b k}
to
  b.flag (⇑fin.cast_succ k) ⊔ submodule.span R {⇑b k}
using
  [fin.coe_eq_cast_succ]
Try to change the left-hand side to the simplified term!
 -/

-- to_mathlib\topology\algebra\module.lean
#check @continuous_linear_equiv.cancel_right /- Left-hand side simplifies from
  f.comp e.to_continuous_linear_map = f'.comp e.to_continuous_linear_map
to
  f.comp ↑e = f'.comp ↑e
using
  [continuous_linear_equiv.coe_def_rev]
Try to change the left-hand side to the simplified term!
 -/
#check @continuous_linear_equiv.cancel_left /- Left-hand side simplifies from
  e.to_continuous_linear_map.comp f = e.to_continuous_linear_map.comp f'
to
  ↑e.comp f = ↑e.comp f'
using
  [continuous_linear_equiv.coe_def_rev]
Try to change the left-hand side to the simplified term!
 -/


/- The `doc_blame` linter reports: -/
/- DEFINITIONS ARE MISSING DOCUMENTATION STRINGS: -/
-- local\ample_relation.lean
#check @rel_loc.formal_sol.is_short_at /- def missing doc string -/

-- local\h_principle.lean
#check @step_landscape.π /- def missing doc string -/
#check @step_landscape.v /- def missing doc string -/
#check @step_landscape.K /- def missing doc string -/
#check @step_landscape.b /- def missing doc string -/
#check @step_landscape.g /- def missing doc string -/
#check @step_landscape.ρ /- def missing doc string -/

-- local\parametric_h_principle.lean
#check @one_jet_snd /- def missing doc string -/
#check @rel_loc.family_formal_sol.uncurry /- def missing doc string -/
#check @family_jet_sec.curry /- def missing doc string -/
#check @rel_loc.family_formal_sol.curry /- def missing doc string -/

-- loops\basic.lean
#check @loop.as_continuous_family /- def missing doc string -/

-- loops\exists.lean
#check @nice_loop /- constant missing doc string -/

-- loops\reparametrization.lean
#check @smooth_surrounding_family /- constant missing doc string -/
#check @smooth_surrounding_family.surrounding_parameters_at /- def missing doc string -/
#check @smooth_surrounding_family.surrounding_points_at /- def missing doc string -/
#check @smooth_surrounding_family.surrounding_weights_at /- def missing doc string -/
#check @smooth_surrounding_family.local_centering_density /- def missing doc string -/
#check @smooth_surrounding_family.local_centering_density_mp /- def missing doc string -/
#check @smooth_surrounding_family.local_centering_density_nhd /- def missing doc string -/
#check @smooth_surrounding_family.is_centering_density /- constant missing doc string -/
#check @smooth_surrounding_family.reparametrize /- def missing doc string -/

-- to_mathlib\analysis\cont_diff.lean
#check @strict_differentiable_at /- def missing doc string -/
#check @strict_differentiable /- def missing doc string -/
#check @equiv.to_homeomorph_of_cont_diff /- def missing doc string -/

-- to_mathlib\analysis\inner_product_space\orientation.lean
#check @orthonormal_basis.adjust_to_orientation /- def missing doc string -/
#check @orientation.volume_form /- def missing doc string -/

-- to_mathlib\analysis\inner_product_space\projection.lean
#check @orthogonal_projection_orthogonal_line_iso /- def missing doc string -/

-- to_mathlib\analysis\normed_space\operator_norm.lean
#check @linear_map.coprodₗ /- def missing doc string -/
#check @continuous_linear_map.coprodL /- def missing doc string -/

-- to_mathlib\equivariant.lean
#check @equivariant_equiv.to_equiv /- def missing doc string -/
#check @equivariant_equiv /- constant missing doc string -/
#check @equivariant_equiv.equivariant_map /- def missing doc string -/
#check @equivariant_equiv.symm /- def missing doc string -/

-- to_mathlib\linear_algebra\basis.lean
#check @basis.flag /- def missing doc string -/

-- to_mathlib\order\filter\eventually_constant.lean
#check @filter.eventually_constant /- def missing doc string -/
#check @filter.eventual_value /- def missing doc string -/

-- to_mathlib\partition2.lean
#check @smooth_partition_of_unity.prod /- def missing doc string -/

-- to_mathlib\smooth_barycentric.lean
#check @affine_bases /- def missing doc string -/
#check @eval_barycentric_coords /- def missing doc string -/

-- to_mathlib\topology\misc.lean
#check @proj_I /- def missing doc string -/

-- to_mathlib\topology\periodic.lean
#check @ℤ_sub_ℝ /- def missing doc string -/
#check @trans_one /- def missing doc string -/
#check @one_periodic /- def missing doc string -/
#check @proj_𝕊₁ /- def missing doc string -/
#check @𝕊₁.repr /- def missing doc string -/
#check @one_periodic.lift /- def missing doc string -/


/- The `unused_arguments` linter reports: -/
/- UNUSED ARGUMENTS. -/
-- local\ample_set.lean
#check @mem_span_of_zero_mem_segment /- argument 4: [_inst_3 : topological_space F] -/
#check @ample_of_two_le_codim /- argument 5: [_inst_7 : topological_add_group F] (duplicate), argument 6: [_inst_8 : has_continuous_smul ℝ F] (duplicate) -/

-- local\corrugation.lean
#check @corrugation.cont_diff' /- argument 13: [_inst_10 : finite_dimensional ℝ G], argument 20: [_inst_14 : finite_dimensional ℝ E] -/
#check @corrugation.remainder /- argument 10: [_inst_14 : finite_dimensional ℝ E] -/
#check @remainder.smooth /- argument 13: [_inst_10 : finite_dimensional ℝ G] -/

-- local\h_principle.lean
#check @step_landscape.Ω /- argument 9: [_inst_7 : borel_space F], argument 10: [_inst_8 : finite_dimensional ℝ F] -/
#check @step_landscape.b /- argument 9: [_inst_7 : borel_space F], argument 10: [_inst_8 : finite_dimensional ℝ F] -/
#check @step_landscape.g /- argument 9: [_inst_7 : borel_space F], argument 10: [_inst_8 : finite_dimensional ℝ F] -/
#check @step_landscape.accepts.smooth_b /- argument 14: (h : step_landscape.accepts R L 𝓕) -/
#check @step_landscape.accepts.smooth_g /- argument 14: (h : step_landscape.accepts R L 𝓕) -/
#check @step_landscape.bu_lt /- argument 9: [_inst_7 : borel_space F], argument 10: [_inst_8 : finite_dimensional ℝ F] -/

-- local\sphere_eversion.lean
#check @loc_immersion_rel_open_aux /- argument 6: [_inst_5 : finite_dimensional ℝ E'] -/
#check @mem_slice_iff_of_not_mem /- argument 5: [_inst_4 : finite_dimensional ℝ E], argument 6: [_inst_5 : finite_dimensional ℝ E'] -/
#check @slice_eq_of_not_mem /- argument 8: {w : E'} (duplicate) -/
#check @loc_formal_eversion_aux_φ /- argument 3: [_inst_4 : finite_dimensional ℝ E] -/

-- loops\basic.lean
#check @loop.sub_apply /- argument 3: [_inst_4 : normed_space ℝ F] -/
#check @loop.norm_at_le_supr_norm_Icc /- argument 3: [_inst_4 : normed_space ℝ F] -/
#check @loop.support /- argument 4: [_inst_8 : topological_space X'] -/
#check @loop.average /- argument 5: [_inst_12 : borel_space F], argument 6: [_inst_13 : topological_space.second_countable_topology F] -/
#check @loop.is_const_of_not_mem_support /- argument 4: [_inst_4 : normed_space ℝ F], argument 7: [_inst_12 : borel_space F], argument 8: [_inst_13 : topological_space.second_countable_topology F], argument 9: [_inst_14 : complete_space F] -/

-- loops\delta_mollifier.lean
#check @loop.mollify /- argument 6: [_inst_5 : borel_space F] -/

-- loops\exists.lean
#check @exists_loops_aux1 /- argument 12: [_inst_6 : borel_space F], argument 14: [_inst_8 : finite_dimensional ℝ E], argument 17: (hg : 𝒞 ⊤ g) -/

-- loops\reparametrization.lean
#check @loop.tendsto_mollify_apply_aux /- argument 5: [_inst_3 : finite_dimensional ℝ E] -/
#check @smooth_surrounding_family.local_centering_density_periodic /- argument 16: (hy : y ∈ γ.local_centering_density_nhd x) -/

-- loops\surrounding.lean
#check @local_loops_def /- argument 3: [_inst_2 : normed_space ℝ E] -/

-- to_mathlib\analysis\calculus.lean
#check @partial_deriv_fst /- argument 5: [_inst_11 : normed_space 𝕜 F] -/
#check @partial_deriv_snd /- argument 5: [_inst_3 : normed_space 𝕜 E] -/

-- to_mathlib\analysis\cont_diff.lean
#check @orthogonal_projection_singleton' /- argument 7: (hv : v ≠ 0) -/

-- to_mathlib\analysis\inner_product_space\gram_schmidt.lean
#check @gram_schmidt_def'' /- argument 6: [_inst_3 : nonempty ι], argument 7: [_inst_4 : fintype ι] -/
#check @gram_schmidt_of_orthogonal /- argument 6: [_inst_3 : nonempty ι], argument 7: [_inst_4 : fintype ι] -/
#check @gram_schmidt_normed_unit_length' /- argument 6: [_inst_3 : nonempty ι], argument 7: [_inst_4 : fintype ι] -/
#check @gram_schmidt_orthonormal_basis' /- argument 7: [_inst_4 : fintype ι] (duplicate) -/
#check @gram_schmidt_orthonormal_basis'_apply /- argument 7: [_inst_4 : fintype ι] (duplicate) -/
#check @gram_schmidt_orthonormal_basis'_apply_of_orthogonal /- argument 7: [_inst_4 : fintype ι] (duplicate) -/
#check @inner_gram_schmidt_orthonormal_basis'_eq_zero /- argument 7: [_inst_4 : fintype ι] (duplicate) -/
#check @gram_schmidt_orthonormal_basis'_inv_triangular /- argument 7: [_inst_4 : fintype ι] (duplicate) -/
#check @gram_schmidt_orthonormal_basis'_inv_triangular' /- argument 7: [_inst_4 : fintype ι] (duplicate) -/
#check @gram_schmidt_orthonormal_basis'_inv_block_triangular /- argument 7: [_inst_4 : fintype ι] (duplicate) -/
#check @gram_schmidt_orthonormal_basis'_det /- argument 7: [_inst_4 : fintype ι] (duplicate) -/

-- to_mathlib\analysis\inner_product_space\orientation.lean
#check @orthonormal_basis.orthonormal_adjust_to_orientation /- argument 3: [_inst_2 : finite_dimensional ℝ E] -/
#check @orthonormal_basis.det_to_matrix_orthonormal_basis_of_same_orientation /- argument 3: [_inst_2 : finite_dimensional ℝ E] -/
#check @orientation.volume_form /- argument 3: [_inst_2 : finite_dimensional ℝ E] -/

-- to_mathlib\analysis\inner_product_space\projection.lean
#check @linear_isometry_equiv.apply_ne_zero /- argument 7: [_inst_7 : complete_space F] -/
#check @orthogonal_projection_eq_zero_of_mem /- argument 3: [_inst_2 : complete_space E] -/
#check @mem_orthogonal_span_singleton_iff /- argument 3: [_inst_2 : complete_space E] -/
#check @orthogonal_projection_comp_coe /- argument 3: [_inst_2 : complete_space E] -/

-- to_mathlib\analysis\normed_space\operator_norm.lean
#check @continuous.prodL' /- argument 16: [_inst_23 : has_continuous_const_smul R Fₗ], argument 17: [_inst_24 : has_continuous_const_smul R Gₗ], argument 18: [_inst_25 : smul_comm_class 𝕜 R Fₗ], argument 19: [_inst_26 : smul_comm_class 𝕜 R Gₗ] -/

-- to_mathlib\geometry\manifold\misc_manifold.lean
#check @mdifferentiable_at.prod_mk /- argument 30: [_inst_21 : smooth_manifold_with_corners I M], argument 31: [_inst_22 : smooth_manifold_with_corners I' M'], argument 32: [_inst_23 : smooth_manifold_with_corners J N] -/
#check @in_coordinates /- argument 22: [_inst_15 : topological_space N] -/

-- to_mathlib\linear_algebra\determinant.lean
#check @basis.coord_units_smul /- argument 8: [_inst_5 : fintype ι] -/

-- to_mathlib\measure_theory\basic.lean
#check @is_compact.integrable_const /- argument 6: [_inst_8 : measurable_space E] -/

-- to_mathlib\partition2.lean
#check @smooth_partition_of_unity.prod /- argument 18: [_inst_13 : sigma_compact_space M₁], argument 19: [_inst_14 : t2_space M₁] -/

-- to_mathlib\smooth_barycentric.lean
#check @affine_bases_findim /- argument 8: [_inst_6 : decidable_eq ι] -/
#check @eval_barycentric_coords /- argument 9: [_inst_5 : fintype ι], argument 10: [_inst_6 : decidable_eq ι] -/

-- to_mathlib\topology\misc.lean
#check @decode₂_locally_finite /- argument 2: [_inst_1 : topological_space α] (duplicate) -/

-- to_mathlib\topology\path.lean
#check @continuous.path_strans /- argument 4: [_inst_6 : separated_space X] -/

-- to_mathlib\topology\periodic.lean
#check @continuous.bounded_on_compact_of_one_periodic /- argument 5: [_inst_3 : t2_space X] -/


/- The `ge_or_gt` linter reports: -/
/- The following declarations use ≥/>, probably in a way where we would prefer
  to use ≤/< instead. See note [nolint_ge] for more information. -/
-- to_mathlib\analysis\cont_diff.lean
#check @cont_diff_parametric_symm_of_deriv_pos /- the type contains ≥/>. Use ≤/< instead. -/



-/
