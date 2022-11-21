import main
import local.sphere_eversion


attribute [main_declaration] Smale Gromov rel_mfld.ample.satisfies_h_principle_with'

attribute [main_declaration]
  immersion_rel_open_ample
  immersion_inclusion_sphere -- do we want to keep this?
  immersion_antipodal_sphere -- do we want to keep this?
  sphere_eversion_of_loc
  satisfied_or_refund -- this is unused, because it just packages up some stuff.
  -- It is referred to in the blueprint

/-- Files in the sphere eversion project, minus some files that only contain meta code. -/
meta def filenames : list string :=
[
"src/global/indexing.lean",
"src/global/localisation_data.lean",
"src/global/immersion.lean",
"src/global/one_jet_bundle.lean",
"src/global/smooth_embedding.lean",
"src/global/gromov.lean",
"src/global/relation.lean",
"src/global/one_jet_sec.lean",
"src/global/localized_construction.lean",
"src/global/parametricity_for_free.lean",
"src/global/localisation.lean",
"src/global/twist_one_jet_sec.lean",
"src/loops/reparametrization.lean",
"src/loops/surrounding.lean",
"src/loops/delta_mollifier.lean",
"src/loops/exists.lean",
"src/loops/basic.lean",
"src/local/ample_set.lean",
"src/local/ample_relation.lean",
"src/local/dual_pair.lean",
"src/local/one_jet.lean",
"src/local/relation.lean",
"src/local/sphere_eversion.lean",
"src/local/h_principle.lean",
"src/local/parametric_h_principle.lean",
"src/local/corrugation.lean",
"src/main.lean",
"src/notations.lean",
"src/to_mathlib/order/filter/eventually_constant.lean",
"src/to_mathlib/data/nat/basic.lean",
"src/to_mathlib/data/set/prod.lean",
"src/to_mathlib/data/set/finite.lean",
"src/to_mathlib/data/set/basic.lean",
"src/to_mathlib/data/real_basic.lean",
"src/to_mathlib/topology/algebra/module.lean",
"src/to_mathlib/topology/algebra/order/compact.lean",
"src/to_mathlib/topology/algebra/order/basic.lean",
"src/to_mathlib/topology/local_homeomorph.lean",
"src/to_mathlib/topology/nhds_set.lean",
"src/to_mathlib/topology/paracompact.lean",
"src/to_mathlib/topology/periodic.lean",
"src/to_mathlib/topology/separation.lean",
"src/to_mathlib/topology/hausdorff_distance.lean",
"src/to_mathlib/topology/misc.lean",
"src/to_mathlib/topology/path.lean",
"src/to_mathlib/logic/equiv/local_equiv.lean",
"src/to_mathlib/partition2.lean",
"src/to_mathlib/set_theory/cardinal/basic.lean",
"src/to_mathlib/smooth_barycentric.lean",
"src/to_mathlib/equivariant.lean",
"src/to_mathlib/geometry/manifold/charted_space.lean",
"src/to_mathlib/geometry/manifold/smooth_manifold_with_corners.lean",
"src/to_mathlib/geometry/manifold/vector_bundle/basic_core_constructions.lean",
"src/to_mathlib/geometry/manifold/misc.lean",
"src/to_mathlib/geometry/manifold/misc_manifold.lean",
"src/to_mathlib/partition.lean",
"src/to_mathlib/unused/linear_algebra/multilinear.lean",
"src/to_mathlib/analysis/inner_product_space/dual.lean",
"src/to_mathlib/analysis/inner_product_space/cross_product.lean",
"src/to_mathlib/analysis/inner_product_space/projection.lean",
"src/to_mathlib/analysis/inner_product_space/rotation.lean",
"src/to_mathlib/analysis/cut_off.lean",
"src/to_mathlib/analysis/calculus.lean",
"src/to_mathlib/analysis/cont_diff.lean",
"src/to_mathlib/analysis/normed_space/operator_norm.lean",
"src/to_mathlib/analysis/normed_space/misc.lean",
"src/to_mathlib/analysis/calculus/affine_map.lean",
"src/to_mathlib/analysis/normed_group.lean",
"src/to_mathlib/measure_theory/interval_integral.lean",
"src/to_mathlib/measure_theory/borel_space.lean",
"src/to_mathlib/measure_theory/parametric_interval_integral.lean",
"src/to_mathlib/linear_algebra/basis.lean",
"src/to_mathlib/linear_algebra/basic.lean",
"src/to_mathlib/linear_algebra/finite_dimensional.lean"
]

open tactic
setup_tactic_parser

meta def lint_unused : tactic unit := do
  let fs := filenames.map some,
  ds ← all_unused (filenames.map some), -- we're not interested in this file
  str ← get_project_dir `lint_sphere_cmd 9,
  env ← get_env,
  let d := grouped_by_filename env (ds.map $ λ _, "unused") str.length (print_warnings env ff name.anonymous),
  trace d

-- #eval lint_unused

/-
-- loops/basic.lean
#check @loop.const_zero /- unused -/
#check @loop.inhabited /- unused -/
#check @loop.add_nat_eq /- unused -/
#check @loop.comp_fract_eq /- unused -/
#check @loop.has_neg_neg_apply /- unused -/
#check @loop.sub_apply /- unused -/
#check @loop.norm_at_le_supr_norm_Icc /- unused -/
#check @loop.is_closed_support /- unused -/
#check @loop.continuous_of_family /- unused -/
#check @loop.continuous_of_family_step /- unused -/
#check @loop.as_continuous_family /- unused -/
#check @loop.as_continuous_family_apply_apply /- unused -/
#check @loop.of_path_continuous /- unused -/
#check @loop.round_trip_continuous /- unused -/
#check @loop.zero_average /- unused -/
#check @loop.eq_const_of_not_mem_support /- unused -/
#check @loop.compact_support_diff /- unused -/

-- to_mathlib/analysis/calculus.lean
#check @real.smooth_transition.continuous_at /- unused -/
#check @cont_diff_on.clm_apply /- unused -/
#check @cont_diff_within_at.fderiv_within_apply /- unused -/
#check @cont_diff_within_at.fderiv_within_right /- unused -/
#check @cont_diff.fderiv_apply /- unused -/
#check @cont_diff_at.fderiv /- unused -/
#check @cont_diff_at.comp₂ /- unused -/
#check @cont_diff_at.clm_comp /- unused -/
#check @fderiv_prod_left /- unused -/
#check @cont_diff.partial_fst /- unused -/
#check @cont_diff.partial_snd /- unused -/
#check @continuous_linear_map.comp_leftL /- unused -/
#check @differentiable.fderiv_partial_fst /- unused -/
#check @differentiable.fderiv_partial_snd /- unused -/
#check @partial_deriv_fst /- unused -/
#check @partial_fderiv_fst_eq_smul_right /- unused -/
#check @partial_fderiv_fst_one /- unused -/
#check @with_top.le_mul_self /- unused -/
#check @with_top.le_add_self /- unused -/
#check @with_top.le_self_add /- unused -/
#check @with_top.le_self_mul /- unused -/
#check @cont_diff.cont_diff_partial_fst_apply /- unused -/
#check @cont_diff.cont_diff_partial_snd_apply /- unused -/
#check @cont_diff.continuous_partial_snd /- unused -/

-- to_mathlib/analysis/calculus/affine_map.lean
#check @range_affine_equiv_ball /- unused -/

-- to_mathlib/analysis/cont_diff.lean
#check @continuous_linear_map.blocks /- unused -/
#check @strict_differentiable_at /- unused -/
#check @strict_differentiable /- unused -/
#check @strict_differentiable_at.differentiable_at /- unused -/
#check @homeomorph.cont_diff_at_symm /- unused -/
#check @cont_diff_within_at.mul_const /- unused -/
#check @cont_diff_on.mul_const /- unused -/
#check @cont_diff.mul_const /- unused -/

-- to_mathlib/analysis/inner_product_space/cross_product.lean
#check @orientation.cross_product'_apply /- unused -/

-- to_mathlib/analysis/inner_product_space/projection.lean
#check @coe_orthogonal_projection_orthogonal_singleton /- unused -/
#check @normed_space.continuous_iff /- unused -/
#check @normed_space.continuous_iff' /- unused -/

-- to_mathlib/analysis/inner_product_space/rotation.lean
#check @orientation.inj_on_rot /- unused -/

-- to_mathlib/analysis/normed_space/operator_norm.lean
#check @continuous_linear_map.le_op_norm_of_le' /- unused -/
#check @linear_map.coprodₗ /- unused -/
#check @eventually_norm_sub_lt /- unused -/

-- to_mathlib/data/nat/basic.lean
#check @exists_by_induction /- unused -/

-- to_mathlib/data/real_basic.lean
#check @real.bcsupr_le /- unused -/
#check @real.bcsupr_nonneg /- unused -/

-- to_mathlib/equivariant.lean
#check @equivariant_equiv.real.function.has_uncurry /- unused -/
#check @equivariant_equiv.coe_mk /- unused -/
#check @equivariant_equiv.ext /- unused -/
#check @equivariant_equiv.symm_symm /- unused -/
#check @equivariant_equiv.symm_apply_apply /- unused -/

-- to_mathlib/geometry/manifold/misc_manifold.lean
#check @cont_mdiff_at.clm_apply /- unused -/
#check @cont_mdiff.clm_apply /- unused -/
#check @mfderiv_prod_left /- unused -/
#check @cont_mdiff_map.continuous_map_class /- unused -/
#check @cont_mdiff_map.prod_mk /- unused -/
#check @diffeomorph.continuous_map_class /- unused -/

-- to_mathlib/geometry/manifold/vector_bundle/basic_core_constructions.lean
#check @basic_smooth_vector_bundle_core.trivial_coord_change_at /- unused -/
#check @basic_smooth_vector_bundle_core.pullback_coord_change /- unused -/
#check @basic_smooth_vector_bundle_core.pullback_chart /- unused -/
#check @basic_smooth_vector_bundle_core.pullback_fst_chart /- unused -/
#check @basic_smooth_vector_bundle_core.pullback_fst_chart_at /- unused -/
#check @basic_smooth_vector_bundle_core.pullback_snd_chart /- unused -/
#check @basic_smooth_vector_bundle_core.pullback_snd_chart_at /- unused -/

-- to_mathlib/linear_algebra/basic.lean
#check @submodule.map_inf_le /- unused -/
#check @submodule.map_inf /- unused -/
#check @linear_map.injective_iff_of_direct_sum /- unused -/

-- to_mathlib/linear_algebra/basis.lean
#check @basis.flag_mono /- unused -/
#check @fin.coe_succ_le_iff_le /- unused -/
#check @fin.coe_lt_succ /- unused -/

-- to_mathlib/measure_theory/parametric_interval_integral.lean
#check @has_fderiv_at_of_dominated_of_fderiv_le'' /- unused -/
#check @continuous_parametric_integral_of_continuous /- unused -/

-- to_mathlib/order/filter/eventually_constant.lean
#check @continuous_within_at.congr_nhds /- unused -/
#check @filter.eventually_constant_iff_tendsto /- unused -/
#check @filter.eventually_constant_const /- unused -/
#check @filter.eventual_value_unique' /- unused -/
#check @filter.eventual_value_eq_fn /- unused -/
#check @filter.eventually_constant.tendsto /- unused -/
#check @filter.eventually_constant.tendsto_nhds /- unused -/
#check @filter.eventual_value_eq_lim /- unused -/
#check @eventually_constant_on_at_top /- unused -/
#check @locally_eventually_constant_on.nonempty /- unused -/
#check @locally_eventually_constant_on.continuous_within_at /- unused -/
#check @locally_eventually_constant_on.nhd /- unused -/
#check @locally_eventually_constant_on.nhd_mem_nhds /- unused -/
#check @locally_eventually_constant_on.eventually_constant_nhd /- unused -/

-- to_mathlib/partition.lean
#check @tsupport_smul_right /- unused -/
#check @locally_finite.smul_right /- unused -/
#check @locally_finite_support_iff /- unused -/
#check @locally_finite_mul_support_iff /- unused -/
#check @locally_finite.exists_finset_mul_support_eq /- unused -/
#check @locally_finite.exists_finset_support_eq /- unused -/
#check @partition_of_unity.exists_finset_nhd' /- unused -/
#check @partition_of_unity.exists_finset_nhd /- unused -/
#check @tactic.mem_univ /- unused -/
#check @smooth_partition_of_unity.cont_diff_at_sum' /- unused -/
#check @has_fderiv_at_of_not_mem /- unused -/
#check @cont_diff_at_of_not_mem /- unused -/

-- to_mathlib/topology/algebra/module.lean
#check @continuous_linear_map.comp_fst_add_comp_snd /- unused -/

-- to_mathlib/topology/algebra/order/basic.lean
#check @has_basis_nhds_set_Ici /- unused -/

-- to_mathlib/topology/hausdorff_distance.lean
#check @metric.thickening_ball /- unused -/
#check @metric.inf_dist_pos_iff_not_mem_closure /- unused -/

-- to_mathlib/topology/misc.lean
#check @continuous.eventually /- unused -/
#check @nhds_set_prod_le /- unused -/
#check @support_norm /- unused -/
#check @has_compact_support_of_subset /- unused -/
#check @has_compact_mul_support_of_subset /- unused -/
#check @periodic_const /- unused -/
#check @proj_Icc_eq_proj_I /- unused -/
#check @proj_I_of_le_zero /- unused -/
#check @proj_I_of_one_le /- unused -/
#check @range_proj_I /- unused -/
#check @monotone_proj_I /- unused -/
#check @strict_mono_on_proj_I /- unused -/
#check @proj_I_le_max /- unused -/
#check @min_le_proj_I /- unused -/
#check @proj_I_mapsto /- unused -/
#check @convex.is_preconnected' /- unused -/
#check @is_preconnected_ball /- unused -/
#check @is_connected_ball /- unused -/
#check @topological_space.cover_nat_nhds_within /- unused -/
#check @topological_space.cover_nat_nhds_within' /- unused -/
#check @set.subtype.image_coe_eq_iff_eq_univ /- unused -/
#check @set.subtype.preimage_coe_eq_univ /- unused -/
#check @precise_refinement_set' /- unused -/
#check @point_finite_of_locally_finite_coe_preimage /- unused -/
#check @exists_subset_Union_interior_of_is_open /- unused -/

-- to_mathlib/topology/nhds_set.lean
#check @nhds_set_inter_le /- unused -/
#check @sup_Sup /- unused -/
#check @Sup_sup /- unused -/

-- to_mathlib/topology/path.lean
#check @path.strans_self /- unused -/

-- to_mathlib/topology/periodic.lean
#check @𝕊₁.inhabited /- unused -/
#check @is_closed_int /- unused -/
#check @𝕊₁.t2_space /- unused -/
#check @continuous.bounded_of_one_periodic_of_compact /- unused -/

-- to_mathlib/topology/separation.lean
#check @t2_space_iff_of_continuous_surjective_open /- unused -/

-/
