import geometry.manifold.diffeomorph
import geometry.manifold.algebra.monoid
import geometry.manifold.metrizable
import to_mathlib.analysis.calculus

open bundle set function filter
open_locale manifold topology

section charted_space

variables {M H : Type*} [topological_space M] [topological_space H] [charted_space H M]
  (G : structure_groupoid H)

end charted_space

namespace model_with_corners

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
  {H : Type*} [topological_space H]
  {M : Type*} [topological_space M] (f : local_homeomorph M H) (I : model_with_corners 𝕜 E H)

end model_with_corners

section smooth_manifold_with_corners
open smooth_manifold_with_corners

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
  {E' : Type*} [normed_add_comm_group E'] [normed_space 𝕜 E']
  {F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]
  {H : Type*} [topological_space H] {I : model_with_corners 𝕜 E H}
  {H' : Type*} [topological_space H'] {I' : model_with_corners 𝕜 E' H'}
  {G : Type*} [topological_space G] {J : model_with_corners 𝕜 F G}
  {M : Type*} [topological_space M] [charted_space H M]
  {M' : Type*} [topological_space M'] [charted_space H' M']
  {N : Type*} [topological_space N] [charted_space G N]
  {F' : Type*} [normed_add_comm_group F'] [normed_space 𝕜 F']
  {F'' : Type*} [normed_add_comm_group F''] [normed_space 𝕜 F'']
variables {f : M → M'} {m n : ℕ∞} {s : set M} {x : M}


namespace basic_smooth_vector_bundle_core
variables [smooth_manifold_with_corners I M] (Z : basic_smooth_vector_bundle_core I M E')

end basic_smooth_vector_bundle_core

variables [smooth_manifold_with_corners I M] [smooth_manifold_with_corners I' M']
  [smooth_manifold_with_corners J N]

-- this can be useful to see where we (ab)use definitional equalities
-- local attribute [irreducible] tangent_space

/-! The two instances below deserve some further thought. For example one might not want the tangent
space at every point to carry a canonical norm.

Note that `dual_pair.update` requires `F` to be a `normed_add_comm_group` (though perhaps we could
get away with `has_continuous_smul` with sufficient extra work).

In `rel_mfld.slice` we use `dual_pair.update` applied to `tangent_space`. If we don't add these
instances, then in fact Lean still accepts the definition. What is going on is that Lean
is unfolding the definition of `tangent_space`, realizing that `tangent_space I x = E` and
`tangent_space I' y = E'` and using the `normed_add_comm_group` instances of these types.
Note that this still uses these instances but at the cost that up to reducible transparency, the
term is not type-correct (in other words: you have to unfold `tangent_space` to realize that the
term is type-correct).

This means that many tactics, like `simp`, `rw`, and `dsimp` fail to rewrite within this term,
because the result is not type correct up to reducible transparancy.

Declaring these instances avoids such problems. -/

instance {x : M} : normed_add_comm_group (tangent_space I x) := by delta_instance tangent_space
instance {x : M} : normed_space 𝕜 (tangent_space I x) := by delta_instance tangent_space

lemma tangent_bundle_core_coord_change_achart (x x' : M) (z : H) :
  (tangent_bundle_core I M).coord_change (achart H x) (achart H x') z =
  fderiv_within 𝕜 (ext_chart_at I x' ∘ (ext_chart_at I x).symm) (range I) (I z) :=
rfl

variables (I)
-- used in tangent_bundle_model_space_chart_at

lemma model_with_corners.fderiv_within_comp_symm (x : H) :
  fderiv_within 𝕜 (I ∘ I.symm) (range I) (I x) = continuous_linear_map.id 𝕜 E :=
begin
  have : fderiv_within 𝕜 (I ∘ I.symm) (range I) (I x) = fderiv_within 𝕜 id (range I) (I x),
  { refine fderiv_within_congr I.unique_diff_at_image (λ y hy, _) (by simp only with mfld_simps),
    exact model_with_corners.right_inv _ hy },
  rwa fderiv_within_id I.unique_diff_at_image at this
end


lemma tangent_bundle_core_coord_change_model_space (x x' : H) (z : H) :
  (tangent_bundle_core I H).coord_change (achart H x) (achart H x') z =
  continuous_linear_map.id 𝕜 E :=
begin
  simp only [tangent_bundle_core_coord_change_achart, ext_chart_at, I.fderiv_within_comp_symm] with mfld_simps,
end


lemma cont_diff_on_coord_change' {e e' : local_homeomorph M H}
  (h : e ∈ atlas H M) (h' : e' ∈ atlas H M) :
  cont_diff_on 𝕜 ⊤ (I ∘ (e.symm ≫ₕ e') ∘ I.symm) (I.symm ⁻¹' (e.symm ≫ₕ e').source ∩ range I) :=
(has_groupoid.compatible (cont_diff_groupoid ⊤ I) h h').1

variables {I}
/-- A congruence lemma for `mfderiv`, (ab)using the fact that `tangent_space I' (f x)` is
definitionally equal to `E'`. -/
lemma mfderiv_congr_point {x' : M} (h : x = x') :
  @eq (E →L[𝕜] E') (mfderiv I I' f x) (mfderiv I I' f x') :=
by subst h

/-- A congruence lemma for `mfderiv`, (ab)using the fact that `tangent_space I' (f x)` is
definitionally equal to `E'`. -/
lemma mfderiv_congr {f' : M → M'} (h : f = f') :
  @eq (E →L[𝕜] E') (mfderiv I I' f x) (mfderiv I I' f' x) :=
by subst h

/-- The derivative of the projection `M × M' → M` is the projection `TM × TM' → TM` -/
lemma mfderiv_fst (x : M × M') :
  mfderiv (I.prod I') I prod.fst x = continuous_linear_map.fst 𝕜 E E' :=
begin
  simp_rw [mfderiv, if_pos smooth_at_fst.mdifferentiable_at, written_in_ext_chart_at,
    ext_chart_at_prod, function.comp, local_equiv.prod_coe, local_equiv.prod_coe_symm],
  have : unique_diff_within_at 𝕜 (range (I.prod I')) (ext_chart_at (I.prod I') x x) :=
  (I.prod I').unique_diff _ (mem_range_self _),
  refine (filter.eventually_eq.fderiv_within_eq this _ _).trans _,
  swap 3,
  { exact (ext_chart_at I x.1).right_inv ((ext_chart_at I x.1).maps_to $
      mem_ext_chart_source I x.1) },
  { refine eventually_of_mem (ext_chart_at_target_mem_nhds_within (I.prod I') x)
      (λ y hy, local_equiv.right_inv _ _),
    rw [ext_chart_at_prod] at hy,
    exact hy.1 },
  exact fderiv_within_fst this,
end

/-- The derivative of the projection `M × M' → M'` is the projection `TM × TM' → TM'` -/
lemma mfderiv_snd (x : M × M') :
  mfderiv (I.prod I') I' prod.snd x = continuous_linear_map.snd 𝕜 E E' :=
begin
  simp_rw [mfderiv, if_pos smooth_at_snd.mdifferentiable_at, written_in_ext_chart_at,
    ext_chart_at_prod, function.comp, local_equiv.prod_coe, local_equiv.prod_coe_symm],
  have : unique_diff_within_at 𝕜 (range (I.prod I')) (ext_chart_at (I.prod I') x x) :=
  (I.prod I').unique_diff _ (mem_range_self _),
  refine (filter.eventually_eq.fderiv_within_eq this _ _).trans _,
  swap 3,
  { exact (ext_chart_at I' x.2).right_inv ((ext_chart_at I' x.2).maps_to $
      mem_ext_chart_source I' x.2) },
  { refine eventually_of_mem (ext_chart_at_target_mem_nhds_within (I.prod I') x)
      (λ y hy, local_equiv.right_inv _ _),
    rw [ext_chart_at_prod] at hy,
    exact hy.2 },
  exact fderiv_within_snd this,
end

lemma mdifferentiable_at.prod_mk {f : N → M} {g : N → M'} {x : N}
  (hf : mdifferentiable_at J I f x)
  (hg : mdifferentiable_at J I' g x) :
  mdifferentiable_at J (I.prod I') (λ x, (f x, g x)) x :=
⟨hf.1.prod hg.1, hf.2.prod hg.2⟩


-- todo: rename differentiable_at.fderiv_within_prod -> differentiable_within_at.fderiv_within_prod
lemma mdifferentiable_at.mfderiv_prod {f : N → M} {g : N → M'} {x : N}
  (hf : mdifferentiable_at J I f x)
  (hg : mdifferentiable_at J I' g x) :
  mfderiv J (I.prod I') (λ x, (f x, g x)) x = (mfderiv J I f x).prod (mfderiv J I' g x) :=
begin
  classical,
  simp_rw [mfderiv, if_pos (hf.prod_mk hg), if_pos hf, if_pos hg],
  exact differentiable_at.fderiv_within_prod hf.2 hg.2 (J.unique_diff _ (mem_range_self _))
end

lemma mfderiv_prod_left {x₀ : M} {y₀ : M'} :
  mfderiv I (I.prod I') (λ x, (x, y₀)) x₀ = continuous_linear_map.inl 𝕜 E E' :=
begin
  refine ((mdifferentiable_at_id I).mfderiv_prod (mdifferentiable_at_const I I')).trans _,
  rw [mfderiv_id, mfderiv_const],
  refl
end

lemma mfderiv_prod_right {x₀ : M} {y₀ : M'} :
  mfderiv I' (I.prod I') (λ y, (x₀, y)) y₀ = continuous_linear_map.inr 𝕜 E E' :=
begin
  refine ((mdifferentiable_at_const I' I).mfderiv_prod (mdifferentiable_at_id I')).trans _,
  rw [mfderiv_id, mfderiv_const],
  refl
end

lemma mfderiv_prod_eq_add {f : N × M → M'} {p : N × M}
  (hf : mdifferentiable_at (J.prod I) I' f p) :
  mfderiv (J.prod I) I' f p =
  (show F × E →L[𝕜] E', from mfderiv (J.prod I) I' (λ (z : N × M), f (z.1, p.2)) p +
  mfderiv (J.prod I) I' (λ (z : N × M), f (p.1, z.2)) p) :=
begin
  dsimp only,
  rw [← @prod.mk.eta _ _ p] at hf,
  rw [mfderiv_comp p (by apply hf) (smooth_fst.prod_mk smooth_const).mdifferentiable_at,
    mfderiv_comp p (by apply hf) (smooth_const.prod_mk smooth_snd).mdifferentiable_at,
    ← continuous_linear_map.comp_add,
    smooth_fst.mdifferentiable_at.mfderiv_prod smooth_const.mdifferentiable_at,
    smooth_const.mdifferentiable_at.mfderiv_prod smooth_snd.mdifferentiable_at,
    mfderiv_fst, mfderiv_snd, mfderiv_const, mfderiv_const],
  symmetry,
  convert continuous_linear_map.comp_id _,
  { exact continuous_linear_map.fst_prod_zero_add_zero_prod_snd },
  simp_rw [prod.mk.eta],
end

/-- When `ϕ` is a continuous linear map that changes vectors in charts around `x` to vectors
  in charts around `y`, `in_coordinates' Z Z' x₀ x y₀ y ϕ` is a coordinate change of this continuous
  linear map that makes sense from charts around `x₀` to charts around `y₀`
  by composing it with appropriate coordinate changes given by smooth vector bundles `Z` and `Z'`.
  -/
def in_coordinates' (Z : basic_smooth_vector_bundle_core I M F)
  (Z' : basic_smooth_vector_bundle_core I' M' F')
  (x₀ x : M) (y₀ y : M') (ϕ : F →L[𝕜] F') : F →L[𝕜] F' :=
Z'.coord_change (achart H' y) (achart H' y₀) (chart_at H' y y) ∘L ϕ ∘L
  Z.coord_change (achart H x₀) (achart H x) (chart_at H x₀ x)

variables (I I')
/-- When `ϕ x` is a continuous linear map that changes vectors in charts around `f x` to vectors
  in charts around `g x`, `in_coordinates I I' f g ϕ x₀ x` is a coordinate change of this continuous
  linear map that makes sense from charts around `f x₀` to charts around `g x₀`
  by composing it with appropriate coordinate changes. -/
noncomputable def in_coordinates (f : N → M) (g : N → M') (ϕ : N → E →L[𝕜] E') :
  N → N → E →L[𝕜] E' :=
λ x₀ x, in_coordinates' (tangent_bundle_core I M) (tangent_bundle_core I' M')
  (f x₀) (f x) (g x₀) (g x) (ϕ x)


lemma in_coordinates'_tangent_bundle_core_model_space
  (x₀ x : H) (y₀ y : H') (ϕ : E →L[𝕜] E') : in_coordinates' (tangent_bundle_core I H)
    (tangent_bundle_core I' H') x₀ x y₀ y ϕ = ϕ :=
by simp_rw [in_coordinates', tangent_bundle_core_coord_change_model_space,
    continuous_linear_map.id_comp, continuous_linear_map.comp_id]

variables {I I'}

/-- The appropriate (more general) formulation of `cont_mdiff_at.mfderiv''`. -/
lemma cont_mdiff_at.mfderiv''' {x : N} (f : N → M → M') (g : N → M)
  (hf : cont_mdiff_at (J.prod I) I' n (function.uncurry f) (x, g x))
  (hg : cont_mdiff_at J I m g x) (hmn : m + 1 ≤ n) :
  cont_mdiff_at J 𝓘(𝕜, E →L[𝕜] E') m
    (in_coordinates I I' g (λ x, f x (g x)) (λ x', mfderiv I I' (f x') (g x')) x) x :=
begin
  have h4f : continuous_at (λ x, f x (g x)) x,
  { apply continuous_at.comp (by apply hf.continuous_at) (continuous_at_id.prod hg.continuous_at) },
  have h3f := cont_mdiff_at_iff_cont_mdiff_at_nhds.mp (hf.of_le $ (self_le_add_left 1 m).trans hmn),
  have h2f : ∀ᶠ x₂ in 𝓝 x, cont_mdiff_at I I' 1 (f x₂) (g x₂),
  { refine ((continuous_at_id.prod hg.continuous_at).tendsto.eventually h3f).mono (λ x hx, _),
    exact hx.comp (g x) (cont_mdiff_at_const.prod_mk cont_mdiff_at_id) },
  have h2g := hg.continuous_at.preimage_mem_nhds (ext_chart_at_source_mem_nhds I (g x)),
  have : cont_diff_within_at 𝕜 m (λ x', fderiv_within 𝕜
    (ext_chart_at I' (f x (g x)) ∘ f ((ext_chart_at J x).symm x') ∘ (ext_chart_at I (g x)).symm)
    (range I) (ext_chart_at I (g x) (g ((ext_chart_at J x).symm x'))))
    (range J) (ext_chart_at J x x),
  { rw [cont_mdiff_at_iff] at hf hg,
    simp_rw [function.comp, uncurry, ext_chart_at_prod, local_equiv.prod_coe_symm] at hf ⊢,
    refine (cont_diff_within_at_fderiv_within _
      (hg.2.mono_of_mem _) I.unique_diff hmn _ _ _ _).mono_of_mem _,
    swap 3,
    { simp_rw [function.comp, ext_chart_at_to_inv], exact hf.2 },
    { refine (ext_chart_at J x).target ∩
      (λ x', (ext_chart_at J x).symm x') ⁻¹' (g ⁻¹' (ext_chart_at I (g x)).source) },
    { exact mem_of_superset self_mem_nhds_within
        ((inter_subset_left _ _).trans $ ext_chart_at_target_subset_range J x) },
    { simp_rw [mem_inter_iff, mem_preimage, ext_chart_at_to_inv],
      exact ⟨local_equiv.maps_to _ (mem_ext_chart_source J x), mem_ext_chart_source I (g x)⟩ },
    { simp_rw [model_with_corners.range_prod],
      exact set.prod_mono ((inter_subset_left _ _).trans $ ext_chart_at_target_subset_range J x)
        subset_rfl },
    { refine eventually_of_forall (λ x', mem_range_self _) },
    swap 2,
    { refine inter_mem (ext_chart_at_target_mem_nhds_within J x) _,
      refine nhds_within_le_nhds (ext_chart_at_preimage_mem_nhds' _ _ (mem_ext_chart_source J x) _),
      exact hg.1.preimage_mem_nhds (ext_chart_at_source_mem_nhds I (g x)) },
    simp_rw [function.comp, model_with_corners.range_prod, ext_chart_at_to_inv],
    refine mem_of_superset self_mem_nhds_within _,
    refine (image_subset_range _ _).trans _,
    exact range_comp_subset_range (λ a, chart_at H (g x) $ g $ (chart_at G x).symm $ J.symm a) I },
  have : cont_mdiff_at J 𝓘(𝕜, E →L[𝕜] E') m
    (λ x', fderiv_within 𝕜 (ext_chart_at I' (f x (g x)) ∘ f x' ∘ (ext_chart_at I (g x)).symm)
    (range I) (ext_chart_at I (g x) (g x'))) x,
  { simp_rw [cont_mdiff_at_iff_source_of_mem_source (mem_chart_source G x),
      cont_mdiff_within_at_iff_cont_diff_within_at, function.comp],
    exact this },
  have : cont_mdiff_at J 𝓘(𝕜, E →L[𝕜] E') m
    (λ x', fderiv_within 𝕜 (ext_chart_at I' (f x (g x)) ∘ (ext_chart_at I' (f x' (g x'))).symm ∘
      written_in_ext_chart_at I I' (g x') (f x') ∘ ext_chart_at I (g x') ∘
      (ext_chart_at I (g x)).symm) (range I) (ext_chart_at I (g x) (g x'))) x,
  { refine this.congr_of_eventually_eq _,
    filter_upwards [h2g, h2f],
    intros x₂ hx₂ h2x₂,
    have : ∀ x' ∈ (ext_chart_at I (g x)).symm ⁻¹' (ext_chart_at I (g x₂)).source ∩
        (ext_chart_at I (g x)).symm ⁻¹' (f x₂ ⁻¹' (ext_chart_at I' (f x₂ (g x₂))).source),
      (ext_chart_at I' (f x (g x)) ∘ (ext_chart_at I' (f x₂ (g x₂))).symm ∘
      written_in_ext_chart_at I I' (g x₂) (f x₂) ∘ ext_chart_at I (g x₂) ∘
      (ext_chart_at I (g x)).symm) x' =
      ext_chart_at I' (f x (g x)) (f x₂ ((ext_chart_at I (g x)).symm x')),
    { rintro x' ⟨hx', h2x'⟩,
      simp_rw [written_in_ext_chart_at, function.comp_apply],
      rw [(ext_chart_at I (g x₂)).left_inv hx', (ext_chart_at I' (f x₂ (g x₂))).left_inv h2x'] },
    refine filter.eventually_eq.fderiv_within_eq_nhds (I.unique_diff _ $ mem_range_self _) _,
    refine eventually_of_mem (inter_mem _ _) this,
    { exact ext_chart_at_preimage_mem_nhds' _ _ hx₂ (ext_chart_at_source_mem_nhds I (g x₂)) },
    refine ext_chart_at_preimage_mem_nhds' _ _ hx₂ _,
    exact (h2x₂.continuous_at).preimage_mem_nhds (ext_chart_at_source_mem_nhds _ _) },
  /- The conclusion is the same as the following, when unfolding coord_change of
    `tangent_bundle_core` -/
  change cont_mdiff_at J 𝓘(𝕜, E →L[𝕜] E') m
    (λ x', (fderiv_within 𝕜 (ext_chart_at I' (f x (g x)) ∘ (ext_chart_at I' (f x' (g x'))).symm)
        (range I') (ext_chart_at I' (f x' (g x')) (f x' (g x')))).comp
        ((mfderiv I I' (f x') (g x')).comp (fderiv_within 𝕜 (ext_chart_at I (g x') ∘
        (ext_chart_at I (g x)).symm) (range I) (ext_chart_at I (g x) (g x'))))) x,
  refine this.congr_of_eventually_eq _,
  filter_upwards [h2g, h2f,
    h4f.preimage_mem_nhds (ext_chart_at_source_mem_nhds I' (f x (g x)))],
  intros x₂ hx₂ h2x₂ h3x₂,
  symmetry,
  rw [(h2x₂.mdifferentiable_at le_rfl).mfderiv],
  have hI := (cont_diff_within_at_ext_coord_change I (g x₂) (g x) $
    local_equiv.mem_symm_trans_source _ hx₂ $ mem_ext_chart_source I (g x₂))
    .differentiable_within_at le_top,
  have hI' := (cont_diff_within_at_ext_coord_change I' (f x (g x)) (f x₂ (g x₂)) $
    local_equiv.mem_symm_trans_source _
    (mem_ext_chart_source I' (f x₂ (g x₂))) h3x₂).differentiable_within_at le_top,
  have h3f := (h2x₂.mdifferentiable_at le_rfl).2,
  refine fderiv_within.comp₃ _ hI' h3f hI _ _ _ _ (I.unique_diff _ $ mem_range_self _),
  { exact λ x _, mem_range_self _ },
  { exact λ x _, mem_range_self _ },
  { simp_rw [written_in_ext_chart_at, function.comp_apply,
      (ext_chart_at I (g x₂)).left_inv (mem_ext_chart_source I (g x₂))] },
  { simp_rw [function.comp_apply, (ext_chart_at I (g x)).left_inv hx₂] }
end

/-- The map `D_xf(x,y)` is `C^n` as a continuous linear map, assuming that `f` is a `C^(n+1)` map
between manifolds.
We have to insert appropriate coordinate changes to make sense of this statement.
This statement is general enough to work for partial derivatives / functions with parameters. -/
lemma cont_mdiff_at.mfderiv'' (f : M → M → M')
  (hf : cont_mdiff_at (I.prod I) I' n (function.uncurry f) (x, x)) (hmn : m + 1 ≤ n) :
  cont_mdiff_at I 𝓘(𝕜, E →L[𝕜] E') m
    (in_coordinates I I' id (λ x, f x x) (λ x', mfderiv I I' (f x') x') x) x :=
hf.mfderiv''' f id cont_mdiff_at_id hmn

/-- The map `mfderiv f` is `C^n` as a continuous linear map, assuming that `f` is `C^(n+1)`.
We have to insert appropriate coordinate changes to make sense of this statement. -/
lemma cont_mdiff_at.mfderiv' {f : M → M'}
  (hf : cont_mdiff_at I I' n f x) (hmn : m + 1 ≤ n) :
  cont_mdiff_at I 𝓘(𝕜, E →L[𝕜] E') m (in_coordinates I I' id f (mfderiv I I' f) x) x :=
begin
  have : cont_mdiff_at (I.prod I) I' n (λ x : M × M, f x.2) (x, x) :=
  cont_mdiff_at.comp (x, x) hf cont_mdiff_at_snd,
  apply cont_mdiff_at.mfderiv'' (λ x, f) this hmn
  -- apply cont_mdiff_at.mfderiv''' (λ x, f) id this cont_mdiff_at_id hmn
end

instance has_smooth_add_self : has_smooth_add 𝓘(𝕜, F) F :=
⟨by { convert cont_diff_add.cont_mdiff, exact model_with_corners_self_prod.symm,
  exact charted_space_self_prod }⟩

end smooth_manifold_with_corners

section maps

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
{E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
{E' : Type*} [normed_add_comm_group E'] [normed_space 𝕜 E']
{F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]
{H : Type*} [topological_space H]
{H' : Type*} [topological_space H']
{G : Type*} [topological_space G]
{G' : Type*} [topological_space G']
{I : model_with_corners 𝕜 E H} {I' : model_with_corners 𝕜 E' H'}
{J : model_with_corners 𝕜 F G} {J' : model_with_corners 𝕜 F G'}

variables {M : Type*} [topological_space M] [charted_space H M]
{M' : Type*} [topological_space M'] [charted_space H' M']
{N : Type*} [topological_space N] [charted_space G N]
{N' : Type*} [topological_space N'] [charted_space G' N']
{n : ℕ∞}
(f : C^∞⟮I, M; J, N⟯)

namespace cont_mdiff_map

/-- The first projection of a product, as a smooth map. -/
def fst : C^n⟮I.prod I', M × M'; I, M⟯ := ⟨prod.fst, cont_mdiff_fst⟩

/-- The second projection of a product, as a smooth map. -/
def snd : C^n⟮I.prod I', M × M'; I', M'⟯ := ⟨prod.snd, cont_mdiff_snd⟩

/-- Given two smooth maps `f` and `g`, this is the smooth map `(x, y) ↦ (f x, g y)`. -/
def prod_mk (f : C^n⟮J, N; I, M⟯) (g : C^n⟮J, N; I', M'⟯) : C^n⟮J, N; I.prod I', M × M'⟯ :=
⟨λ x, (f x, g x), f.2.prod_mk g.2⟩

end cont_mdiff_map

namespace diffeomorph

instance : continuous_map_class (M ≃ₘ⟮I, J⟯ N) M N :=
{ coe := coe_fn,
  coe_injective' := coe_fn_injective,
  map_continuous := λ f, f.continuous }

end diffeomorph

end maps

section
variables {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
  {H : Type*} [topological_space H] (I : model_with_corners ℝ E H) {M : Type*}
  [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
  {G : Type*} [normed_add_comm_group G] [normed_space ℝ G] [finite_dimensional ℝ G]
  {HG : Type*} [topological_space HG] (IG : model_with_corners ℝ G HG) {N : Type*}
  [topological_space N] [charted_space HG N] [smooth_manifold_with_corners IG N]

def filter.germ.cont_mdiff_at' {x : M} (φ : germ (𝓝 x) N) (n : ℕ∞) : Prop :=
quotient.lift_on' φ (λ f, cont_mdiff_at I IG n f x) (λ f g h, propext begin
  split,
  all_goals { refine λ H, H.congr_of_eventually_eq _ },
  exacts [h.symm, h]
end)
end
