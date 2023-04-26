import geometry.manifold.cont_mdiff_mfderiv

open bundle set function filter continuous_linear_map
open_locale manifold topology
noncomputable theory

section smooth_manifold_with_corners
open smooth_manifold_with_corners

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
  {E' : Type*} [normed_add_comm_group E'] [normed_space 𝕜 E']
  {F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]
  {F' : Type*} [normed_add_comm_group F'] [normed_space 𝕜 F']
  {H : Type*} [topological_space H] {I : model_with_corners 𝕜 E H}
  {H' : Type*} [topological_space H'] {I' : model_with_corners 𝕜 E' H'}
  {G : Type*} [topological_space G] {J : model_with_corners 𝕜 F G}
  {G' : Type*} [topological_space G'] {J' : model_with_corners 𝕜 F' G'}
  {M : Type*} [topological_space M] [charted_space H M]
  {M' : Type*} [topological_space M'] [charted_space H' M']
  {N : Type*} [topological_space N] [charted_space G N]
  {N' : Type*} [topological_space N'] [charted_space G' N']
  {F'' : Type*} [normed_add_comm_group F''] [normed_space 𝕜 F'']
variables {f : M → M'} {m n : ℕ∞} {s : set M} {x x' : M}

variables [smooth_manifold_with_corners I M] [smooth_manifold_with_corners I' M']
  [smooth_manifold_with_corners J N]

variables (I I')

/-- When `ϕ x` is a continuous linear map that changes vectors in charts around `f x` to vectors
in charts around `g x`, `in_tangent_coordinates I I' f g ϕ x₀ x` is a coordinate change of
this continuous linear map that makes sense from charts around `f x₀` to charts around `g x₀`
by composing it with appropriate coordinate changes.
Note that in the type of `ϕ` is more accurately
`Π x : N, tangent_space I (f x) →L[𝕜] tangent_space I' (g x)`.
We are unfolding `tangent_space` in this type so that Lean recognizes that the type of `ϕ` doesn't
actually depend on `f` or `g`.

This is the underlying function of the trivializations of the hom of (pullbacks of) tangent spaces.
-/
def in_tangent_coordinates {N} (f : N → M) (g : N → M')
  (ϕ : N → E →L[𝕜] E') : N → N → E →L[𝕜] E' :=
λ x₀ x, in_coordinates E (tangent_space I) E' (tangent_space I') (f x₀) (f x) (g x₀) (g x) (ϕ x)

/-- The map `in_coordinates` for the tangent bundle is trivial on the model spaces -/
lemma in_coordinates_tangent_bundle_core_model_space
  (x₀ x : H) (y₀ y : H') (ϕ : E →L[𝕜] E') :
    in_coordinates E (tangent_space I) E' (tangent_space I') x₀ x y₀ y ϕ = ϕ :=
begin
  refine (vector_bundle_core.in_coordinates_eq _ _ _ _ _).trans _,
  { exact mem_univ x },
  { exact mem_univ y },
  simp_rw [tangent_bundle_core_index_at, tangent_bundle_core_coord_change_model_space,
    continuous_linear_map.id_comp, continuous_linear_map.comp_id]
end

lemma in_tangent_coordinates_model_space (f : N → H) (g : N → H') (ϕ : N → E →L[𝕜] E') (x₀ : N) :
    in_tangent_coordinates I I' f g ϕ x₀ = ϕ :=
by simp_rw [in_tangent_coordinates, in_coordinates_tangent_bundle_core_model_space]

lemma in_tangent_coordinates_eq (f : N → M) (g : N → M') (ϕ : N → E →L[𝕜] E') {x₀ x : N}
  (hx : f x ∈ (chart_at H (f x₀)).source) (hy : g x ∈ (chart_at H' (g x₀)).source) :
  in_tangent_coordinates I I' f g ϕ x₀ x =
  (tangent_bundle_core I' M').coord_change (achart H' (g x)) (achart H' (g x₀)) (g x) ∘L ϕ x ∘L
  (tangent_bundle_core I M).coord_change (achart H (f x₀)) (achart H (f x)) (f x) :=
(tangent_bundle_core I M).in_coordinates_eq (tangent_bundle_core I' M') (ϕ x) hx hy

variables {I I'}
/-- The function that sends `x` to the `y`-derivative of `f(x,y)` at `g(x)` is `C^n` at `x₀`,
where the derivative is taken as a continuous linear map.
We have to assume that `f` is `C^(n+1)` at `(x₀, g(x₀))` and `g` is `C^n` at `x₀`.
We have to insert a coordinate change from `x₀` to `x` to make the derivative sensible.
`cont_mdiff_at.mfderiv_id` and `cont_mdiff_at.mfderiv_const` are special cases of this.

This lemma should be generalized to a `cont_mdiff_within_at` for `mfderiv_within`. If we do that, we
can deduce `cont_mdiff_on.cont_mdiff_on_tangent_map_within` from this.
-/
lemma cont_mdiff_at.mfderiv {x₀ : N} (f : N → M → M') (g : N → M)
  (hf : cont_mdiff_at (J.prod I) I' n (function.uncurry f) (x₀, g x₀))
  (hg : cont_mdiff_at J I m g x₀) (hmn : m + 1 ≤ n) :
  cont_mdiff_at J 𝓘(𝕜, E →L[𝕜] E') m
    (in_tangent_coordinates I I' g (λ x, f x (g x)) (λ x, mfderiv I I' (f x) (g x)) x₀) x₀ :=
begin
  have h4f : continuous_at (λ x, f x (g x)) x₀,
  { apply continuous_at.comp (by apply hf.continuous_at) (continuous_at_id.prod hg.continuous_at) },
  have h4f := h4f.preimage_mem_nhds (ext_chart_at_source_mem_nhds I' (f x₀ (g x₀))),
  have h3f := cont_mdiff_at_iff_cont_mdiff_at_nhds.mp (hf.of_le $ (self_le_add_left 1 m).trans hmn),
  have h2f : ∀ᶠ x₂ in 𝓝 x₀, cont_mdiff_at I I' 1 (f x₂) (g x₂),
  { refine ((continuous_at_id.prod hg.continuous_at).tendsto.eventually h3f).mono (λ x hx, _),
    exact hx.comp (g x) (cont_mdiff_at_const.prod_mk cont_mdiff_at_id) },
  have h2g := hg.continuous_at.preimage_mem_nhds (ext_chart_at_source_mem_nhds I (g x₀)),
  have : cont_diff_within_at 𝕜 m (λ x, fderiv_within 𝕜
    (ext_chart_at I' (f x₀ (g x₀)) ∘ f ((ext_chart_at J x₀).symm x) ∘ (ext_chart_at I (g x₀)).symm)
    (range I) (ext_chart_at I (g x₀) (g ((ext_chart_at J x₀).symm x))))
    (range J) (ext_chart_at J x₀ x₀),
  { rw [cont_mdiff_at_iff] at hf hg,
    simp_rw [function.comp, uncurry, ext_chart_at_prod, local_equiv.prod_coe_symm,
      model_with_corners.range_prod] at hf ⊢,
    refine cont_diff_within_at.fderiv_within _ hg.2 I.unique_diff hmn (mem_range_self _) _,
    { simp_rw [ext_chart_at_to_inv], exact hf.2 },
    { rw [← image_subset_iff],
      rintros _ ⟨x, hx, rfl⟩,
      exact mem_range_self _ } },
  have : cont_mdiff_at J 𝓘(𝕜, E →L[𝕜] E') m
    (λ x, fderiv_within 𝕜 (ext_chart_at I' (f x₀ (g x₀)) ∘ f x ∘ (ext_chart_at I (g x₀)).symm)
    (range I) (ext_chart_at I (g x₀) (g x))) x₀,
  { simp_rw [cont_mdiff_at_iff_source_of_mem_source (mem_chart_source G x₀),
      cont_mdiff_within_at_iff_cont_diff_within_at, function.comp],
    exact this },
  have : cont_mdiff_at J 𝓘(𝕜, E →L[𝕜] E') m
    (λ x, fderiv_within 𝕜 (ext_chart_at I' (f x₀ (g x₀)) ∘ (ext_chart_at I' (f x (g x))).symm ∘
      written_in_ext_chart_at I I' (g x) (f x) ∘ ext_chart_at I (g x) ∘
      (ext_chart_at I (g x₀)).symm) (range I) (ext_chart_at I (g x₀) (g x))) x₀,
  { refine this.congr_of_eventually_eq _,
    filter_upwards [h2g, h2f],
    intros x₂ hx₂ h2x₂,
    have : ∀ x ∈ (ext_chart_at I (g x₀)).symm ⁻¹' (ext_chart_at I (g x₂)).source ∩
        (ext_chart_at I (g x₀)).symm ⁻¹' (f x₂ ⁻¹' (ext_chart_at I' (f x₂ (g x₂))).source),
      (ext_chart_at I' (f x₀ (g x₀)) ∘ (ext_chart_at I' (f x₂ (g x₂))).symm ∘
      written_in_ext_chart_at I I' (g x₂) (f x₂) ∘ ext_chart_at I (g x₂) ∘
      (ext_chart_at I (g x₀)).symm) x =
      ext_chart_at I' (f x₀ (g x₀)) (f x₂ ((ext_chart_at I (g x₀)).symm x)),
    { rintro x ⟨hx, h2x⟩,
      simp_rw [written_in_ext_chart_at, function.comp_apply],
      rw [(ext_chart_at I (g x₂)).left_inv hx, (ext_chart_at I' (f x₂ (g x₂))).left_inv h2x] },
    refine filter.eventually_eq.fderiv_within_eq_nhds (I.unique_diff _ $ mem_range_self _) _,
    refine eventually_of_mem (inter_mem _ _) this,
    { exact ext_chart_at_preimage_mem_nhds' _ _ hx₂ (ext_chart_at_source_mem_nhds I (g x₂)) },
    refine ext_chart_at_preimage_mem_nhds' _ _ hx₂ _,
    exact (h2x₂.continuous_at).preimage_mem_nhds (ext_chart_at_source_mem_nhds _ _) },
  /- The conclusion is equal to the following, when unfolding coord_change of
    `tangent_bundle_core` -/
  have : cont_mdiff_at J 𝓘(𝕜, E →L[𝕜] E') m
    (λ x, (fderiv_within 𝕜 (ext_chart_at I' (f x₀ (g x₀)) ∘ (ext_chart_at I' (f x (g x))).symm)
        (range I') (ext_chart_at I' (f x (g x)) (f x (g x)))).comp
        ((mfderiv I I' (f x) (g x)).comp (fderiv_within 𝕜 (ext_chart_at I (g x) ∘
        (ext_chart_at I (g x₀)).symm) (range I) (ext_chart_at I (g x₀) (g x))))) x₀,
  { refine this.congr_of_eventually_eq _,
    filter_upwards [h2g, h2f, h4f],
    intros x₂ hx₂ h2x₂ h3x₂,
    symmetry,
    rw [(h2x₂.mdifferentiable_at le_rfl).mfderiv],
    have hI := (cont_diff_within_at_ext_coord_change I (g x₂) (g x₀) $
      local_equiv.mem_symm_trans_source _ hx₂ $ mem_ext_chart_source I (g x₂))
      .differentiable_within_at le_top,
    have hI' := (cont_diff_within_at_ext_coord_change I' (f x₀ (g x₀)) (f x₂ (g x₂)) $
      local_equiv.mem_symm_trans_source _
      (mem_ext_chart_source I' (f x₂ (g x₂))) h3x₂).differentiable_within_at le_top,
    have h3f := (h2x₂.mdifferentiable_at le_rfl).2,
    refine fderiv_within.comp₃ _ hI' h3f hI _ _ _ _ (I.unique_diff _ $ mem_range_self _),
    { exact λ x _, mem_range_self _ },
    { exact λ x _, mem_range_self _ },
    { simp_rw [written_in_ext_chart_at, function.comp_apply,
        (ext_chart_at I (g x₂)).left_inv (mem_ext_chart_source I (g x₂))] },
    { simp_rw [function.comp_apply, (ext_chart_at I (g x₀)).left_inv hx₂] } },
  refine this.congr_of_eventually_eq _,
  filter_upwards [h2g, h4f] with x hx h2x,
  rw [in_tangent_coordinates_eq],
  { refl },
  { rwa [ext_chart_at_source] at hx },
  { rwa [ext_chart_at_source] at h2x },
end

/-- The function `x ↦ D_yf(x,y)` is `C^n` at `x₀`, where the derivative is taken as a continuous
linear map. We have to assume that `f` is `C^(n+1)` at `(x₀, x₀)`.
We have to insert a coordinate change from `x₀` to `x` to make the derivative sensible.
This is a special case of `cont_mdiff_at.mfderiv` (with `g = id`),
and `cont_mdiff_at.mfderiv_const` is a special case of this.
-/
lemma cont_mdiff_at.mfderiv_id {x₀ : M} (f : M → M → M')
  (hf : cont_mdiff_at (I.prod I) I' n (function.uncurry f) (x₀, x₀)) (hmn : m + 1 ≤ n) :
  cont_mdiff_at I 𝓘(𝕜, E →L[𝕜] E') m
    (in_tangent_coordinates I I' id (λ x, f x x) (λ x, mfderiv I I' (f x) x) x₀) x₀ :=
hf.mfderiv f id cont_mdiff_at_id hmn

/-- The derivative `D_yf(y)` is `C^n` at `x₀`, where the derivative is taken as a continuous
linear map. We have to assume that `f` is `C^(n+1)` at `x₀`.
We have to insert a coordinate change from `x₀` to `x` to make the derivative sensible.
This is a special case of See `cont_mdiff_at.mfderiv_id` where `f` does not contain any parameters.
-/
lemma cont_mdiff_at.mfderiv_const {x₀ : M} {f : M → M'}
  (hf : cont_mdiff_at I I' n f x₀) (hmn : m + 1 ≤ n) :
  cont_mdiff_at I 𝓘(𝕜, E →L[𝕜] E') m (in_tangent_coordinates I I' id f (mfderiv I I' f) x₀) x₀ :=
begin
  have : cont_mdiff_at (I.prod I) I' n (λ x : M × M, f x.2) (x₀, x₀) :=
  cont_mdiff_at.comp (x₀, x₀) hf cont_mdiff_at_snd,
  apply cont_mdiff_at.mfderiv_id (λ x, f) this hmn
end

end smooth_manifold_with_corners
