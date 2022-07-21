import geometry.manifold.diffeomorph

open bundle set function filter
open_locale manifold topological_space

namespace set

variables {α β γ δ : Type*} {f : α → β → γ} {s s₁ : set α} {t t₁ : set β} {x : α} {y : β}

lemma image2.some_prop (z : image2 f s t) : ∃ (y : s × t), f y.1 y.2 = z :=
let ⟨_, ⟨x, y, hx, hy, rfl⟩⟩ := z in ⟨⟨⟨x, hx⟩, ⟨y, hy⟩⟩, rfl⟩

/-- Choose arbitrary elements in the domain mapped to `z`. Probably not mathlib-worthy. -/
noncomputable def image2.some (f : α → β → γ) (s : set α) (t : set β) (z : image2 f s t) : s × t :=
classical.some (image2.some_prop z)

lemma image2.some_spec (f : α → β → γ) (hx : x ∈ s) (hy : y ∈ t) :
  (λ x : s × t, f x.1 x.2) (image2.some f s t ⟨f x y, mem_image2_of_mem hx hy⟩) = f x y :=
classical.some_spec (image2.some_prop ⟨f x y, mem_image2_of_mem hx hy⟩)

lemma image2.some_spec_fst (f : α → β → γ) (hx : x ∈ s) (hy : y ∈ t) : ∃ y' ∈ t,
  f (image2.some f s t ⟨f x y, mem_image2_of_mem hx hy⟩).1 y' = f x y :=
⟨(image2.some f s t ⟨f x y, mem_image2_of_mem hx hy⟩).2, subtype.mem _, image2.some_spec f hx hy⟩

lemma image2.some_spec_snd (f : α → β → γ) (hx : x ∈ s) (hy : y ∈ t) : ∃ x' ∈ s,
  f x' (image2.some f s t ⟨f x y, mem_image2_of_mem hx hy⟩).2 = f x y :=
⟨(image2.some f s t ⟨f x y, mem_image2_of_mem hx hy⟩).1, subtype.mem _, image2.some_spec f hx hy⟩

end set

section charted_space

variables {M H : Type*} [topological_space M] [topological_space H] [charted_space H M]
  (G : structure_groupoid H)

variable (H)
/-- `achart H x` is the chart at `x`, considered as an element of the atlas. -/
def achart (x : M) : atlas H M := ⟨chart_at H x, chart_mem_atlas H x⟩

lemma achart_def (x : M) : achart H x = ⟨chart_at H x, chart_mem_atlas H x⟩ := rfl
@[simp] lemma coe_achart (x : M) : (achart H x : local_homeomorph M H) = chart_at H x := rfl
@[simp] lemma achart_val (x : M) : (achart H x).1 = chart_at H x := rfl

variable {H}

end charted_space


namespace model_with_corners

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {E : Type*} [normed_group E] [normed_space 𝕜 E]
  {H : Type*} [topological_space H]
  {M : Type*} [topological_space M] (f : local_homeomorph M H) (I : model_with_corners 𝕜 E H)

lemma injective : injective I :=
I.left_inverse.injective

lemma preimage_image (s : set H) : I ⁻¹' (I '' s) = s :=
I.injective.preimage_image s

end model_with_corners

section smooth_manifold_with_corners
open smooth_manifold_with_corners

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {E : Type*} [normed_group E] [normed_space 𝕜 E]
  {E' : Type*} [normed_group E'] [normed_space 𝕜 E']
  {F : Type*} [normed_group F] [normed_space 𝕜 F]
  {H : Type*} [topological_space H] {I : model_with_corners 𝕜 E H}
  {H' : Type*} [topological_space H'] {I' : model_with_corners 𝕜 E' H'}
  {G : Type*} [topological_space G] {J : model_with_corners 𝕜 F G}
  {M : Type*} [topological_space M] [charted_space H M]
  {M' : Type*} [topological_space M'] [charted_space H' M']
  {N : Type*} [topological_space N] [charted_space G N]
variables {f : M → M'} {m n : with_top ℕ} {s : set M} {x : M}

lemma ext_chart_preimage_mem_nhds' {x' : M} {t : set M}
  (h : x' ∈ (ext_chart_at I x).source) (ht : t ∈ 𝓝 x') :
  (ext_chart_at I x).symm ⁻¹' t ∈ 𝓝 (ext_chart_at I x x') :=
begin
  apply (ext_chart_continuous_at_symm' I x h).preimage_mem_nhds,
  rwa (ext_chart_at I x).left_inv h
end

lemma cont_mdiff_at_iff_target {x : M} :
  cont_mdiff_at I I' n f x ↔
    continuous_at f x ∧ cont_mdiff_at I 𝓘(𝕜, E') n (ext_chart_at I' (f x) ∘ f) x :=
by rw [cont_mdiff_at, cont_mdiff_at, cont_mdiff_within_at_iff_target, continuous_within_at_univ]

namespace basic_smooth_vector_bundle_core
variables [smooth_manifold_with_corners I M] (Z : basic_smooth_vector_bundle_core I M E')

lemma chart_apply (z : Z.to_topological_vector_bundle_core.total_space) :
  Z.chart (chart_mem_atlas H x) z = (chart_at H x z.proj,
    Z.coord_change (achart H z.proj) (achart H x) (achart H z.proj z.proj) z.2) :=
rfl

/-- A version of `cont_mdiff_at_iff_target` when the codomain is the total space of
  a `basic_smooth_vector_bundle_core`. The continuity condition in the RHS is weaker. -/
lemma cont_mdiff_at_iff_target {f : N → Z.to_topological_vector_bundle_core.total_space}
  {x : N} {n : with_top ℕ} :
  cont_mdiff_at J (I.prod 𝓘(𝕜, E')) n f x ↔ continuous_at (bundle.total_space.proj ∘ f) x ∧
  cont_mdiff_at J 𝓘(𝕜, E × E') n (ext_chart_at (I.prod 𝓘(𝕜, E')) (f x) ∘ f) x :=
begin
  let Z' := Z.to_topological_vector_bundle_core,
  rw [cont_mdiff_at_iff_target, and.congr_left_iff],
  refine λ hf, ⟨λ h, Z'.continuous_proj.continuous_at.comp h, λ h, _⟩,
  exact (Z'.local_triv ⟨chart_at _ (f x).1, chart_mem_atlas _ _⟩).to_fiber_bundle_trivialization
    .continuous_at_of_comp_left h (mem_chart_source _ _) (h.prod hf.continuous_at.snd)
end

end basic_smooth_vector_bundle_core

lemma tangent_bundle_core_coord_change_achart [smooth_manifold_with_corners I M]
  (x x' : M) (z : H) :
  (tangent_bundle_core I M).coord_change (achart H x) (achart H x') z =
  fderiv_within 𝕜 (ext_chart_at I x' ∘ (ext_chart_at I x).symm) (range I) (I z) :=
rfl

variables (I)

lemma cont_diff_on_coord_change' [smooth_manifold_with_corners I M]
  {e e' : local_homeomorph M H} (h : e ∈ atlas H M) (h' : e' ∈ atlas H M) :
  cont_diff_on 𝕜 ⊤ (I ∘ (e.symm ≫ₕ e') ∘ I.symm) (I.symm ⁻¹' (e.symm ≫ₕ e').source ∩ range I) :=
(has_groupoid.compatible (cont_diff_groupoid ⊤ I) h h').1

lemma ext_chart_at_target (x : M) : (ext_chart_at I x).target =
  I.symm ⁻¹' (chart_at H x).target ∩ range I :=
by simp_rw [ext_chart_at, local_equiv.trans_target, I.target_eq, I.to_local_equiv_coe_symm,
  inter_comm]

lemma ext_coord_change_source (x x' : M) :
  ((ext_chart_at I x').symm ≫ ext_chart_at I x).source =
  I '' ((chart_at H x').symm ≫ₕ (chart_at H x)).source :=
by { simp_rw [local_equiv.trans_source, I.image_eq, ext_chart_at_source, local_equiv.symm_source,
      ext_chart_at_target, inter_right_comm _ (range I)], refl }

variables [smooth_manifold_with_corners I M] [smooth_manifold_with_corners I' M']

lemma cont_diff_on_ext_coord_change (x x' : M) :
  cont_diff_on 𝕜 ⊤ (ext_chart_at I x ∘ (ext_chart_at I x').symm)
  ((ext_chart_at I x').symm ≫ ext_chart_at I x).source :=
by { rw [ext_coord_change_source, I.image_eq], exact (has_groupoid.compatible
  (cont_diff_groupoid ⊤ I) (chart_mem_atlas H x') (chart_mem_atlas H x)).1 }

lemma cont_diff_within_at_ext_coord_change (x x' : M) {y : E}
  (hy : y ∈ ((ext_chart_at I x').symm ≫ ext_chart_at I x).source) :
  cont_diff_within_at 𝕜 ⊤ (ext_chart_at I x ∘ (ext_chart_at I x').symm) (range I) y :=
begin
  apply (cont_diff_on_ext_coord_change I x x' y hy).mono_of_mem,
  rw [ext_coord_change_source] at hy ⊢,
  obtain ⟨z, hz, rfl⟩ := hy,
  exact I.image_mem_nhds_within ((local_homeomorph.open_source _).mem_nhds hz)
end

variables (𝕜)
lemma ext_chart_self_eq {x : H} : ⇑(ext_chart_at I x) = I := rfl
lemma ext_chart_self_apply {x y : H} : ext_chart_at I x y = I y := rfl
lemma ext_chart_model_space_apply {x y : E} : ext_chart_at 𝓘(𝕜, E) x y = y := rfl
variables {𝕜 I}

/-- Note: does not hold for `n = ∞`. -/
lemma cont_mdiff_at_iff_cont_mdiff_at_nhds {n : ℕ} :
  cont_mdiff_at I I' n f x ↔ ∀ᶠ x' in 𝓝 x, cont_mdiff_at I I' n f x' :=
begin
  refine ⟨_, λ h, h.self_of_nhds⟩,
  rw [cont_mdiff_at_iff_cont_mdiff_on_nhds],
  rintro ⟨u, hu, h⟩,
  obtain ⟨v, hvu, hv, hxv⟩ := mem_nhds_iff.mp hu,
  refine eventually_of_mem (hv.mem_nhds hxv) (λ x' hx', _),
  exact (h x' (hvu hx')).cont_mdiff_at (mem_of_superset (hv.mem_nhds hx') hvu)
end

lemma cont_mdiff_at.mfderiv' {f : M → M'}
  (hf : cont_mdiff_at I I' n f x) (hmn : m + 1 ≤ n) :
  cont_mdiff_at I 𝓘(𝕜, E →L[𝕜] E') m
  (λ x', (tangent_bundle_core I' M').coord_change (achart H' (f x')) (achart H' (f x))
    (chart_at H' (f x') (f x')) ∘L mfderiv I I' f x' ∘L
    (tangent_bundle_core I M).coord_change (achart H x) (achart H x') (chart_at H x x')) x :=
begin
  have h2f := cont_mdiff_at_iff_cont_mdiff_at_nhds.mp (hf.of_le $ (self_le_add_left 1 m).trans hmn),
  have : cont_diff_within_at 𝕜 m (fderiv_within 𝕜 (written_in_ext_chart_at I I' x f) (range I))
    (range I) (ext_chart_at I x x),
  { rw [cont_mdiff_at_iff] at hf, exact hf.2.fderiv_within I.unique_diff hmn (mem_range_self _) },
  have : cont_mdiff_at I 𝓘(𝕜, E →L[𝕜] E') m
    (λ x', fderiv_within 𝕜 (written_in_ext_chart_at I I' x f) (range I) (ext_chart_at I x x')) x,
  { rw [cont_mdiff_at_iff],
    refine ⟨(this.continuous_within_at.comp (ext_chart_at_continuous_at I x).continuous_within_at
      (λ _ _, mem_range_self _)).continuous_at univ_mem, _⟩,
    simp_rw [function.comp, ext_chart_model_space_apply],
    refine this.congr_of_eventually_eq' _ (mem_range_self _),
    { refine eventually_of_mem (ext_chart_at_target_mem_nhds_within I x) (λ x' hx', _),
      simp_rw [(ext_chart_at I x).right_inv hx'] } },
  have : cont_mdiff_at I 𝓘(𝕜, E →L[𝕜] E') m
    (λ x', fderiv_within 𝕜 (ext_chart_at I' (f x) ∘ (ext_chart_at I' (f x')).symm ∘
      written_in_ext_chart_at I I' x' f ∘ ext_chart_at I x' ∘ (ext_chart_at I x).symm)
      (range I) (ext_chart_at I x x')) x,
  { refine this.congr_of_eventually_eq _,
    filter_upwards [ext_chart_at_source_mem_nhds I x, h2f],
    intros x₂ hx₂ h2x₂,
    have : ∀ x' ∈ (ext_chart_at I x).symm ⁻¹' (ext_chart_at I x₂).source ∩
        (ext_chart_at I x).symm ⁻¹' (f ⁻¹' (ext_chart_at I' (f x₂)).source),
      (ext_chart_at I' (f x) ∘ (ext_chart_at I' (f x₂)).symm ∘
      written_in_ext_chart_at I I' x₂ f ∘ ext_chart_at I x₂ ∘ (ext_chart_at I x).symm) x' =
      written_in_ext_chart_at I I' x f x',
    { rintro x' ⟨hx', h2x'⟩,
      simp_rw [written_in_ext_chart_at, function.comp_apply],
      rw [(ext_chart_at I x₂).left_inv hx', (ext_chart_at I' (f x₂)).left_inv h2x'] },
    refine filter.eventually_eq.fderiv_within_eq_nhds (I.unique_diff _ $ mem_range_self _) _,
    refine eventually_of_mem (inter_mem _ _) this,
    { exact ext_chart_preimage_mem_nhds' hx₂ (ext_chart_at_source_mem_nhds I x₂) },
    refine ext_chart_preimage_mem_nhds' hx₂ _,
    exact (h2x₂.continuous_at).preimage_mem_nhds (ext_chart_at_source_mem_nhds _ _) },
  /- The conclusion is the same as the following, when unfolding coord_change of
    `tangent_bundle_core` -/
  change cont_mdiff_at I 𝓘(𝕜, E →L[𝕜] E') m
    (λ x', (fderiv_within 𝕜 (ext_chart_at I' (f x) ∘ (ext_chart_at I' (f x')).symm)
        (range I') (ext_chart_at I' (f x') (f x'))).comp ((mfderiv I I' f x').comp
          (fderiv_within 𝕜 (ext_chart_at I x' ∘ (ext_chart_at I x).symm)
             (range I) (ext_chart_at I x x')))) x,
  refine this.congr_of_eventually_eq _,
  filter_upwards [ext_chart_at_source_mem_nhds I x, h2f,
    hf.continuous_at.preimage_mem_nhds (ext_chart_at_source_mem_nhds I' (f x))],
  intros x₂ hx₂ h2x₂ h3x₂,
  symmetry,
  rw [(h2x₂.mdifferentiable_at le_rfl).mfderiv],
  have hI := (cont_diff_within_at_ext_coord_change I x₂ x $ local_equiv.mem_symm_trans_source _
    hx₂ $ mem_ext_chart_source I x₂).differentiable_within_at le_top,
  have hI' := (cont_diff_within_at_ext_coord_change I' (f x) (f x₂) $
    local_equiv.mem_symm_trans_source _
    (mem_ext_chart_source I' (f x₂)) h3x₂).differentiable_within_at le_top,
  have h3f := (h2x₂.mdifferentiable_at le_rfl).2,
  refine fderiv_within.comp₃ _ hI' h3f hI _ _ _ _ (I.unique_diff _ $ mem_range_self _),
  { exact λ x _, mem_range_self _ },
  { exact λ x _, mem_range_self _ },
  { simp_rw [written_in_ext_chart_at, function.comp_apply,
      (ext_chart_at I x₂).left_inv (mem_ext_chart_source I x₂)] },
  { simp_rw [function.comp_apply, (ext_chart_at I x).left_inv hx₂] }
end

end smooth_manifold_with_corners

section maps

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{E' : Type*} [normed_group E'] [normed_space 𝕜 E']
{F : Type*} [normed_group F] [normed_space 𝕜 F]
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
{n : with_top ℕ}
(f : C^∞⟮I, M; J, N⟯)

namespace cont_mdiff_map

instance : continuous_map_class C^n⟮I, M; J, N⟯ M N :=
{ coe := coe_fn,
  coe_injective' := coe_inj,
  map_continuous := λ f, f.cont_mdiff_to_fun.continuous }

/-- The first projection of a product, as a smooth map. -/
def fst : C^n⟮I.prod I', M × M'; I, M⟯ := ⟨prod.fst, cont_mdiff_fst⟩

/-- The second projection of a product, as a smooth map. -/
def snd : C^n⟮I.prod I', M × M'; I', M'⟯ := ⟨prod.snd, cont_mdiff_snd⟩

end cont_mdiff_map

namespace diffeomorph

instance : continuous_map_class (M ≃ₘ⟮I, J⟯ N) M N :=
{ coe := coe_fn,
  coe_injective' := coe_fn_injective,
  map_continuous := λ f, f.continuous }

end diffeomorph

end maps
