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

variables (H)
lemma mem_achart_source (x : M) : x ∈ (achart H x).1.source :=
mem_chart_source H x
variables {H}

end charted_space


namespace model_with_corners

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
  {H : Type*} [topological_space H]
  {M : Type*} [topological_space M] (f : local_homeomorph M H) (I : model_with_corners 𝕜 E H)

lemma preimage_image (s : set H) : I ⁻¹' (I '' s) = s :=
I.injective.preimage_image s

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
variables {f : M → M'} {m n : with_top ℕ} {s : set M} {x : M}

lemma cont_mdiff_at_iff_target {x : M} :
  cont_mdiff_at I I' n f x ↔
    continuous_at f x ∧ cont_mdiff_at I 𝓘(𝕜, E') n (ext_chart_at I' (f x) ∘ f) x :=
by rw [cont_mdiff_at, cont_mdiff_at, cont_mdiff_within_at_iff_target, continuous_within_at_univ]

section boundary

variables (I M)

/-- An element is on the boundary of a manifold `M` if its chart maps it to the frontier of the
model space. Note: this also includes all corners of `M`. -/
def boundary : set M := {x : M | ext_chart_at I x x ∈ frontier (range I) }

variables {I M}

lemma mem_boundary {x : M} : x ∈ boundary I M ↔ ext_chart_at I x x ∈ frontier (range I) := iff.rfl

lemma mem_boundary_iff_of_mem {x x' : M} (hx : x ∈ (ext_chart_at I x').source) :
  x ∈ boundary I M ↔ ext_chart_at I x' x ∈ frontier (range I) :=
sorry

end boundary

namespace basic_smooth_vector_bundle_core
variables [smooth_manifold_with_corners I M] (Z : basic_smooth_vector_bundle_core I M E')

lemma coord_change_comp' {i j k : atlas H M} {x : M}
  (hi : x ∈ i.1.source) (hj : x ∈ j.1.source) (hk : x ∈ k.1.source) (v : E') :
  Z.coord_change j k (j x) (Z.coord_change i j (i x) v) = Z.coord_change i k (i x) v :=
begin
  rw [show j x = _, by rw [← i.1.left_inv hi]],
  apply Z.coord_change_comp,
  simp only [hi, hj, hk] with mfld_simps
end

lemma coord_change_self' {i : atlas H M} {x : M} (hi : x ∈ i.1.source) (v : E') :
  Z.coord_change i i (i x) v = v :=
Z.coord_change_self i (i x) (i.1.maps_to hi) v

lemma coord_change_comp_eq_self (i j : atlas H M) {x : H}
  (hx : x ∈ (i.1.symm.trans j.1).source) (v : E') :
  Z.coord_change j i (i.1.symm.trans j.1 x) (Z.coord_change i j x v) = v :=
begin
  rw [Z.coord_change_comp i j i x _ v, Z.coord_change_self _ _ hx.1],
  simp only with mfld_simps at hx,
  simp only [hx.1, hx.2] with mfld_simps
end

lemma coord_change_comp_eq_self' {i j : atlas H M} {x : M}
  (hi : x ∈ i.1.source) (hj : x ∈ j.1.source) (v : E') :
  Z.coord_change j i (j x) (Z.coord_change i j (i x) v) = v :=
by rw [Z.coord_change_comp' hi hj hi v, Z.coord_change_self' hi]

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

lemma smooth_iff_target {f : N → Z.to_topological_vector_bundle_core.total_space} :
  smooth J (I.prod 𝓘(𝕜, E')) f ↔ continuous (bundle.total_space.proj ∘ f) ∧
  ∀ x, smooth_at J 𝓘(𝕜, E × E') (ext_chart_at (I.prod 𝓘(𝕜, E')) (f x) ∘ f) x :=
by simp_rw [smooth, smooth_at, cont_mdiff, Z.cont_mdiff_at_iff_target, forall_and_distrib,
  continuous_iff_continuous_at]

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

variables [smooth_manifold_with_corners I M] [smooth_manifold_with_corners I' M']
variables {𝕜 I}

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
    { exact ext_chart_preimage_mem_nhds' _ _ hx₂ (ext_chart_at_source_mem_nhds I x₂) },
    refine ext_chart_preimage_mem_nhds' _ _ hx₂ _,
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

lemma cont_diff_within_at.comp_cont_mdiff_within_at
  {g : F → F''} {f : M → F} {s : set M} {t : set F} {x : M}
  (hg : cont_diff_within_at 𝕜 n g t (f x))
  (hf : cont_mdiff_within_at I 𝓘(𝕜, F) n f s x) (h : s ⊆ f ⁻¹' t) :
  cont_mdiff_within_at I 𝓘(𝕜, F'') n (g ∘ f) s x :=
begin
  rw cont_mdiff_within_at_iff at *,
  refine ⟨hg.continuous_within_at.comp hf.1 h, _⟩,
  rw [← (ext_chart_at I x).left_inv (mem_ext_chart_source I x)] at hg,
  apply cont_diff_within_at.comp _ (by exact hg) hf.2 _,
  exact (inter_subset_left _ _).trans (preimage_mono h)
end

lemma cont_diff_at.comp_cont_mdiff_at {g : F → F''} {f : M → F} {x : M}
  (hg : cont_diff_at 𝕜 n g (f x)) (hf : cont_mdiff_at I 𝓘(𝕜, F) n f x) :
  cont_mdiff_at I 𝓘(𝕜, F'') n (g ∘ f) x :=
hg.comp_cont_mdiff_within_at hf subset.rfl

lemma cont_diff.comp_cont_mdiff {g : F → F''} {f : M → F}
  (hg : cont_diff 𝕜 n g) (hf : cont_mdiff I 𝓘(𝕜, F) n f) :
  cont_mdiff I 𝓘(𝕜, F'') n (g ∘ f) :=
λ x, hg.cont_diff_at.comp_cont_mdiff_at (hf x)

-- the following proof takes very long in pure term mode
lemma cont_mdiff_at.clm_comp {g : M → F →L[𝕜] F''} {f : M → F' →L[𝕜] F} {x : M}
  (hg : cont_mdiff_at I 𝓘(𝕜, F →L[𝕜] F'') n g x) (hf : cont_mdiff_at I 𝓘(𝕜, F' →L[𝕜] F) n f x) :
  cont_mdiff_at I 𝓘(𝕜, F' →L[𝕜] F'') n (λ x, (g x).comp (f x)) x :=
@cont_diff_at.comp_cont_mdiff_at 𝕜 _ E _ _ ((F →L[𝕜] F'') × (F' →L[𝕜] F)) _ _ _ _ _ _ _ _
  _ _ _ _ _
  (λ x, x.1.comp x.2) (λ x, (g x, f x)) x
  (by { apply cont_diff.cont_diff_at, apply is_bounded_bilinear_map.cont_diff, exact is_bounded_bilinear_map_comp }) (hg.prod_mk_space hf)

lemma cont_mdiff.clm_comp {g : M → F →L[𝕜] F''} {f : M → F' →L[𝕜] F}
  (hg : cont_mdiff I 𝓘(𝕜, F →L[𝕜] F'') n g) (hf : cont_mdiff I 𝓘(𝕜, F' →L[𝕜] F) n f) :
  cont_mdiff I 𝓘(𝕜, F' →L[𝕜] F'') n (λ x, (g x).comp (f x)) :=
λ x, (hg x).clm_comp (hf x)

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
