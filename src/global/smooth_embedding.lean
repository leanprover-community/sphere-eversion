import topology.metric_space.hausdorff_distance
import topology.uniform_space.separation
import geometry.manifold.cont_mdiff
import global.indexing
import to_mathlib.topology.paracompact
import to_mathlib.topology.local_homeomorph
import to_mathlib.topology.algebra.order.compact
import to_mathlib.topology.nhds_set
import to_mathlib.geometry.manifold.charted_space
import to_mathlib.geometry.manifold.smooth_manifold_with_corners
import to_mathlib.analysis.normed_space.misc

noncomputable theory

open set equiv
open_locale manifold topological_space

section general
variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
  {H : Type*} [topological_space H]
  (I : model_with_corners 𝕜 E H)
  (M : Type*) [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
  {E' : Type*} [normed_add_comm_group E'] [normed_space 𝕜 E']
  {H' : Type*} [topological_space H']
  (I' : model_with_corners 𝕜 E' H')
  (M' : Type*) [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M']

structure open_smooth_embedding  :=
(to_fun : M → M')
(inv_fun : M' → M)
(left_inv'   : ∀{x}, inv_fun (to_fun x) = x)
(open_map : is_open_map to_fun)
(smooth_to : smooth I I' to_fun)
(smooth_inv : smooth_on I' I inv_fun (range to_fun))

instance : has_coe_to_fun (open_smooth_embedding I M I' M') (λ _, M → M') :=
⟨open_smooth_embedding.to_fun⟩

namespace open_smooth_embedding

variables {I I' M M'} (f : open_smooth_embedding I M I' M')

@[simp] lemma coe_mk (f g h₁ h₂ h₃ h₄) :
  ⇑(⟨f, g, h₁, h₂, h₃, h₄⟩ : open_smooth_embedding I M I' M') = f :=
rfl

@[simp] lemma left_inv (x : M) : f.inv_fun (f x) = x := by apply f.left_inv'

@[simp] lemma inv_fun_comp_coe : f.inv_fun ∘ f = id := funext f.left_inv

@[simp] lemma right_inv {y : M'} (hy : y ∈ range f) : f (f.inv_fun y) = y :=
by { obtain ⟨x, rfl⟩ := hy, rw [f.left_inv] }

lemma coe_comp_inv_fun_eventually_eq (x : M) : f ∘ f.inv_fun =ᶠ[𝓝 (f x)] id :=
filter.eventually_of_mem (f.open_map.range_mem_nhds x) $ λ y hy, f.right_inv hy

lemma injective : function.injective f :=
function.left_inverse.injective (left_inv f)

protected lemma continuous : continuous f := f.smooth_to.continuous

lemma is_open_range : is_open (range f) :=
f.open_map.is_open_range

lemma smooth_at_inv {y : M'} (hy : y ∈ range f) : smooth_at I' I f.inv_fun y :=
(f.smooth_inv y hy).cont_mdiff_at $ f.is_open_range.mem_nhds hy

/- Note that we are slightly abusing the fact that `tangent_space I x` and
`tangent_space I (f.inv_fun (f x))` are both definitionally `E` below. -/
def fderiv (x : M) : tangent_space I x ≃L[𝕜] tangent_space I' (f x) :=
have h₁ : mdifferentiable_at I' I f.inv_fun (f x) := ((f.smooth_inv (f x) (mem_range_self x)
  ).mdifferentiable_within_at le_top).mdifferentiable_at (f.open_map.range_mem_nhds x),
have h₂ : mdifferentiable_at I I' f x := f.smooth_to.cont_mdiff.mdifferentiable le_top _,
continuous_linear_equiv.equiv_of_inverse
  (mfderiv I I' f x)
  (mfderiv I' I f.inv_fun (f x))
begin
  intros v,
  rw [← continuous_linear_map.comp_apply, ← mfderiv_comp x h₁ h₂, f.inv_fun_comp_coe, mfderiv_id,
    continuous_linear_map.coe_id', id.def],
end
begin
  intros v,
  have hx : x = f.inv_fun (f x), { rw f.left_inv, },
  have hx' : f (f.inv_fun (f x)) = f x, { rw f.left_inv, },
  rw hx at h₂,
  rw [hx, hx', ← continuous_linear_map.comp_apply, ← mfderiv_comp (f x) h₂ h₁, ((has_mfderiv_at_id
    I' (f x)).congr_of_eventually_eq (f.coe_comp_inv_fun_eventually_eq x)).mfderiv,
    continuous_linear_map.coe_id', id.def],
end

@[simp] lemma fderiv_coe (x : M) :
  (f.fderiv x : tangent_space I x →L[𝕜] tangent_space I' (f x)) = mfderiv I I' f x :=
by { ext, refl }

@[simp] lemma fderiv_symm_coe (x : M) :
  ((f.fderiv x).symm : tangent_space I' (f x) →L[𝕜] tangent_space I x) =
  mfderiv I' I f.inv_fun (f x) :=
by { ext, refl }

lemma fderiv_symm_coe' {x : M'} (hx : x ∈ range f) :
  ((f.fderiv (f.inv_fun x)).symm : tangent_space I' (f (f.inv_fun x)) →L[𝕜]
    tangent_space I (f.inv_fun x)) =
  (mfderiv I' I f.inv_fun x : tangent_space I' x →L[𝕜] tangent_space I (f.inv_fun x)) :=
by rw [fderiv_symm_coe, f.right_inv hx]

open filter

lemma open_embedding : open_embedding f :=
open_embedding_of_continuous_injective_open f.continuous f.injective f.open_map

lemma inducing : inducing f := f.open_embedding.to_inducing

-- `∀ᶠ x near s, p x` means property `p` holds at every point in a neighborhood of the set `s`.
notation `∀ᶠ` binders ` near ` s `, ` r:(scoped p, filter.eventually p $ 𝓝ˢ s) := r

lemma forall_near' {P : M → Prop} {A : set M'} (h : ∀ᶠ m near f ⁻¹' A, P m) :
  ∀ᶠ m' near A ∩ range f, ∀ m, m' = f m → P m :=
begin
  rw eventually_nhds_set_iff at h ⊢,
  rintros _ ⟨hfm₀, m₀, rfl⟩,
  have : ∀ U ∈ 𝓝 m₀, ∀ᶠ m' in 𝓝 (f m₀), m' ∈ f '' U,
  { intros U U_in,
    exact f.open_map.image_mem_nhds U_in },
  apply (this _ $ h m₀ hfm₀).mono,
  rintros _ ⟨m₀, hm₀, hm₀'⟩ m₁ rfl,
  rwa ← f.injective hm₀'
end

lemma eventually_nhds_set_mono {α : Type*} [topological_space α] {s t : set α} {P : α → Prop}
  (h : ∀ᶠ x near t, P x) (h' : s ⊆ t) : ∀ᶠ x near s, P x :=
h.filter_mono (nhds_set_mono h')

-- TODO: optimize this proof which is probably more complicated than it needs to be
lemma forall_near [t2_space M'] {P : M → Prop} {P' : M' → Prop} {K : set M} (hK : is_compact K)
  {A : set M'} (hP : ∀ᶠ m near f ⁻¹' A, P m) (hP' : ∀ᶠ m' near A, m' ∉ f '' K → P' m')
  (hPP' : ∀ m, P m → P' (f m)) :
  ∀ᶠ m' near A, P' m' :=
begin
  rw show A = (A ∩ range f) ∪ (A ∩ (range f)ᶜ), by simp,
  apply filter.eventually.union,
  { have : ∀ᶠ m' near A ∩ range f, m' ∈ range f,
      from f.is_open_range.forall_near_mem_of_subset (inter_subset_right _ _),
    apply (this.and $ f.forall_near' hP).mono,
    rintros _ ⟨⟨m, rfl⟩, hm⟩,
    exact hPP' _ (hm _ rfl) },
  { have op : is_open (f '' K)ᶜ,
    { rw is_open_compl_iff,
      exact (hK.image f.continuous).is_closed },
    have : A ∩ (range f)ᶜ ⊆ A ∩ (f '' K)ᶜ,
    { exact inter_subset_inter_right _ (compl_subset_compl.mpr (image_subset_range f K)) },
    apply eventually_nhds_set_mono _ this,
    rw eventually_nhds_set_iff at hP' ⊢,
    rintros x ⟨hx, hx'⟩,
    have hx' : ∀ᶠ y in 𝓝 x, y ∈ (f '' K)ᶜ,
      from is_open_iff_eventually.mp op x hx',
    apply ((hP' x hx).and hx').mono,
    rintros y ⟨hy, hy'⟩,
    exact hy hy' },
end

variables (I M)

/-- The identity map is a smooth open embedding. -/
@[simps] def id : open_smooth_embedding I M I M :=
{ to_fun := id,
  inv_fun := id,
  left_inv' := λ x, rfl,
  open_map := is_open_map.id,
  smooth_to := smooth_id,
  smooth_inv := smooth_on_id }

variables {I M I' M'}

@[simps] def comp
  {E'' : Type*} [normed_add_comm_group E''] [normed_space 𝕜 E'']
  {H'' : Type*} [topological_space H'']
  {I'' : model_with_corners 𝕜 E'' H''}
  {M'' : Type*} [topological_space M''] [charted_space H'' M''] [smooth_manifold_with_corners I'' M'']
  (g : open_smooth_embedding I' M' I'' M'') (f : open_smooth_embedding I M I' M') :
  open_smooth_embedding I M I'' M'' :=
{ to_fun := g ∘ f,
  inv_fun := f.inv_fun ∘ g.inv_fun,
  left_inv' := λ x, by simp only [function.comp_app, left_inv],
  open_map := g.open_map.comp f.open_map,
  smooth_to := g.smooth_to.comp f.smooth_to,
  smooth_inv := (f.smooth_inv.comp' g.smooth_inv).mono
  begin
    change range (g ∘ f) ⊆ range g ∩ g.inv_fun ⁻¹' range f,
    refine subset_inter_iff.mpr ⟨range_comp_subset_range f g, _⟩,
    rintros x' ⟨x, rfl⟩,
    exact ⟨x, by simp only [left_inv]⟩,
  end, }

/-
Note: the only indended use of the following definition is the case where `f = (id : ℝ → ℝ)`,
but the proof shouldn't be hard anyway.
-/
@[simps] def prod
  {F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]
  {G : Type*} [topological_space G]
  {J : model_with_corners 𝕜 F G}
  {N : Type*} [topological_space N] [charted_space G N] [smooth_manifold_with_corners J N]
  {F' : Type*} [normed_add_comm_group F'] [normed_space 𝕜 F']
  {G' : Type*} [topological_space G']
  {J' : model_with_corners 𝕜 F' G'}
  {N' : Type*} [topological_space N'] [charted_space G' N'] [smooth_manifold_with_corners J' N']
  (f : open_smooth_embedding I M J N)
  (f' : open_smooth_embedding I' M' J' N') :
  open_smooth_embedding (I.prod I') (M × M') (J.prod J') (N × N') :=
{ to_fun := prod.map f f',
  inv_fun := prod.map f.inv_fun f'.inv_fun,
  left_inv' := sorry,
  open_map := sorry,
  smooth_to := sorry,
  smooth_inv := sorry }

end open_smooth_embedding

namespace continuous_linear_equiv

variables (e : E ≃L[𝕜] E') [complete_space E] [complete_space E']

@[simp] lemma is_open_map : is_open_map e := (e : E →L[𝕜] E').is_open_map e.surjective

@[simps] def to_open_smooth_embedding :
  open_smooth_embedding 𝓘(𝕜, E) E 𝓘(𝕜, E') E' :=
{ to_fun := e,
  inv_fun := e.symm,
  left_inv' := e.symm_apply_apply,
  open_map := e.is_open_map,
  smooth_to := (e : E →L[𝕜] E').cont_mdiff,
  smooth_inv := (e.symm : E' →L[𝕜] E).cont_mdiff.cont_mdiff_on }

end continuous_linear_equiv

end general

section without_boundary

open metric (hiding mem_nhds_iff) function

universe u

section general_nonsense

variables {𝕜 E H M : Type*} [nontrivially_normed_field 𝕜]
  [normed_add_comm_group E] [normed_space 𝕜 E]
  [topological_space H] {I : model_with_corners 𝕜 E H}
  [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
  {x : M} {n : ℕ∞}

lemma ext_chart_at_target_eq_image_chart_target :
  (ext_chart_at I x).target = I '' (chart_at H x).target :=
begin
  erw [(chart_at H x).to_local_equiv.trans_target'' I.to_local_equiv, I.source_eq, univ_inter],
  refl,
end

@[simp] lemma model_with_corners_self.ext_chart_at {e : E} :
  ext_chart_at 𝓘(𝕜, E) e = local_equiv.refl E :=
by simp

lemma cont_mdiff_on_ext_chart_symm :
  cont_mdiff_on 𝓘(𝕜, E) I n (ext_chart_at I x).symm (ext_chart_at I x).target :=
begin
  -- TODO: find a sane proof
  have hs : (ext_chart_at I x).target ⊆ (chart_at E (ext_chart_at I x x)).source, { simp, },
  have h2s : maps_to (ext_chart_at I x).symm (ext_chart_at I x).target (chart_at H x).source,
  { rw ← ext_chart_at_source I, exact (ext_chart_at I x).symm_maps_to, },
  refine (cont_mdiff_on_iff_of_subset_source hs h2s).mpr ⟨_, _⟩,
  { rw ext_chart_at_target_eq_image_chart_target,
    apply (chart_at H x).symm.continuous_to_fun.comp I.continuous_inv_fun.continuous_on,
    simpa using maps_to_id _, },
  { simp only [model_with_corners_self.ext_chart_at, local_equiv.refl_symm, local_equiv.refl_coe,
      comp.right_id, id.def, image_id'],
    exact (cont_diff_on_congr (λ y hy, (ext_chart_at I x).right_inv hy)).mpr cont_diff_on_id, },
end

end general_nonsense

variables
  {F H : Type*} (M : Type u)
  [normed_add_comm_group F] [normed_space ℝ F]
  [topological_space H] [topological_space M] [charted_space H M]
  [t2_space M] [locally_compact_space M] [sigma_compact_space M]
  (IF : model_with_corners ℝ F H) [smooth_manifold_with_corners IF M]

/- Clearly should be generalised. Maybe what we really want is a theory of local diffeomorphisms.

Note that the input `f` is morally an `open_smooth_embedding` but stated in terms of `cont_diff`
instead of `cont_mdiff`. This is more convenient for our purposes. -/
def open_smooth_emb_of_diffeo_subset_chart_target (x : M) {f : local_homeomorph F F}
  (hf₁ : f.source = univ)
  (hf₂ : cont_diff ℝ ∞ f)
  (hf₃ : cont_diff_on ℝ ∞ f.symm f.target)
  (hf₄ : range f ⊆ IF '' (chart_at H x).target) :
  open_smooth_embedding 𝓘(ℝ, F) F IF M :=
{ to_fun := (ext_chart_at IF x).symm ∘ f,
  inv_fun := f.inv_fun ∘ (ext_chart_at IF x),
  left_inv' := λ y,
  begin
    obtain ⟨z, hz, hz'⟩ := hf₄ (mem_range_self y),
    have aux : f.symm (IF z) = y, { rw hz', exact f.left_inv (hf₁.symm ▸ mem_univ _), },
    simp only [← hz', (chart_at H x).right_inv hz, aux, ext_chart_at, local_equiv.coe_trans,
      local_homeomorph.inv_fun_eq_coe, model_with_corners.to_local_equiv_coe,
      local_homeomorph.coe_coe, local_equiv.coe_trans_symm, local_homeomorph.coe_coe_symm,
      model_with_corners.left_inv, model_with_corners.to_local_equiv_coe_symm, comp_app, aux],
  end,
  open_map := λ u hu,
  begin
    have aux : is_open (f '' u) := f.image_open_of_open hu (hf₁.symm ▸ subset_univ u),
    convert ext_chart_preimage_open_of_open' IF x aux,
    rw image_comp,
    refine (ext_chart_at IF x).symm_image_eq_source_inter_preimage
      ((image_subset_range f u).trans _),
    rw ext_chart_at_target_eq_image_chart_target,
    exact hf₄,
  end,
  smooth_to :=
  begin
    refine cont_mdiff_on_ext_chart_symm.comp_cont_mdiff hf₂.cont_mdiff (λ y, _),
    rw ext_chart_at_target_eq_image_chart_target,
    exact hf₄ (mem_range_self y),
  end,
  smooth_inv :=
  begin
    rw ← ext_chart_at_target_eq_image_chart_target at hf₄,
    have hf' : range ((ext_chart_at IF x).symm ∘ f) ⊆ (ext_chart_at IF x) ⁻¹' f.target,
    { rw [range_comp, ← image_subset_iff, ← f.image_source_eq_target, hf₁, image_univ],
      exact (local_equiv.image_symm_image_of_subset_target _ hf₄).subset, },
    have hf'' : range ((ext_chart_at IF x).symm ∘ f) ⊆ (chart_at H x).source,
    { rw [← ext_chart_at_source IF, range_comp, ← local_equiv.symm_image_target_eq_source],
      exact (monotone_image hf₄).trans subset.rfl, },
    exact hf₃.cont_mdiff_on.comp (cont_mdiff_on_ext_chart_at.mono hf'') hf',
  end}

@[simp] lemma coe_open_smooth_emb_of_diffeo_subset_chart_target
  (x : M) {f : local_homeomorph F F}
  (hf₁ : f.source = univ)
  (hf₂ : cont_diff ℝ ∞ f)
  (hf₃ : cont_diff_on ℝ ∞ f.symm f.target)
  (hf₄ : range f ⊆ IF '' (chart_at H x).target) :
  (open_smooth_emb_of_diffeo_subset_chart_target M IF x hf₁ hf₂ hf₃ hf₄ : F → M) =
  (ext_chart_at IF x).symm ∘ f :=
by simp [open_smooth_emb_of_diffeo_subset_chart_target]

lemma range_open_smooth_emb_of_diffeo_subset_chart_target
  (x : M) {f : local_homeomorph F F}
  (hf₁ : f.source = univ)
  (hf₂ : cont_diff ℝ ∞ f)
  (hf₃ : cont_diff_on ℝ ∞ f.symm f.target)
  (hf₄ : range f ⊆ IF '' (chart_at H x).target) :
  range (open_smooth_emb_of_diffeo_subset_chart_target M IF x hf₁ hf₂ hf₃ hf₄) =
  (ext_chart_at IF x).symm '' (range f) :=
by rw [coe_open_smooth_emb_of_diffeo_subset_chart_target, range_comp]

variables {M} (F) [model_with_corners.boundaryless IF] [finite_dimensional ℝ F]

lemma nice_atlas'
  {ι : Type*} {s : ι → set M} (s_op : ∀ j, is_open $ s j) (cov : (⋃ j, s j) = univ)
  (U : set F) (hU₁ : (0 : F) ∈ U) (hU₂ : is_open U) :
  ∃ (ι' : Type u) (t : set ι') (φ : t → open_smooth_embedding 𝓘(ℝ, F) F IF M),
  t.countable ∧
  (∀ i, ∃ j, range (φ i) ⊆ s j) ∧
  locally_finite (λ i, range (φ i)) ∧
  (⋃ i, φ i '' U) = univ :=
begin
  let W : M → ℝ → set M := λ x r,
    (ext_chart_at IF x).symm ∘ diffeomorph_to_nhd (ext_chart_at IF x x) r '' U,
  let B : M → ℝ → set M := charted_space.ball IF,
  let p : M → ℝ → Prop :=
    λ x r, 0 < r ∧ ball (ext_chart_at IF x x) r ⊆ (ext_chart_at IF x).target ∧ ∃ j, B x r ⊆ s j,
  have hW₀ : ∀ x r, p x r → x ∈ W x r := λ x r h, ⟨0, hU₁, by simp [h.1]⟩,
  have hW₁ : ∀ x r, p x r → is_open (W x r),
  { rintros x r ⟨h₁, h₂, -, -⟩,
    simp only [W],
    rw image_comp,
    let V := diffeomorph_to_nhd (ext_chart_at IF x x) r '' U,
    change is_open ((ext_chart_at IF x).symm '' V),
    have hV₁ : is_open V := ((diffeomorph_to_nhd
      (ext_chart_at IF x x) r).is_open_image_iff_of_subset_source (by simp)).mp hU₂,
    have hV₂ : V ⊆ (ext_chart_at IF x).target :=
      subset.trans ((image_subset_range _ _).trans (by simp [h₁])) h₂,
    rw (ext_chart_at IF x).symm_image_eq_source_inter_preimage hV₂,
    exact ext_chart_preimage_open_of_open' IF x hV₁, },
  have hB : ∀ x, (𝓝 x).has_basis (p x) (B x) :=
    λ x, charted_space.nhds_has_basis_balls_of_open_cov IF x s_op cov,
  have hp : ∀ i r, p i r → 0 < r := λ i r h, h.1,
  obtain ⟨t, ht₁, ht₂, ht₃, ht₄⟩ :=
    exists_countable_locally_finite_cover surjective_id hp hW₀ hW₁ hB,
  let g : M × ℝ → local_homeomorph F F := λ z, diffeomorph_to_nhd (ext_chart_at IF z.1 z.1) z.2,
  have hg₁ : ∀ z, (g z).source = univ, { simp, },
  have hg₂ : ∀ z, cont_diff ℝ ∞ (g z), { simp, },
  have hg₃ : ∀ z, cont_diff_on ℝ ∞ (g z).symm (g z).target, { simp, },
  refine ⟨M × ℝ, t,
    λ z, open_smooth_emb_of_diffeo_subset_chart_target M IF z.1.1 (hg₁ z.1) (hg₂ z.1) (hg₃ z.1) _,
    ht₁, λ z, _, _, _⟩,
  { obtain ⟨⟨x, r⟩, hxr⟩ := z,
    obtain ⟨hr : 0 < r, hr' : ball (ext_chart_at IF x x) r ⊆ _, -⟩ := ht₂ _ hxr,
    rw ← ext_chart_at_target_eq_image_chart_target,
    exact (range_diffeomorph_to_nhd_subset_ball (ext_chart_at IF x x) hr).trans hr', },
  { obtain ⟨⟨x, r⟩, hxr⟩ := z,
    obtain ⟨hr : 0 < r, -, j, hj : B x r ⊆ s j⟩ := ht₂ _ hxr,
    simp_rw range_open_smooth_emb_of_diffeo_subset_chart_target,
    exact ⟨j, subset_trans (monotone_image (range_diffeomorph_to_nhd_subset_ball _ hr)) hj⟩, },
  { simp_rw range_open_smooth_emb_of_diffeo_subset_chart_target,
    refine ht₄.subset _,
    rintros ⟨⟨x, r⟩, hxr⟩,
    obtain ⟨hr : 0 < r, -, -⟩ := ht₂ _ hxr,
    exact monotone_image (range_diffeomorph_to_nhd_subset_ball _ hr), },
  { simpa only [Union_coe_set] using ht₃, },
end

variables [nonempty M]

lemma nice_atlas {ι : Type*} {s : ι → set M} (s_op : ∀ j, is_open $ s j) (cov : (⋃ j, s j) = univ) :
  ∃ n, ∃ φ : index_type n → open_smooth_embedding 𝓘(ℝ, F) F IF M,
  (∀ i, ∃ j, range (φ i) ⊆ s j) ∧
  locally_finite (λ i, range (φ i)) ∧
  (⋃ i, φ i '' ball 0 1) = univ :=
begin
  obtain ⟨ι', t, φ, h₁, h₂, h₃, h₄⟩ := nice_atlas' F IF s_op cov (ball 0 1) (by simp) is_open_ball,
  have htne : t.nonempty,
  { by_contra contra,
    simp only [not_nonempty_iff_eq_empty.mp contra, Union_false, Union_coe_set, Union_empty,
      @eq_comm _ _ univ, univ_eq_empty_iff] at h₄,
    exact not_is_empty_of_nonempty M h₄, },
  obtain ⟨n, ⟨fn⟩⟩ := (set.countable_iff_exists_nonempty_index_type_equiv htne).mp h₁,
  refine ⟨n, φ ∘ fn, λ i, h₂ (fn i), h₃.comp_injective fn.injective, _⟩,
  rwa fn.surjective.Union_comp (λ i, φ i '' ball 0 1),
end

end without_boundary

namespace open_smooth_embedding

section updating

variables {𝕜 EX EM EY EN X M Y N : Type*} [nontrivially_normed_field 𝕜]
  [normed_add_comm_group EX] [normed_space 𝕜 EX]
  [normed_add_comm_group EM] [normed_space 𝕜 EM]
  [normed_add_comm_group EY] [normed_space 𝕜 EY]
  [normed_add_comm_group EN] [normed_space 𝕜 EN]
  {HX : Type*} [topological_space HX] {IX : model_with_corners 𝕜 EX HX}
  {HY : Type*} [topological_space HY] {IY : model_with_corners 𝕜 EY HY}
  {HM : Type*} [topological_space HM] {IM : model_with_corners 𝕜 EM HM}
  {HN : Type*} [topological_space HN] {IN : model_with_corners 𝕜 EN HN}
  [topological_space X] [charted_space HX X] [smooth_manifold_with_corners IX X]
  [topological_space M] [charted_space HM M] [smooth_manifold_with_corners IM M]

section non_metric
variables
  [topological_space Y]      [charted_space HY Y] [smooth_manifold_with_corners IY Y]
  [topological_space N]      [charted_space HN N] [smooth_manifold_with_corners IN N]
  (φ : open_smooth_embedding IX X IM M)
  (ψ : open_smooth_embedding IY Y IN N)
  (f : M → N) (g : X → Y)

section
local attribute [instance] classical.dec
/-- This is definition `def:update` in the blueprint. -/
def update (m : M) : N := if m ∈ range φ then ψ (g (φ.inv_fun m)) else f m
end

@[simp] lemma update_of_nmem_range {m : M} (hm : m ∉ range φ) :
  update φ ψ f g m = f m :=
by simp [update, hm]

@[simp] lemma update_of_mem_range {m : M} (hm : m ∈ range φ) :
  update φ ψ f g m = ψ (g (φ.inv_fun m)) :=
by simp [update, hm]

@[simp] lemma update_apply_embedding (x : X) :
  update φ ψ f g (φ x) = ψ (g x) :=
by simp [update]

/- This small auxiliry result is used in the next two lemmas. -/
lemma nice_update_of_eq_outside_compact_aux {K : set X} (g : X → Y)
  (hg : ∀ (x : X), x ∉ K → f (φ x) = ψ (g x)) {m : M} (hm : m ∉ φ '' K) :
  φ.update ψ f g m = f m :=
begin
  by_cases hm' : m ∈ range φ,
  { obtain ⟨x, rfl⟩ := hm',
    replace hm : x ∉ K, { contrapose! hm, exact mem_image_of_mem φ hm, },
    simp [hg x hm] },
  { simp [hm'] }
end


/- FIXME: the blueprint statement corresponding to the next two lemmas has very confusing
quantifiers status.
-/

/-
In the next lemma, it is better to assume directly that `φ '' K` is closed. This
will hold both when `K` is compact and when `φ = Id.prod ψ` and `K = ℝ × H` with `H` compact.
-/

/-- This is half of lemma `lem:updating` in the blueprint. -/
lemma smooth_update [t2_space M]
  {K : set X} (hK : is_compact K) (hf : smooth IM IN f) (hg : smooth IX IY g)
  (hg' : ∀ x, x ∉ K → f (φ x) = ψ (g x)) : smooth IM IN (update φ ψ f g) :=
begin
  have hK' : ∀ m ∉ φ '' K, update φ ψ f g m = f m := λ m hm, by
    from nice_update_of_eq_outside_compact_aux φ ψ f g hg' hm,
  refine cont_mdiff_of_locally_cont_mdiff_on (λ m, _),
  let U := range φ,
  let V := (φ '' K)ᶜ,
  have h₂ : is_open V := is_open_compl_iff.mpr (hK.image φ.continuous).is_closed,
  have h₃ : V ∪ U = univ,
  { rw [← compl_subset_iff_union, compl_compl], exact image_subset_range φ K, },
  have h₄ : ∀ m ∈ U, update φ ψ f g m = (ψ ∘ g ∘ φ.inv_fun) m := λ m hm, by simp [hm],
  by_cases hm : m ∈ U,
  { exact ⟨U, φ.is_open_range, hm, (cont_mdiff_on_congr h₄).mpr $
      ψ.smooth_to.comp_cont_mdiff_on $ hg.comp_cont_mdiff_on φ.smooth_inv⟩, },
  { refine ⟨V, h₂, _, (cont_mdiff_on_congr hK').mpr hf.cont_mdiff_on⟩,
    simpa [hm] using set.ext_iff.mp h₃ m }
end

end non_metric

section metric
variables
  [metric_space Y]      [charted_space HY Y] [smooth_manifold_with_corners IY Y]
  [metric_space N]      [charted_space HN N] [smooth_manifold_with_corners IN N]
  (φ : open_smooth_embedding IX X IM M)
  (ψ : open_smooth_embedding IY Y IN N)
  (f : M → N) (g : X → Y)
  [decidable_pred (∈ range φ)]


/-
The next lemma probably isn't quite enough. We want to apply it to
`K = [0, 1] × Ball 0 2` but the condition `f (φ x) = ψ (g x)` doesn't hold on
`{1} × Ball 0 2`. However we also don't care about what happens when `t` isn't in `[0, 1]`
so we should probably weaken the conclusion.
We could even use a reflection trick to reduce to a case where `K = [0, 2] × Ball 0 2`
and the whole boundary is ok.
-/

/-- This is half of lemma `lem:updating` in the blueprint. -/
lemma dist_update [proper_space Y] {K : set X} (hK : is_compact K) (hf : smooth IM IN f)
  (hf' : f '' range φ ⊆ range ψ) {ε : M → ℝ} (hε : ∀ m, 0 < ε m) (hε' : continuous ε) :
  ∃ (η > (0 : ℝ)), ∀ g : X → Y,
    (∀ x, x ∉ K → f (φ x) = ψ (g x)) →
    (∀ x, dist (g x) (ψ.inv_fun (f (φ x))) < η) →
      ∀ m, dist (update φ ψ f g m) (f m) < ε m :=
begin
  let K₁ := metric.cthickening 1 ((ψ.inv_fun ∘ f ∘ φ) '' K),
  have hK₁ : is_compact K₁,
  { refine metric.is_compact_of_is_closed_bounded metric.is_closed_cthickening
      (metric.bounded.cthickening $ is_compact.bounded $ hK.image _),
    replace hf' : ∀ x, f (φ x) ∈ range ψ := λ x, hf' ⟨φ x, mem_range_self x, rfl⟩,
    exact ψ.smooth_inv.continuous_on.comp_continuous
      (hf.continuous.comp φ.continuous) hf', },
  have h₁ : uniform_continuous_on ψ K₁ :=
    hK₁.uniform_continuous_on_of_continuous ψ.continuous.continuous_on,
  have hεφ : ∀ x ∈ K, 0 < (ε ∘ φ) x := λ x hx, hε _,
  obtain ⟨ε₀, hε₀, hε₀'⟩ :=
    hK.exists_forall_le' (hε'.comp φ.continuous).continuous_on hεφ,
  obtain ⟨τ, hτ : 0 < τ, hτ'⟩ := metric.uniform_continuous_on_iff.mp h₁ ε₀ hε₀,
  refine ⟨min τ 1, by simp [hτ], λ g hg hη m,  _⟩,
  have hK' : ∀ m ∉ φ '' K, update φ ψ f g m = f m := λ m hm, by
    from nice_update_of_eq_outside_compact_aux φ ψ f g hg hm,
  by_cases hm : m ∈ φ '' K, swap, { simp [hK', hm, hε m], },
  obtain ⟨x, hx, rfl⟩ := hm,
  refine lt_of_lt_of_le _ (hε₀' x hx),
  simp only [update_apply_embedding],
  have h₁ : g x ∈ K₁ :=
    metric.mem_cthickening_of_dist_le _ _ _ _ ⟨x, hx, rfl⟩ (lt_min_iff.mp (hη x)).2.le,
  have h₂ : f (φ x) ∈ range ψ := hf' ⟨φ x, mem_range_self x, rfl⟩,
  rw ← ψ.right_inv h₂,
  exact hτ' _ h₁ _ (metric.self_subset_cthickening _ ⟨x, hx, rfl⟩) (lt_min_iff.mp (hη x)).1,
end
end metric

end updating

end open_smooth_embedding
