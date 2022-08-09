import geometry.manifold.cont_mdiff
import global.indexing
import to_mathlib.topology.paracompact
import to_mathlib.topology.local_homeomorph
import to_mathlib.geometry.manifold.charted_space

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
(right_inv'  : ∀{x}, x ∈ range to_fun → to_fun (inv_fun x) = x)
(open_map : is_open_map to_fun)
(smooth_to : smooth I I' to_fun)
(smooth_inv : smooth_on I' I inv_fun (range to_fun))

instance : has_coe_to_fun (open_smooth_embedding I M I' M') (λ _, M → M') :=
⟨open_smooth_embedding.to_fun⟩

namespace open_smooth_embedding

variables {I I' M M'} (f : open_smooth_embedding I M I' M')

@[simp] lemma left_inv (x : M) : f.inv_fun (f x) = x := by apply f.left_inv'

@[simp] lemma inv_fun_comp_coe : f.inv_fun ∘ f = id := funext f.left_inv

@[simp] lemma right_inv {y : M'} (hy : y ∈ range f) : f (f.inv_fun y) = y := f.right_inv' hy

lemma coe_comp_inv_fun_eventually_eq (x : M) : f ∘ f.inv_fun =ᶠ[𝓝 (f x)] id :=
filter.eventually_of_mem (f.open_map.range_mem_nhds x) $ λ y hy, f.right_inv' hy

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

end open_smooth_embedding

end general

section without_boundary

open metric (hiding mem_nhds_iff) function

universe u

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
  (M : Type u) [topological_space M] [charted_space E M] [smooth_manifold_with_corners 𝓘(𝕜, E) M]
  [t2_space M] [locally_compact_space M] [sigma_compact_space M]

/- Clearly should be generalised. Maybe what we really want is a theory of local diffeomorphisms. -/
def open_smooth_embedding_of_subset_chart_target {x : M}
  {f : open_smooth_embedding 𝓘(𝕜, E) E 𝓘(𝕜, E) E} (hf : range f ⊆ (chart_at E x).target) :
  open_smooth_embedding 𝓘(𝕜, E) E 𝓘(𝕜, E) M :=
{ to_fun := (chart_at E x).symm ∘ f,
  inv_fun := f.inv_fun ∘ (chart_at E x),
  left_inv' := λ y, by simp [hf (mem_range_self y)],
  right_inv' := by { rintros - ⟨y, rfl⟩, simp [hf (mem_range_self y)], },
  open_map := λ u hu,
  begin
    rw image_comp,
    apply local_homeomorph.image_open_of_open _ (f.open_map _ hu),
    rw ← image_univ at hf,
    exact (monotone_image (subset_univ u)).trans hf,
  end,
  smooth_to := cont_mdiff_on_chart_symm.comp_cont_mdiff f.smooth_to (range_subset_iff.mp hf),
  smooth_inv :=
  begin
    have hf' : range ((chart_at E x).symm ∘ f) ⊆ (chart_at E x) ⁻¹' range f,
    { rw [range_comp, ← image_subset_iff],
      exact (local_equiv.image_symm_image_of_subset_target _ hf).subset },
    refine f.smooth_inv.comp _ hf',
    have hf'' : range ((chart_at E x).symm ∘ f) ⊆ (chart_at E x).source,
    { rw [range_comp, ← local_equiv.symm_image_target_eq_source],
      exact (monotone_image hf).trans subset.rfl, },
    exact cont_mdiff_on_chart.mono hf'',
  end }

@[simp] lemma coe_open_smooth_embedding_of_subset_chart_target {x : M}
  {f : open_smooth_embedding 𝓘(𝕜, E) E 𝓘(𝕜, E) E} (hf : range f ⊆ (chart_at E x).target) :
  (open_smooth_embedding_of_subset_chart_target M hf : E → M) = (chart_at E x).symm ∘ f :=
rfl

variables (𝕜)

/-- Provided `0 < r`, this is a diffeomorphism from `E` onto the open ball of radius `r` in `E`
centred at a point `c` and sending `0` to `c`.

The values for `r ≤ 0` are junk. -/
def open_smooth_embedding_to_ball (c : E) (r : ℝ) :
  open_smooth_embedding 𝓘(𝕜, E) E 𝓘(𝕜, E) E :=
sorry

@[simp] lemma open_smooth_embedding_to_ball_apply_zero (c : E) {r : ℝ} (h : 0 < r) :
  open_smooth_embedding_to_ball 𝕜 c r 0 = c :=
sorry

@[simp] lemma range_open_smooth_embedding_to_ball (c : E) {r : ℝ} (h : 0 < r) :
  range (open_smooth_embedding_to_ball 𝕜 c r) = ball c r :=
sorry

variables (E) {M}

lemma nice_atlas'
  {ι : Type*} {s : ι → set M} (s_op : ∀ j, is_open $ s j) (cov : (⋃ j, s j) = univ) :
  ∃ (ι' : Type u) (t : set ι') (φ : t → open_smooth_embedding 𝓘(𝕜, E) E 𝓘(𝕜, E) M),
  t.countable ∧
  (∀ i, ∃ j, range (φ i) ⊆ s j) ∧
  locally_finite (λ i, range (φ i)) ∧
  (⋃ i, φ i '' ball 0 1) = univ :=
begin
  let W : M → ℝ → set M := λ x r,
    (chart_at E x).symm ∘ open_smooth_embedding_to_ball 𝕜 (chart_at E x x) r '' (ball 0 1),
  let B : M → ℝ → set M := charted_space.ball E,
  let p : M → ℝ → Prop :=
    λ x r, 0 < r ∧ ball (chart_at E x x) r ⊆ (chart_at E x).target ∧ ∃ j, B x r ⊆ s j,
  have hW₀ : ∀ x r, p x r → x ∈ W x r := λ x r h, ⟨0, by simp, by simp [h.1]⟩,
  have hW₁ : ∀ x r, p x r → is_open (W x r),
  { rintros x r ⟨h₁, h₂, -, -⟩,
    simp only [W],
    have aux :
      open_smooth_embedding_to_ball 𝕜 (chart_at E x x) r '' ball 0 1 ⊆ (chart_at E x).target :=
      subset.trans ((image_subset_range _ _).trans (by simp [h₁])) h₂,
    rw [image_comp, local_homeomorph.is_open_symm_image_iff_of_subset_target _ aux],
    exact open_smooth_embedding.open_map _ _ is_open_ball, },
  have hB : ∀ x, (𝓝 x).has_basis (p x) (B x) :=
    λ x, charted_space.nhds_has_basis_balls_of_open_cov E x s_op cov,
  have hp : ∀ i r, p i r → 0 < r := λ i r h, h.1,
  obtain ⟨t, ht₁, ht₂, ht₃, ht₄⟩ :=
    exists_countable_locally_finite_cover surjective_id hp hW₀ hW₁ hB,
  refine ⟨M × ℝ, t, λ z, _, ht₁, λ z, _, _, _⟩,
  { have h : range (open_smooth_embedding_to_ball 𝕜 (chart_at E z.1.1 z.1.1) z.1.2) ⊆
      (chart_at E z.1.1).target,
    { have aux : 0 < z.val.snd := hp _ _ (ht₂ _ z.2),
      simpa only [range_open_smooth_embedding_to_ball, aux] using (ht₂ _ z.2).2.1, },
    exact open_smooth_embedding_of_subset_chart_target M h, },
  { have aux : 0 < (z : M × ℝ).snd := hp _ _ (ht₂ _ z.2),
    simp only [subtype.val_eq_coe, coe_open_smooth_embedding_of_subset_chart_target],
    simp only [range_comp, range_open_smooth_embedding_to_ball, aux],
    exact (ht₂ z.1 z.2).2.2, },
  { convert ht₄,
    ext1 z,
    have aux : 0 < (z : M × ℝ).snd := hp _ _ (ht₂ _ z.2),
    simp only [subtype.val_eq_coe, coe_open_smooth_embedding_of_subset_chart_target],
    simpa only [range_comp, range_open_smooth_embedding_to_ball, aux], },
  { simpa only [Union_coe_set] using ht₃, },
end

variables [nonempty M]

lemma nice_atlas {ι : Type*} {s : ι → set M} (s_op : ∀ j, is_open $ s j) (cov : (⋃ j, s j) = univ) :
  ∃ n, ∃ φ : index_type n → open_smooth_embedding 𝓘(𝕜, E) E 𝓘(𝕜, E) M,
  (∀ i, ∃ j, range (φ i) ⊆ s j) ∧
  locally_finite (λ i, range (φ i)) ∧
  (⋃ i, φ i '' ball 0 1) = univ :=
begin
  obtain ⟨ι', t, φ, h₁, h₂, h₃, h₄⟩ := nice_atlas' 𝕜 E s_op cov,
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
