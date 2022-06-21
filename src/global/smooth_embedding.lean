import geometry.manifold.cont_mdiff
import global.indexing
import to_mathlib.topology.maps

noncomputable theory

open set equiv
open_locale manifold topological_space

section general
variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {E : Type*} [normed_group E] [normed_space 𝕜 E]
  {H : Type*} [topological_space H]
  (I : model_with_corners 𝕜 E H)
  (M : Type*) [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
  {E' : Type*} [normed_group E'] [normed_space 𝕜 E']
  {H' : Type*} [topological_space H']
  (I' : model_with_corners 𝕜 E' H')
  (M' : Type*) [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M']

structure open_smooth_embedding  :=
(to_fun : M → M')
(inv_fun : M' → M)
(left_inv'   : ∀{x}, inv_fun (to_fun x) = x)
(right_inv'  : ∀{x}, x ∈ range to_fun → to_fun (inv_fun x) = x)
(open_map : is_open_map to_fun)
(diff_to : cont_mdiff I I' ⊤ to_fun)
(diff_inv : cont_mdiff_on I' I ⊤ inv_fun (range to_fun))

instance : has_coe_to_fun (open_smooth_embedding I M I' M') (λ _, M → M') :=
⟨open_smooth_embedding.to_fun⟩

namespace open_smooth_embedding

variables {I I' M M'} (f : open_smooth_embedding I M I' M')

@[simp] lemma left_inv (x : M) : f.inv_fun (f x) = x := by erw f.left_inv'

@[simp] lemma inv_fun_comp_coe : f.inv_fun ∘ f = id := by { ext, simp, }

lemma coe_comp_inv_fun_eventually_eq (x : M) : f ∘ f.inv_fun =ᶠ[𝓝 (f x)] id :=
filter.eventually_of_mem (f.open_map.range_mem_nhds x) $ λ y hy, f.right_inv' hy

/- Note that we are slightly abusing the fact that `tangent_space I x` and
`tangent_space I (f.inv_fun (f x))` are both definitionally `E` below. -/
def fderiv (x : M) : tangent_space I x ≃L[𝕜] tangent_space I' (f x) :=
have h₁ : mdifferentiable_at I' I f.inv_fun (f x) := ((f.diff_inv (f x) (mem_range_self x)
  ).mdifferentiable_within_at le_top).mdifferentiable_at (f.open_map.range_mem_nhds x),
have h₂ : mdifferentiable_at I I' f x := f.diff_to.mdifferentiable le_top _,
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

end open_smooth_embedding

end general

section without_boundary

open metric function

/-- We should be able to use this to deduce `nice_atlas`, using `B`, `p`, `c` to represent images of
Euclidean balls under coordinate charts which also lie in the supplied open cover `s`.

NB: We could generalise and replace `ι × ℝ` with a dependent family of types somewhat similar to
but it doesn't seem worth it. -/
lemma nice_atlas_aux {ι X : Type*} [topological_space X] [sigma_compact_space X]
  {B : ι → ℝ → set X} {p : ι → ℝ → Prop} {c : ι → X}
  (hB₀ : ∀ i r, is_open (B i r))
  (hB₁ : ∀ i, (𝓝 (c i)).has_basis (p i) (B i))
  (hB₂ : ∀ i, monotone (B i))
  (hp : ∀ i r₁ r₂, r₁ ≤ r₂ → p i r₂ → p i r₁)
  (hc : surjective c) :
  ∃ (s : set (ι × ℝ)),
    countable s ∧
    ∀ z ∈ s, ↿p z ∧
    (⋃ z ∈ s, ↿B z) = univ ∧
    locally_finite (λ (z : s), B (z : ι × ℝ).fst (2 • (z : ι × ℝ).snd)) :=
begin
  /-
  1. Take a compact exhaustion `Kᵢ`.
  2. Define countable family of compact sets `Cᵢ := Kᵢ₊₂ \ (Kᵢ₊₁)ᵒ` with open neighbourhoods
     `Uᵢ := (Kᵢ₊₃)ᵒ \ Kᵢ`.
  3. For each `i`, cover `Cᵢ` by elements of `B`, satisfying `p`, such that corresponding doubled
     radius elements still contained in `Uᵢ`.
  4. Let `s` be union over `i` of finite subcovers of sets in step 3.
  5. Required properties obvious. Note locally finite follows since the enclosing `Uᵢ`, `Uⱼ` are
     disjoint if `|i - j|  4`.
  -/
  sorry,
end

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {E : Type*} [normed_group E] [normed_space 𝕜 E]
  (M : Type*) [topological_space M] [charted_space E M] [smooth_manifold_with_corners 𝓘(𝕜, E) M]
  [sigma_compact_space M]

lemma nice_atlas {ι : Type*} {s : ι → set M} (s_op : ∀ j, is_open $ s j) (cov : (⋃ j, s j) = univ) :
  ∃ n, ∃ φ : index_type n → open_smooth_embedding 𝓘(𝕜, E) E 𝓘(𝕜, E) M,
  (⋃ i, (φ i) '' (ball 0 1)) = univ ∧ locally_finite (λ i, range $ φ i) ∧
  ∀ i, ∃ j, range (φ i) ⊆ s j :=
sorry

end without_boundary
