import geometry.manifold.cont_mdiff

noncomputable theory

open set equiv
open_locale manifold

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
variables {I I' M M'}

def fderiv (f : open_smooth_embedding I M I' M') (x : M) :
tangent_space I x ≃L[𝕜] tangent_space I' (f x) :=
{ to_fun := mfderiv I I' f x,
  map_add' := (mfderiv I I' f x).map_add,
  map_smul' := (mfderiv I I' f x).map_smul,
  inv_fun := continuous_linear_map.inverse (mfderiv I I' f x),
  left_inv := sorry,
  right_inv := sorry,
  continuous_to_fun := sorry,
  continuous_inv_fun := sorry }

end open_smooth_embedding

end general

section without_boundary

open metric

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {E : Type*} [normed_group E] [normed_space 𝕜 E]
  (M : Type*) [topological_space M] [charted_space E M] [smooth_manifold_with_corners 𝓘(𝕜, E) M]

lemma nice_atlas : ∃ φ : ℕ → open_smooth_embedding 𝓘(𝕜, E) E 𝓘(𝕜, E) M,
  (⋃ n, (φ n) '' (ball 0 1)) = univ :=
begin

  sorry
end

end without_boundary
