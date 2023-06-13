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

variables {I I'}

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


end smooth_manifold_with_corners
