import geometry.manifold.instances.sphere

import global.gromov

noncomputable theory

open metric finite_dimensional set function
open_locale manifold

section general

variables
{E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
{H : Type*} [topological_space H] (I : model_with_corners ℝ E H)
{M : Type*} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]

{E' : Type*} [normed_add_comm_group E'] [normed_space ℝ E']
{H' : Type*} [topological_space H'] (I' : model_with_corners ℝ E' H')
{M' : Type*} [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M']

{F : Type*} [normed_add_comm_group F] [normed_space ℝ F]
{G : Type*} [topological_space G] (J : model_with_corners ℝ F G)
(N : Type*) [topological_space N] [charted_space G N] [smooth_manifold_with_corners J N]

local notation `TM` := tangent_space I
local notation `TM'` := tangent_space I'

/-- A map between manifolds is an immersion if it is differentiable and its differential at
any point is injective. Note the formalized definition doesn't require differentiability.
If `f` is not differentiable at `m` then, by definition, `mfderiv I I' f m` is zero, which
is not injective unless the source dimension is zero, which implies differentiability. -/
def immersion (f : M → M') : Prop := ∀ m, injective (mfderiv I I' f m)

variables (M M')

/-- The relation of immersions for maps between two manifolds. -/
def immersion_rel : rel_mfld I M I' M' := {σ | injective σ.2}

@[simp] lemma immersion_rel_preslice_eq {m : M} {m' : M'} {p : dual_pair' $ tangent_space I m}
  {φ : tangent_space I m →L[ℝ] tangent_space I' m'} (hφ : injective φ) :
  (immersion_rel I M I' M').preslice ⟨(m, m'), φ⟩ p = (p.π.ker.map φ)ᶜ :=
set.ext_iff.mpr $ λ w, p.injective_update_iff hφ

variables {M M'}

lemma immersion_iff_one_jet (f : M → M') :
  immersion I I' f ↔ ∀ m, one_jet_ext I I' f m ∈ immersion_rel I M I' M' :=
by simp [immersion, one_jet_ext, immersion_rel]

variables [finite_dimensional ℝ E] [finite_dimensional ℝ E']

lemma immersion_rel_ample (h : finrank ℝ E < finrank ℝ E') :
  (immersion_rel I M I' M').ample :=
begin
  rintros ⟨⟨m, m'⟩, φ : tangent_space I m →L[ℝ] tangent_space I' m'⟩
          (p : dual_pair' (tangent_space I m)) (hφ : injective φ),
  have aux : ((immersion_rel I M I' M').slice ⟨(m, m'), φ⟩ p) =
             (immersion_rel I M I' M').preslice ⟨(m, m'), φ⟩ p,
  { sorry, }, -- Easy (see proof of `ample_of_two_le_codim`) but annoying that necessary
  rw [aux,  immersion_rel_preslice_eq I M I' M' hφ],
  apply ample_of_two_le_codim,
  haveI : finite_dimensional ℝ (tangent_space I m), { sorry, }, -- trivial
  haveI : finite_dimensional ℝ (tangent_space I' m'), { sorry, }, -- trivial
  replace h : finrank ℝ (tangent_space I m) < finrank ℝ (tangent_space I' m'), { sorry, }, -- trivial
  suffices : 2 ≤ finrank ℝ (tangent_space I' m' ⧸ p.π.ker.map φ.to_linear_map),
  { rw ← finrank_eq_dim,
    exact_mod_cast this },
  have aux := submodule.finrank_quotient_add_finrank (p.π.ker.map φ.to_linear_map),
  apply le_of_add_le_add_right,
  rw aux,
  have := calc finrank ℝ (p.π.ker.map φ.to_linear_map)
         ≤ finrank ℝ p.π.ker : finrank_map_le ℝ φ.to_linear_map p.π.ker
    ...  < finrank ℝ (tangent_space I m) : submodule.finrank_lt (le_top.lt_of_ne p.ker_pi_ne_top),
  linarith,
end

-- the following needs updating after relativizing
-- /-- parametric h-principle for immersions. -/
-- theorem immersion_rel_satisfies_h_principle_with (h : finrank ℝ E < finrank ℝ E') :
--   (immersion_rel I M I' M').satisfies_h_principle_with J N :=
-- begin
--   apply (immersion_rel_ample I I' h).satisfies_h_principle_with J N,
--   have : is_open {L : E →L[ℝ] E' | injective L} := continuous_linear_map.is_open_injective,
--   sorry
-- end

end general

section sphere_eversion

variables {E : Type*} [inner_product_space ℝ E] {n : ℕ} [fact (finrank ℝ E = 3)]

/- Maybe the next two lemmas won't be used directly, but they should be done first as
sanity checks. -/

lemma immersion_inclusion_sphere : immersion (𝓡 2) 𝓘(ℝ, E) (λ x : sphere (0 : E) 1, (x : E)) :=
sorry

lemma immersion_antipodal_sphere : immersion (𝓡 2) 𝓘(ℝ, E) (λ x : sphere (0 : E) 1, -(x : E)) :=
sorry

/- TODO: Next step is to define the homotopy of formal immersions from the inclusion
to the antipodal map. -/

theorem sphere_eversion : ∃ f : ℝ → sphere (0 : E) 1 → E,
  (cont_mdiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E) ∞ (uncurry f)) ∧
  (f 0 = λ x, x) ∧
  (f 1 = λ x, -x) ∧
  ∀ t, immersion (𝓡 2) 𝓘(ℝ, E) (f t) :=
sorry

end sphere_eversion
