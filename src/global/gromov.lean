import global.relation

/-!
# Gromov's theorem

We prove the h-principle for open and ample first order differential relations.
-/

noncomputable theory

open set
open_locale topological_space manifold

variables
{E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
{H : Type*} [topological_space H] {I : model_with_corners ℝ E H}
{M : Type*} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
{E' : Type*} [normed_add_comm_group E'] [normed_space ℝ E']
{H' : Type*} [topological_space H'] {I' : model_with_corners ℝ E' H'}
{M' : Type*} [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M']
{EP : Type*} [normed_add_comm_group EP] [normed_space ℝ EP]
{HP : Type*} [topological_space HP] {IP : model_with_corners ℝ EP HP}
{P : Type*} [topological_space P] [charted_space HP P] [smooth_manifold_with_corners IP P]
{R : rel_mfld I M I' M'}
[finite_dimensional ℝ E] [finite_dimensional ℝ E']
[sigma_compact_space M] [sigma_compact_space M'] [t2_space M] [t2_space M']
{C₁ : set P} {C₂ : set M} {ε : M → ℝ}

/-- The non-parametric version of Gromov's theorem -/
lemma rel_mfld.ample.satisfies_h_principle (hC₁ : is_closed C₁) (hC₂ : is_closed C₂)
  (hε_pos : ∀ x, 0 < ε x) (hε_cont : continuous ε)
  (h1 : R.ample) (h2 : is_open R) :
  R.satisfies_h_principle C₂ ε :=
sorry

/-- **Gromov's Theorem** -/
theorem rel_mfld.ample.satisfies_h_principle_with (hC₁ : is_closed C₁) (hC₂ : is_closed C₂)
  (hε_pos : ∀ x, 0 < ε x) (hε_cont : continuous ε)
  (h1 : R.ample) (h2 : is_open R) :
  R.satisfies_h_principle_with IP C₁ C₂ ε :=
sorry
