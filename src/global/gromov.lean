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
{EX : Type*} [normed_add_comm_group EX] [normed_space ℝ EX]
{HX : Type*} [topological_space HX] {IX : model_with_corners ℝ EX HX}
-- note: X is a metric space
{X : Type*} [metric_space X] [charted_space HX X] [smooth_manifold_with_corners IX X]
{R : rel_mfld I M IX X}
{C₁ : set P} {C₂ : set M} {ε : M → ℝ}


/-- The non-parametric version of Gromov's theorem -/
lemma rel_mfld.ample.satisfies_h_principle (h1 : R.ample) (h2 : is_open R)
  (hC₁ : is_closed C₁) (hC₂ : is_closed C₂)
  (hε_pos : ∀ x, 0 < ε x) (hε_cont : continuous ε) :
  R.satisfies_h_principle C₂ ε :=
sorry

/-- **Gromov's Theorem** -/
theorem rel_mfld.ample.satisfies_h_principle_with (h1 : R.ample) (h2 : is_open R)
  (hC₁ : is_closed C₁) (hC₂ : is_closed C₂)
  (hε_pos : ∀ x, 0 < ε x) (hε_cont : continuous ε) :
  R.satisfies_h_principle_with IP C₁ C₂ ε :=
sorry

variables [finite_dimensional ℝ E'] [sigma_compact_space M'] [t2_space M']

include IP
/-- Gromov's Theorem without metric space assumption -/
theorem rel_mfld.ample.satisfies_h_principle_with' {R : rel_mfld I M I' M'}
  (h1 : R.ample) (h2 : is_open R) (hC₁ : is_closed C₁) (hC₂ : is_closed C₂)
  (hε_pos : ∀ x, 0 < ε x) (hε_cont : continuous ε) :
  by letI := (@topological_space.metrizable_space_metric _ _
    (manifold_with_corners.metrizable_space I' M')); exact
  R.satisfies_h_principle_with IP C₁ C₂ ε :=
begin
  haveI := (@topological_space.metrizable_space_metric _ _
    (manifold_with_corners.metrizable_space I' M')),
  apply rel_mfld.ample.satisfies_h_principle_with; assumption
end
