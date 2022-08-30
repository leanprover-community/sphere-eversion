import global.relation
import global.localisation_data

/-!
# Gromov's theorem

We prove the h-principle for open and ample first order differential relations.
-/

noncomputable theory

open set
open_locale topological_space manifold

variables
{E : Type*} [normed_add_comm_group E] [normed_space ℝ E] [finite_dimensional ℝ E]
{H : Type*} [topological_space H] {I : model_with_corners ℝ E H} [model_with_corners.boundaryless I]
{M : Type*} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
[t2_space M]
[locally_compact_space M] -- investigate how to deduce this from finite-dimensional
[nonempty M] -- investigate how to remove this
[sigma_compact_space M]

{EX : Type*} [normed_add_comm_group EX] [normed_space ℝ EX]  [finite_dimensional ℝ EX]
{HX : Type*} [topological_space HX] {IX : model_with_corners ℝ EX HX} [model_with_corners.boundaryless IX]
-- note: X is a metric space
{X : Type*} [metric_space X] [charted_space HX X] [smooth_manifold_with_corners IX X]
[locally_compact_space X] -- investigate how to deduce this from finite-dimensional
[sigma_compact_space X]
[nonempty X] -- investigate how to remove this

{R : rel_mfld I M IX X}
{C₂ : set M} {ε : M → ℝ}

/-- The non-parametric version of Gromov's theorem -/
lemma rel_mfld.ample.satisfies_h_principle (h1 : R.ample) (h2 : is_open R)
  (hC₂ : is_closed C₂)
  (hε_pos : ∀ x, 0 < ε x) (hε_cont : continuous ε) :
  R.satisfies_h_principle C₂ ε :=
begin
  intros 𝓕 h𝓕,
  have cont : continuous 𝓕.bs,
  {
    sorry },
  let L : localisation_data I IX 𝓕.bs := std_localisation_data E I EX IX cont,
  rcases localisation_stability E I EX IX cont L with ⟨ε, ε_pos, ε_cont, hε⟩,
  have := L.h₄, -- This is where we need to apply the lemma that Yury weakened
  sorry
end

variables
{EP : Type*} [normed_add_comm_group EP] [normed_space ℝ EP]  [finite_dimensional ℝ EP]
{HP : Type*} [topological_space HP] {IP : model_with_corners ℝ EP HP} [model_with_corners.boundaryless IP]
{P : Type*} [topological_space P] [charted_space HP P] [smooth_manifold_with_corners IP P]
[locally_compact_space P] -- investigate how to deduce this from finite-dimensional
[sigma_compact_space P]
[t2_space P]
[nonempty P] -- investigate how to remove this
{C₁ : set P}

/-- **Gromov's Theorem** -/
theorem rel_mfld.ample.satisfies_h_principle_with (h1 : R.ample) (h2 : is_open R)
  (hC₁ : is_closed C₁) (hC₂ : is_closed C₂)
  (hε_pos : ∀ x, 0 < ε x) (hε_cont : continuous ε) :
  R.satisfies_h_principle_with IP C₁ C₂ ε :=
begin
  have hε_pos' : ∀ (x : P × M), 0 < ε x.2 := λ (x : P × M), hε_pos x.snd,
  have hε_cont' : continuous (λ (x : P × M), ε x.2) := hε_cont.comp continuous_snd,
  have is_op : is_open (rel_mfld.relativize IP P R) := R.is_open_relativize IP P h2,
  apply rel_mfld.satisfies_h_principle.satisfies_h_principle_with,
  exact (h1.relativize IP P).satisfies_h_principle is_op (hC₁.prod hC₂) hε_pos' hε_cont',
end

variables
{E' : Type*} [normed_add_comm_group E'] [normed_space ℝ E'] [finite_dimensional ℝ E']
{H' : Type*} [topological_space H'] {I' : model_with_corners ℝ E' H'} [model_with_corners.boundaryless I']
{M' : Type*} [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M']
[locally_compact_space M'] -- investigate how to deduce this from finite-dimensional
[sigma_compact_space M']
[t2_space M']
[nonempty M'] -- investigate how to remove this

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
