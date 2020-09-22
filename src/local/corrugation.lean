import analysis.asymptotics

import parametric_integral
import loops.basic

noncomputable theory

local notation `D` := fderiv ℝ

open set function finite_dimensional asymptotics filter
open_locale topological_space

variables {E : Type*} 
          {F : Type*} [normed_group F] [normed_space ℝ F] [measurable_space F] [borel_space F] [finite_dimensional ℝ F]

/-- Theillière's corrugations. -/
def corrugation (π : E → ℝ) (N : ℝ) (γ : E → loop F) : E → F :=
λ x, (1/N) • ∫ t in 0..(N*π x), (γ x t - (γ x).average)

variables (π : E → ℝ) (N : ℝ) (γ : E → loop F)

lemma corrugation.support [topological_space E] : support (corrugation π N γ) ⊆ loop.support γ :=
sorry

/-- If a loop family has compact support then the corresponding corrugation is
`O(1/N)` uniformly in the source point. -/
lemma corrugation.c0_small [topological_space E] (hγ : is_compact (loop.support γ)) :
  ∃ C, ∀ x, is_O_with C (λ N, corrugation π N γ x) (λ N, 1/N) at_top :=
sorry

variables [normed_group E] [normed_space ℝ E] (hγ : is_compact (loop.support γ))

open linear_map

lemma corrugation.fderiv :
  ∃ C, ∀ x, ∀ v, is_O_with C (λ N, D (corrugation π N γ) x v - (D π x v) • (γ x (N*π v) - (γ x).average)) (λ N, ∥v∥/N) at_top :=
sorry

lemma corrugation.fderiv_ker :
  ∃ C, ∀ x, ∀ w ∈ ker (D π x : E →ₗ[ℝ] ℝ), is_O_with C (λ N, D (corrugation π N γ) x w) (λ N, ∥w∥/N) at_top :=
sorry

lemma corrugation.fderiv_u {u : E} (hu : ∀ x, fderiv ℝ π x u = 1) :
  ∃ C, ∀ x, is_O_with C (λ N, D (corrugation π N γ) x u - (γ x (N*π u) - (γ x).average)) (λ N, ∥u∥/N) at_top :=
sorry