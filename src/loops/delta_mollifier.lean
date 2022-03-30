import notations
import loops.basic
import measure_theory.integral.interval_integral

open set function

/-- A stictly positive, smooth approximation to the Dirac delta function on the circle, centered at
`t` (regarded as a point of the circle) and converging to the Dirac delta function as `η → 0`.

TODO: When constructing these, we can just do `t = 0` case and then translate. -/
def delta_mollifier (η : ℝ) (t : ℝ) : ℝ → ℝ := sorry

variables {η : ℝ} (hη : 0 < η) (t : ℝ)
include hη

lemma delta_mollifier_periodic : periodic (delta_mollifier η t) 1 := sorry

lemma delta_mollifier_pos (s : ℝ) : 0 < delta_mollifier η t s := sorry

lemma delta_mollifier_smooth : 𝒞 ∞ ↿(delta_mollifier η) := sorry

lemma delta_mollifier_integral_eq_one : ∫ s in 0..1, delta_mollifier η t s = 1 := sorry

omit hη

/-- I doubt this is exactly the right property and I think we may be able to get away with something
a good deal weaker. The plan is to try finishing the reparametrization lemma and see what
convergence property it requires. -/
lemma delta_mollifier_converges {F : Type*}
  [normed_group F] [normed_space ℝ F] [finite_dimensional ℝ F] [measurable_space F] [borel_space F]
  {ε : ℝ} (hε : 0 < ε) :
  ∃ δ > (0 : ℝ), ∀ (γ : loop F) (hf : continuous γ) η, η ∈ Ioo 0 δ →
  ∥γ t - ∫ s in 0..1, delta_mollifier η t s • γ s∥ < ε * Sup ((norm ∘ γ) '' (Icc 0 1)) :=
sorry
