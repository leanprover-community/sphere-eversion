import notations
import loops.basic
import measure_theory.integral.interval_integral

noncomputable theory
open set function
open_locale topological_space

/-- A stictly positive, smooth approximation to the Dirac delta function on the circle, centered at
`t` (regarded as a point of the circle) and converging to the Dirac delta function as `η → 0`.

TODO: When constructing these, we can just do `t = 0` case and then translate. -/
def delta_mollifier (η t : ℝ) : ℝ → ℝ := sorry

variables {η : ℝ} (hη : η ≠ 0) (t : ℝ)
include hη

lemma delta_mollifier_periodic : periodic (delta_mollifier η t) 1 := sorry

lemma delta_mollifier_pos (s : ℝ) : 0 < delta_mollifier η t s := sorry

-- TODO Maybe just drop this, we'll probably only ever need `delta_mollifier_smooth'`.
lemma delta_mollifier_smooth : 𝒞 ∞ ↿(delta_mollifier η) := sorry

lemma delta_mollifier_smooth' : 𝒞 ∞ (delta_mollifier η t) :=
(delta_mollifier_smooth hη).comp (cont_diff_prod_mk t)

@[simp] lemma delta_mollifier_integral_eq_one : ∫ s in 0..1, delta_mollifier η t s = 1 := sorry

omit hη

variables {F : Type*} [normed_group F] [normed_space ℝ F] [finite_dimensional ℝ F]
variables [measurable_space F] [borel_space F]

-- TODO Relocate to `src/loops/basic.lean` if this turns out to be useful.
instance loop.has_norm : has_norm (loop F) := ⟨λ γ, ⨆ t, ∥γ t∥⟩

-- TODO Come up with a better name for this.
def loop.mollify (γ : loop F) (η t : ℝ) : F :=
if η = 0 then γ t else ∫ s in 0..1, delta_mollifier η t s • γ s

lemma loop.mollify_eq_of_ne_zero (γ : loop F) (η t : ℝ) (hη : η ≠ 0) :
  γ.mollify η t = ∫ s in 0..1, delta_mollifier η t s • γ s :=
if_neg hη

/-- I doubt this is exactly the right property and I think we may be able to get away with something
a good deal weaker. The plan is to try finishing the reparametrization lemma and see what
convergence property it requires. -/
lemma loop.eval_at_sub_mollify_lt {ε : ℝ} (hε : 0 < ε) :
  ∀ᶠ η in 𝓝 0, ∀ (γ : loop F) (hf : continuous γ), ∥γ t - γ.mollify η t∥ < ε * ∥γ∥ :=
sorry
