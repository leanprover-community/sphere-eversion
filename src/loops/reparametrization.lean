import loops.surrounding


/-!
# The reparametrization lemma
-/

open set function finite_dimensional
open_locale topological_space
local notation `I` := Icc (0 : ℝ) 1

variables {E : Type*} [normed_group E] [normed_space ℝ E]
          {F : Type*} [normed_group F] [normed_space ℝ F] [finite_dimensional ℝ F]
          {g b : E → F} {Ω : set (E × F)} {U K : set E}

/-- Circle diffeomorphisms seen as equivariant maps from `ℝ` to itself. -/
structure circle_diffeo :=
(to_fun : ℝ → ℝ)
(eqv' : ∀ t, to_fun (t+1) = to_fun t + 1)
(smooth' : ∀ t, smooth_at to_fun t)
(deriv' : ∀ t, deriv to_fun t ≠ 0)

namespace circle_diffeo

variable (φ : circle_diffeo)

instance : has_coe_to_fun circle_diffeo := ⟨_, circle_diffeo.to_fun⟩

lemma eqv : ∀ t, φ (t + 1) = φ t + 1 := φ.eqv'

lemma smooth : ∀ t, smooth_at φ t := φ.smooth'

lemma deriv : ∀ t, deriv φ t ≠ 0 := φ.deriv'

/-- Any function `φ : α → circle_diffeo` can be seen as a function `α × ℝ → ℝ`. -/
instance {α : Type*} : has_uncurry (α → circle_diffeo) (α × ℝ) ℝ := ⟨λ φ p, φ p.1 p.2⟩
end circle_diffeo

def loop.reparam (γ : loop F) (φ : circle_diffeo) : loop F :=
{ to_fun := γ ∘ φ,
  per' := λ t, by rw [comp_apply, φ.eqv, γ.per] }

lemma reparametrization [measurable_space F] [borel_space F]
  (γ : E → ℝ → loop F) (h_surr : surrounding_family g b γ U)
  (h_smooth : ∀ (x ∈ U) (t ∈ I) s, smooth_at ↿γ ((x, t, s) : E × ℝ × ℝ)) : 
  ∃ φ : E → circle_diffeo, ∀ (x ∈ U), (∀ s, smooth_at ↿φ (x, s)) ∧
                                      φ x 0 = 0 ∧
                                      ((γ x 1).reparam (φ x)).average = g x :=
sorry

lemma exists_loops [measurable_space F] [borel_space F] 
  (hU : is_open U) (hK : is_compact K) (hKU : K ⊆ U) 
  (hΩ_op : ∀ x ∈ U, is_open (prod.mk x ⁻¹' Ω))
  (hΩ_conn : ∀ x ∈ U, is_connected (prod.mk x ⁻¹' Ω)) 
  (hg : ∀ x ∈ U, smooth_at g x) (hb : ∀ x ∈ U, smooth_at b x) (hb_in : ∀ x ∈ U, (x, b x) ∈ Ω) 
  (hgK : ∀ᶠ x in nhds_set K, g x = b x) (hconv : ∀ x ∈ U, g x ∈ convex_hull (prod.mk x ⁻¹' Ω)) :
  ∃ γ : E → ℝ → loop F, (∀ (x ∈ U) (t ∈ I) s, (x, γ x t s) ∈ Ω ∧
                                              γ x 0 s = b x ∧
                                              (γ x 1).average = g x ∧
                                              smooth_at ↿γ ((x, t, s) : E × ℝ × ℝ)) ∧
                        (∀ᶠ x in nhds_set K, ∀ (t ∈ I) s, γ x t s = b x)  :=
sorry
