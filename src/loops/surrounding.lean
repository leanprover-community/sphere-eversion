import loops.basic
/-!
# Surrounding families of loops
-/

open set function finite_dimensional
open_locale topological_space

variables {E : Type*} [normed_group E] [normed_space ℝ E]
          {F : Type*} [normed_group F] [normed_space ℝ F] [finite_dimensional ℝ F]

local notation `d` := findim ℝ F
local notation `smooth_on` := times_cont_diff_on ℝ ⊤
local notation `I` := Icc (0 : ℝ) 1

/-- A loop `γ` surrounds a point `x` if `x` is surrounded by values of `γ`. -/
def loop.surrounds (γ : loop F) (x : F) : Prop := 
  ∃ t w : fin (d + 1) → ℝ, surrounding_pts x (γ ∘ t) w


lemma surrounding_loop_of_convex_hull {f b : F} {O : set F} (O_op : is_open O) (O_conn : is_connected O) 
  (hsf : f ∈ convex_hull O) (hb : b ∈ O) : 
  ∃ γ : ℝ → loop F, continuous_on ↿γ (set.prod I univ) ∧ 
                    ∀ t, γ t 0 = b ∧
                    ∀ s, γ 0 s = b ∧
                    ∀ (t ∈ I) s, γ t s ∈ O ∧
                    (γ 1).surrounds f :=
sorry

structure surrounding_family (g b : E → F) (γ : E → ℝ → loop F) (U : set E) : Prop :=
(base : ∀ x t, γ x t 0 = b x)
(t₀ : ∀ x s, γ x 0 s = b x)
(surrounds : ∀ x, (γ x 1).surrounds $ g x)
(cont : continuous ↿γ)

structure surrounding_family_in (g b : E → F) (γ : E → ℝ → loop F) (U : set E) (Ω : set $E × F) 
  extends surrounding_family g b γ U : Prop :=
(val_in : ∀ x ∈ U, ∀ (t ∈ I) s, (x, γ x t s) ∈ Ω)

variables {g b : E → F} {Ω : set (E × F)} {U K : set E}

lemma local_loops
  {x₀ : E}
  (hΩ_op : ∀ᶠ x in 𝓝 x₀, is_open (prod.mk x ⁻¹' Ω)) 
  (hg : ∀ᶠ x in 𝓝 x₀, continuous_at g x) (hb : ∀ᶠ x in 𝓝 x₀, continuous_at b x)
  (hb_in : ∀ᶠ x in 𝓝 x₀, (x, b x) ∈ Ω) 
  (hconv : ∀ᶠ x in 𝓝 x₀, g x ∈ convex_hull (prod.mk x ⁻¹' Ω)) :
∃ γ : E → ℝ → loop F, ∀ᶠ x in 𝓝 x₀, ∀ (t ∈ I) s, 
  (x, γ x t s) ∈ Ω ∧
  γ x 0 s = b x ∧
  (γ x 1).surrounds (g x) ∧
  continuous_at ↿γ ((x, t, s) : E × ℝ × ℝ) :=
sorry


lemma satisfied_or_refund {γ₀ γ₁ : E → ℝ → loop F} 
  (h₀ : surrounding_family g b γ₀ U) (h₁ : surrounding_family g b γ₁ U) :
  ∃ γ : ℝ → E → ℝ → loop F, 
    (∀ τ ∈ I, surrounding_family g b (γ τ) U) ∧ 
    γ 0 = γ₀ ∧
    γ 1 = γ₁ ∧
    (∀ (τ ∈ I) (x ∈ U) (t ∈ I) s, continuous_at ↿γ (τ, x, t, s)) :=
sorry

lemma extends_loops {U₀ U₁ K₀ K₁ : set E} (hU₀ : is_open U₀) (hU₁ : is_open U₁)
  (hK₀ : compact K₀) (hK₁ : compact K₁) (hKU₀ : K₀ ⊆ U₀) (hKU₁ : K₁ ⊆ U₁)
  {γ₀ γ₁ : E → ℝ → loop F} 
  (h₀ : surrounding_family g b γ₀ U₀) (h₁ : surrounding_family g b γ₁ U₁) :
  ∃ U ∈ nhds_set (K₀ ∪ K₁), ∃ γ : E → ℝ → loop F, 
    surrounding_family g b γ U ∧ 
    ∀ᶠ x in nhds_set K₀, γ x = γ₀ x :=
sorry


lemma exists_surrounding_loops 
  (hU : is_open U) (hK : compact K) (hKU : K ⊆ U) 
  (hΩ_op : ∀ x ∈ U, is_open (prod.mk x ⁻¹' Ω))
  (hΩ_conn : ∀ x ∈ U, is_connected (prod.mk x ⁻¹' Ω)) 
  (hg : ∀ x ∈ U, smooth_at g x) (hb : ∀ x ∈ U, smooth_at b x) (hb_in : ∀ x ∈ U, (x, b x) ∈ Ω) 
  (hgK : ∀ᶠ x in nhds_set K, g x = b x) 
  (hconv : ∀ x ∈ U, g x ∈ convex_hull (prod.mk x ⁻¹' Ω)) 
  {γ₀ :  E → ℝ → loop F} 
  (hγ₀_surr : ∃ V ∈ nhds_set K, surrounding_family_in g b γ₀ V Ω) :
  ∃ γ : E → ℝ → loop F, (surrounding_family_in g b γ U Ω) ∧ 
                        (∀ᶠ x in nhds_set K, ∀ (t ∈ I), γ x t = γ₀ x t)  :=
sorry