import notations
import loops.reparametrization
import analysis.calculus.specific_functions
import to_mathlib.convolution


noncomputable theory

open set function finite_dimensional prod int
open_locale topological_space unit_interval convolution


variables {E : Type*} [normed_group E] [normed_space ℝ E]
          {F : Type*} [normed_group F]
          {g b : E → F} {Ω : set (E × F)} {U K C : set E}

/-- Equivariant maps from `ℝ` to itself are functions `f : ℝ → ℝ` with `f (t + 1) = f t + 1`. -/
structure equivariant_map :=
(to_fun : ℝ → ℝ)
(eqv' : ∀ t, to_fun (t + 1) = to_fun t + 1)

namespace equivariant_map

variable (φ : equivariant_map)

instance : has_coe_to_fun equivariant_map (λ _, ℝ → ℝ) := ⟨equivariant_map.to_fun⟩

lemma eqv : ∀ t, φ (t + 1) = φ t + 1 := φ.eqv'

end equivariant_map

variables [normed_space ℝ F] [measurable_space F] [borel_space F] [finite_dimensional ℝ F]

@[simp] lemma fract_add_one {α} [linear_ordered_ring α] [floor_ring α] (a : α) :
  fract (a + 1) = fract a :=
by exact_mod_cast fract_add_int a 1

/-- continuous equivariant reparametrization that is locally constant around `0`.
  It linearly connects `(0, 0)`, `(1/4, 0)` and `(3/4, 1)` and `(1, 1)` and is extended to an
  equivariant function. -/
def linear_reparam : equivariant_map :=
⟨λ x, ⌊ x ⌋ + max 0 (min 1 $ 2 * fract (x - 4⁻¹)), λ t,
  by simp [floor_add_one, add_sub, ← sub_add_eq_add_sub _ _ (1 : ℝ), fract_add_one, add_right_comm]⟩

variables (g b Ω U K)

structure nice_loop (γ : ℝ → E → loop F) : Prop :=
(t_le_zero : ∀ x, ∀ t ≤ 0, γ t x = γ 0 x)
(t_ge_one : ∀ x, ∀ t ≥ 1, γ t x = γ 1 x)
(t_zero : ∀ x s, γ 0 x s = b x)
(s_zero : ∀ x t, γ t x 0 = b x)
(avg : ∀ x, (γ 1 x).average = g x)
(mem_Ω : ∀ x t s, (x, γ t x s) ∈ Ω)
(smooth : 𝒞 ∞ ↿γ)
(rel_K : ∀ᶠ x in 𝓝ˢ K, ∀ t s, γ t x s = b x)

variables {g b Ω U K}

open measure_theory measure_theory.measure
/- lemma exists_loops' [finite_dimensional ℝ E]
  --todo: obtain the measure structure on `E` in the proof
  [measure_space E] [is_add_haar_measure (volume : measure E)]
  (hK : is_compact K) (hC : is_closed C) (hU : is_open U) (hKC : K ⊆ C) (hCU : C ⊆ U)
  (hΩ_op : is_open $ Ω ∩ fst ⁻¹' U)
  (hΩ_conn : ∀ x ∈ C, is_connected (prod.mk x ⁻¹' Ω))
  (hg : ∀ x ∈ U, smooth_at g x) (hb : cont_diff ℝ ⊤ b) (hb_in : ∀ x ∈ C, (x, b x) ∈ Ω)
  (hgK : ∀ᶠ x in 𝓝ˢ K, g x = b x) (hconv : ∀ x ∈ C, g x ∈ convex_hull ℝ (prod.mk x ⁻¹' Ω)) :
  ∃ γ : ℝ → E → loop F, nice_loop g b Ω C K γ :=
begin
  -- we could probably get away with something simpler to get γ₀.
  obtain ⟨γ₀, hγ₀_cont, hγ₀0, h2γ₀0, -, hγ₀_surr⟩ := -- γ₀ is γ* in notes
    surrounding_loop_of_convex_hull is_open_univ is_connected_univ
    (by { rw [convex_hull_univ], exact mem_univ 0 }) (mem_univ (0 : F)),
  have := λ x (hx : x ∈ C),
    local_loops_open ⟨U, hU.mem_nhds $ hCU hx, hΩ_op⟩ (hΩ_conn x hx) (hg x $ hCU hx).continuous_at
    hb.continuous (hb_in x hx) (hconv x hx),
  -- let γ₀ : loop F := sorry, -- γ* in notes
  -- have hγ₀ : γ₀.surrounds 0,
  -- { sorry },
  -- have h0γ₀ : γ₀ 0 = 0 := sorry,
  -- have hγ₀_cont : continuous γ₀ := sorry,
  obtain ⟨ε, hε⟩ : { x : ℝ // 0 < x } := ⟨1, zero_lt_one⟩, -- todo
  -- let γ₁ : E → ℝ → loop F := λ x t, γ₀.transform (λ y, b x + t • ε • y),
  let γ₁ : E → ℝ → loop F := λ x t, (γ₀ t).transform (λ y, b x + ε • y), -- γₓ
  have hγ₁ : ∃ V ∈ 𝓝ˢ K, surrounding_family_in g b γ₁ V Ω,
  { refine ⟨_, hgK, ⟨by simp [γ₁, hγ₀0], by simp [γ₁, h2γ₀0], _, _⟩, _⟩,
    { intros x hx, rw [mem_set_of_eq] at hx, rw [hx],
      exact (hγ₀_surr.smul0 hε.ne').vadd0, },
    { refine (hb.continuous.comp continuous_fst).add
        (continuous_const.smul $ hγ₀_cont.comp continuous_snd) },
    sorry }, -- choose ε sufficiently small, and perhaps V smaller
  obtain ⟨γ₂, hγ₂, hγ₂₁⟩ := exists_surrounding_loops hK hC hU hCU hΩ_op hΩ_conn
    (λ x hx, (hg x (hCU hx)).continuous_at) hb.continuous hb_in hconv hγ₁,
  let γ₃ : E → ℝ → loop F := λ x t, (γ₂ x t).reparam linear_reparam,
  let φ : E × ℝ × ℝ → ℝ :=
  (⟨⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩⟩ : cont_diff_bump (0 : E × ℝ × ℝ)),
  let γ₄ := ↿γ₃,
  let γ₅ : E × ℝ × ℝ → F := φ ⋆ γ₄,
  let γ₆ : ℝ → E → loop F,
  { refine λ s x, ⟨λ t, γ₅ (x, s, t), λ t, _⟩,
    change ∫ u, φ u • γ₃ (x - u.1) (s - u.2.1) (t + 1 - u.2.2) =
      ∫ u, φ u • γ₃ (x - u.1) (s - u.2.1) (t - u.2.2),
    simp_rw [← sub_add_eq_add_sub, (γ₃ _ _).per] },
  -- todo: apply reparametrization
  refine ⟨γ₆, _, _, _, _, _, _, _, _⟩,
  { sorry },
  { sorry },
  { sorry },
  { sorry },
  { sorry },
  { sorry },
  { sorry },
  { sorry },
end -/



/- We probably don't get quite this statement after weakening `exists_surrounding_loops` -/
lemma exists_loops
  (hK : is_compact K)
  (hΩ_op : is_open Ω)
  (hΩ_conn : ∀ x, is_connected (prod.mk x ⁻¹' Ω))
  (hg : 𝒞 ∞ g) (hb : 𝒞 ∞ b) (hb_in : ∀ x, (x, b x) ∈ Ω)
  (hgK : ∀ᶠ x near K, g x = b x) (hconv : ∀ x, g x ∈ hull (prod.mk x ⁻¹' Ω)) :
  ∃ γ : ℝ → E → loop F, nice_loop g b Ω K γ  :=
sorry
