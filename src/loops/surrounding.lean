import loops.basic
import data.real.pi
import to_mathlib
import tactic.fin_cases
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

lemma loop.surrounds_iff_range_subset_range (γ : loop F) (x : F) : 
  γ.surrounds x ↔ ∃ (p : fin (d + 1) → F) (w : fin (d + 1) → ℝ), 
  surrounding_pts x p w ∧ range p ⊆ range γ :=
begin

  split,
  { exact λ ⟨t, w, h⟩, ⟨(γ ∘ t), w, h, range_comp_subset_range _ _⟩ },
  { rintros ⟨p, w, h₀, h₁⟩,
    rw range_subset_iff at h₁,
    choose t ht using h₁,
    have hpt : γ ∘ t = p := funext ht,
    exact ⟨t, w, hpt.symm ▸ h₀⟩ }
end

set_option profiler true
lemma surrounding_loop_of_convex_hull {f b : F} {O : set F} (O_op : is_open O) (O_conn : is_connected O) 
  (hsf : f ∈ convex_hull O) (hb : b ∈ O) : 
  ∃ γ : ℝ → loop F, continuous_on ↿γ (set.prod I univ) ∧ 
                    (∀ t, γ t 0 = b) ∧
                    (∀ s, γ 0 s = b) ∧
                    (∀ (t ∈ I) s, γ t s ∈ O) ∧
                    (γ 1).surrounds f :=
begin
  rcases surrounded_of_convex_hull O_op hsf with ⟨p, w, h, hp⟩,
  rw ← O_op.is_connected_iff_is_path_connected at O_conn,
  rcases (O_conn.exists_path_through_family p hp) with ⟨Ω₀, hΩ₀⟩,
  rcases O_conn.joined_in b (p 0) hb (hp 0) with ⟨Ω₁, hΩ₁⟩,
  let Ω := Ω₁.trans Ω₀,
  let γ : ℝ → loop F := λ t, let t' := proj_I t in
  { to_fun :=
      (λ s' : ℝ, if s'≤t' then Ω.extend s' else Ω.extend t') ∘ (λ s, (1 - real.cos (2*real.pi*s))/2),
    per' :=
    begin
      intros s,
      suffices h : (λ s, (1 - real.cos (2*real.pi*s))/2) (s+1) = (λ s, (1 - real.cos (2*real.pi*s))/2) s,
      { delta function.comp,
        rw h },
      simp only [mul_add, mul_one, real.cos_add_two_pi],
    end },
  use γ,
  split,
  { apply continuous.continuous_on,
    have h₁ : continuous (λ (s : ℝ × ℝ), (1 - real.cos (2 * real.pi * s.snd)) / 2) :=
      (continuous_mul_right _).comp ((continuous_const.sub continuous_id).comp $ 
        real.continuous_cos.comp $ (continuous_mul_left _).comp continuous_snd),
    have h₂ : continuous (λ (a : ℝ × ℝ), ↑(proj_I a.fst)) :=
      continuous_subtype_coe.comp (continuous_proj_I.comp continuous_fst),
    simp only [γ, has_uncurry.uncurry, coe_fn, has_coe_to_fun.coe, mul_one, comp_app],
    refine continuous_if _ (Ω.continuous_extend.comp h₁) (Ω.continuous_extend.comp h₂),
    rintros ⟨a, b⟩ hab,
    have := frontier_le_subset_eq h₁ h₂ hab,
    simp only [mem_set_of_eq] at this,
    rw this },
  split,
  { unfold_coes,
    intros t,
    simp [γ, ← subtype.val_eq_coe, (proj_I t).2.1] },
  split,
  { unfold_coes,
    intros s,
    simp only [γ, proj_I, dif_pos, path.extend_zero, comp_app, subtype.coe_mk],
    split_ifs with h,
    { have : real.cos (2 * real.pi * s) = 1 := le_antisymm (real.cos_le_one _) (by linarith [h]),
      simp only [this, path.extend_zero, zero_div, sub_self]},
    { refl } },
  split,
  { rintros t ht,
    suffices h : range (γ t) ⊆ O,
    { rwa range_subset_iff at h },
    unfold_coes,
    simp only [γ],
    apply' (range_comp_subset_range _ _).trans,
    apply' range_ite_subset.trans,
    have : range Ω.extend ⊆ O,
    { simp only [Ω.extend_range, Ω₁.trans_range, hΩ₀.right, range_subset_iff.mpr hΩ₁, union_subset_iff, and_self]},
    rw union_subset_iff, 
    simp only [this, range_subset_iff.mp this, range_const, singleton_subset_iff, and_self] },
  { rw loop.surrounds_iff_range_subset_range,
    refine ⟨p, w, h, _⟩,
    rw range_subset_iff,
    intro i,
    unfold_coes,
    suffices h : p i ∈ range Ω.extend, 
    { have hproj : (proj_I 1 : ℝ) = 1,
      { simp [proj_I, not_le_of_lt zero_lt_one, le_refl 1] },
      have hcos : range (λ (s : ℝ), (1 - real.cos (2 * real.pi * s)) / 2) = I,
      { ext,
        split,
        { rintros ⟨y, hxy⟩,
          simp only [← hxy],
          have h₀ := (2*real.pi*y).neg_one_le_cos, 
          have h₁ := (2*real.pi*y).cos_le_one,
          split; linarith },
        { rintros ⟨h₀, h₁⟩,
          rw mem_range,
          rcases @real.exists_cos_eq (1-2*x) ⟨by linarith, by linarith⟩ with ⟨y, ⟨hy₀, hy₁⟩, hxy⟩,
          use (2*real.pi)⁻¹ * y,
          rw mul_inv_cancel_left';
          linarith [real.pi_pos] } },
      simp only [γ, range_comp, hcos, hproj, mem_image, path.extend_one],
      rcases h with ⟨x, hx⟩,
      use proj_I x,
      use (proj_I x).2,
      have : (proj_I x : ℝ) ∈ I := (proj_I x).2,
      simpa only [this.right, Ω.extend_extends this, if_true, subtype.coe_eta], },
    simp only [Ω.extend_range, Ω, path.trans_range],
    right,
    exact hΩ₀.1 i }
end

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