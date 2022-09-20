import analysis.asymptotics.asymptotics
import linear_algebra.dual
import measure_theory.integral.interval_integral
import analysis.calculus.parametric_integral

import to_mathlib.topology.periodic
import to_mathlib.analysis.calculus
import to_mathlib.measure_theory.parametric_interval_integral
import to_mathlib.measure_theory.borel_space

import notations

import loops.basic
import local.dual_pair

/-! # Theillière's corrugation operation

This files introduces the fundamental calculus tool of convex integration. The version of convex
integration that we formalize is Theillière's corrugation-based convex integration.
It improves a map `f : E → F` by adding to it some corrugation map
`λ x, (1/N) • ∫ t in 0..(N*π x), (γ x t - (γ x).average)` where `γ` is a family of loops in
`F` parametrized by `E` and `N` is some (very large) real number.

Under the assumption that `∀ x, (γ x).average = D f x p.v` for some dual pair `p`, this improved
map will have a derivative which is almost a value of `γ x` in direction `p.v` and almost the
derivative of `f` in direction `ker p.π`. More precisely, its derivative will be almost
`p.update (D f x) (γ x (N*p.π x))`. In addition the improved map will be very close to `f`
in C⁰ topology. All those "almost" and "very close" refer to the asymptotic behavior when `N`
is very large.

The main definition is `corrugation`. The main results are:
* `fderiv_corrugated_map` computing the difference between `D (f + corrugation p.π N γ) x` and
    `p.update (D f x) (γ x (N*p.π x)) + corrugation.remainder p.π N γ x`
* `remainder_c0_small_on` saying this difference is very small
* `corrugation.c0_small_on` saying that corrugations are C⁰-small

-/

noncomputable theory

open set function finite_dimensional asymptotics filter topological_space int measure_theory
     continuous_linear_map
open_locale topological_space unit_interval


variables
  {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
  {F : Type*} [normed_add_comm_group F] [normed_space ℝ F] [finite_dimensional ℝ F]
  {G : Type*} [normed_add_comm_group G] [normed_space ℝ G]
  {H : Type*} [normed_add_comm_group H] [normed_space ℝ H] [finite_dimensional ℝ H]
  {π : E →L[ℝ] ℝ} (N : ℝ) (γ : E → loop F)

open_locale borelize

/-- Theillière's corrugations. -/
def corrugation (π : E →L[ℝ] ℝ) (N : ℝ) (γ : E → loop F) : E → F :=
λ x, (1/N) • ∫ t in 0..(N*π x), (γ x t - (γ x).average)

local notation `𝒯` := corrugation π

/-- The integral appearing in corrugations is periodic. -/
lemma per_corrugation (γ : loop F) (hγ : ∀ s t, interval_integrable γ volume s t) :
  one_periodic (λ s, ∫ t in 0..s, γ t - γ.average) :=
begin
  have int_avg : ∀ s t,  interval_integrable (λ u : ℝ, γ.average) volume s t,
    from λ s t, interval_integrable_const,
  intros s,
  have int₁ : interval_integrable (λ t, γ t - γ.average) volume 0 s,
    from (hγ _ _).sub (int_avg _ _),
  have int₂ : interval_integrable (λ t, γ t - γ.average) volume s (s + 1),
    from (hγ _ _).sub (int_avg _ _),
  have int₃ : interval_integrable γ volume s (s + 1), from hγ _ _,
  have int₄ : interval_integrable (λ t, γ.average) volume s (s + 1), from int_avg _ _,
  dsimp only,
  /- Rmk: Lean doesn't want to rewrite using `interval_integral.integral_sub` without being
    given the integrability assumptions :-( -/
  rw [← interval_integral.integral_add_adjacent_intervals int₁ int₂,
      interval_integral.integral_sub int₃ int₄, γ.periodic.interval_integral_add_eq s 0,
      zero_add, loop.average],
  simp only [add_zero, add_tsub_cancel_left, interval_integral.integral_const, one_smul, sub_self]
end

@[simp] lemma corrugation_const {x : E} (h : (γ x).is_const) : 𝒯 N γ x = 0 :=
begin
  unfold corrugation,
  rw loop.is_const_iff_const_avg at h,
  rw h,
  simp only [add_zero, interval_integral.integral_const, loop.const_apply, loop.average_const, smul_zero, sub_self]
end

variables (γ π N)

lemma corrugation.support : support (𝒯 N γ) ⊆ loop.support γ :=
begin
  intros x x_in,
  apply subset_closure,
  intro h,
  apply x_in,
  simp [h]
end

lemma corrugation_eq_zero (x ∉ loop.support γ) : corrugation π N γ x = 0 :=
nmem_support.mp (λ hx, H (corrugation.support N γ hx))

lemma corrugation.c0_small_on [first_countable_topology E]
  [locally_compact_space E] {γ : ℝ → E → loop F} {K : set E} (hK : is_compact K)
  (h_le : ∀ x, ∀ t ≤ 0, γ t x = γ 0 x) (h_ge : ∀ x, ∀ t ≥ 1, γ t x = γ 1 x)
  (hγ_cont : continuous ↿γ) {ε : ℝ} (ε_pos : 0 < ε) :
  ∀ᶠ N in at_top, ∀ (x ∈ K) t, ∥𝒯 N (γ t) x∥ < ε :=
begin
  have cont' : continuous ↿(λ (q : ℝ × E)  t, ∫ t in 0..t, (γ q.1 q.2) t - (γ q.1 q.2).average),
  { refine continuous_parametric_interval_integral_of_continuous _ continuous_snd,
    refine (hγ_cont.comp₃ continuous_fst.fst.fst continuous_fst.fst.snd continuous_snd).sub _,
    refine loop.continuous_average _,
    exact hγ_cont.comp₃ continuous_fst.fst.fst.fst continuous_fst.fst.fst.snd continuous_snd },
  rcases cont'.bounded_on_compact_of_one_periodic _ ((is_compact_Icc : is_compact I).prod hK) with ⟨C, hC⟩,
  { apply (const_mul_one_div_lt ε_pos C).mono,
    intros N hN x hx t,
    rw [corrugation, norm_smul, mul_comm],
    apply (mul_le_mul_of_nonneg_right _ (norm_nonneg $ 1/N)).trans_lt hN,
    cases le_or_lt t 0 with ht ht,
    { rw h_le x t ht,
      apply hC (0, x),
      simp [hx] },
    { cases le_or_lt 1 t with ht' ht',
      { rw h_ge x t ht',
        apply hC (1, x),
        simp [hx] },
      { exact hC (t, x) (mk_mem_prod ⟨ht.le, ht'.le⟩ hx) _ } } },
  { rintros ⟨t, x⟩,
    apply per_corrugation,
    intros a b,
    exact (hγ_cont.comp₃ continuous_const continuous_const continuous_id).interval_integrable _ _ }
end

variables {γ}

lemma corrugation.cont_diff' {n : ℕ∞} {γ : G → E → loop F} (hγ_diff : 𝒞 n ↿γ)
  {x : H → E} (hx : 𝒞 n x) {g : H → G} (hg : 𝒞 n g) :
  𝒞 n (λ h, 𝒯 N (γ $ g h) $ x h) :=
begin
  apply cont_diff.const_smul,
  apply cont_diff_parametric_primitive_of_cont_diff,
  { apply cont_diff.sub,
    { exact hγ_diff.comp₃ hg.fst' hx.fst' cont_diff_snd },
    { apply cont_diff_average,
      exact hγ_diff.comp₃ hg.fst'.fst' hx.fst'.fst' cont_diff_snd } },
  { apply cont_diff_const.mul (π.cont_diff.comp hx) },
end

lemma corrugation.cont_diff [finite_dimensional ℝ E] {n : ℕ∞} (hγ_diff : 𝒞 n ↿γ) :
  𝒞 n (𝒯 N γ) :=
(cont_diff_parametric_primitive_of_cont_diff
  (cont_diff_sub_average hγ_diff) (π.cont_diff.const_smul N) 0).const_smul _

notation `∂₁` := partial_fderiv_fst ℝ

/--
The remainder appearing when differentiating a corrugation.
-/
def corrugation.remainder (π : E → ℝ) (N : ℝ) (γ : E → loop F) : E → (E →L[ℝ] F) :=
λ x, (1/N) • ∫ t in 0..(N*π x), ∂₁ (λ x t, (γ x).normalize t) x t

local notation `R` := corrugation.remainder π

variable [finite_dimensional ℝ E]

lemma remainder_eq (N : ℝ) {γ : E → loop F} (h : 𝒞 1 ↿γ) :
R N γ = λ x, (1/N) • ∫ t in 0..(N*π x), (loop.diff γ x).normalize t :=
by { simp_rw loop.diff_normalize h, refl }

-- The next lemma is a restatement of the above to emphasize that remainder is a corrugation
-- but it won't be used directly
lemma remainder_eq_corrugation (N : ℝ) {γ : E → loop F} (h : 𝒞 1 ↿γ) :
R N γ = 𝒯 N (λ x, (loop.diff γ x)) :=
remainder_eq _ _ h

@[simp]
lemma remainder_eq_zero (N : ℝ) {γ : E → loop F} (h : 𝒞 1 ↿γ) {x : E} (hx : x ∉ loop.support γ) :
  R N γ x = 0 :=
begin
  have hx' : x ∉ loop.support (loop.diff γ), from (λ h, hx $ loop.support_diff h),
  simp [remainder_eq π N h, loop.normalize_of_is_const (loop.is_const_of_not_mem_support hx')]
end

lemma corrugation.fderiv_eq {N : ℝ} (hN : N ≠ 0) (hγ_diff : 𝒞 1 ↿γ) :
  D (𝒯 N γ) = λ x : E, (γ x (N*π x) - (γ x).average) ⬝ π + R N γ x :=
begin
  ext1 x₀,
  have hπ_diff := π.cont_diff,
  have diff := cont_diff_sub_average hγ_diff,
  have key :=
    (has_fderiv_at_parametric_primitive_of_cont_diff' diff (hπ_diff.const_smul N) x₀ 0).2,
  erw [fderiv_const_smul key.differentiable_at,
       key.fderiv,
       smul_add, add_comm],
  congr' 1,
  rw [fderiv_const_smul (hπ_diff.differentiable le_rfl).differentiable_at N, π.fderiv],
  simp only [smul_smul, inv_mul_cancel hN, one_div, algebra.id.smul_eq_mul, one_smul,
              continuous_linear_map.comp_smul]
end

lemma corrugation.fderiv_apply (hN : N ≠ 0) (hγ_diff : 𝒞 1 ↿γ) (x v : E) :
  D (𝒯 N γ) x v = (π v) • (γ x (N*π x) - (γ x).average) + R N γ x v :=
by simp only [corrugation.fderiv_eq hN hγ_diff, to_span_singleton_apply, add_apply,
              coe_comp', comp_app]

lemma fderiv_corrugated_map (hN : N ≠ 0) (hγ_diff : 𝒞 1 ↿γ) {f : E → F} (hf : 𝒞 1 f)
  (p : dual_pair E) {x} (hfγ : (γ x).average = D f x p.v) :
D (f + corrugation p.π N γ) x = p.update (D f x) (γ x (N*p.π x)) + corrugation.remainder p.π N γ x :=
begin
  ext v,
  erw fderiv_add (hf.differentiable le_rfl).differentiable_at
      ((corrugation.cont_diff N hγ_diff).differentiable le_rfl).differentiable_at,
  simp_rw [continuous_linear_map.add_apply, corrugation.fderiv_apply N hN hγ_diff, hfγ,
    dual_pair.update, continuous_linear_map.add_apply,p.π.comp_to_span_singleton_apply, add_assoc],
end

lemma remainder.smooth {γ : G → E → loop F} (hγ_diff : 𝒞 ∞ ↿γ)
  {x : H → E} (hx : 𝒞 ∞ x) {g : H → G} (hg : 𝒞 ∞ g) :
  𝒞 ∞ (λ h, R N (γ $ g h) $ x h) :=
begin
  apply cont_diff.const_smul,
  apply cont_diff_parametric_primitive_of_cont_diff,
  { let ψ : E → (H × ℝ) → F := λ x q, (γ (g q.1) x).normalize q.2,
    change 𝒞 ⊤ (λ (q : H × ℝ), ∂₁ ψ (x q.1) (q.1, q.2)),
    refine (cont_diff.cont_diff_top_partial_fst _).comp₂ hx.fst'
      (cont_diff_fst.prod cont_diff_snd),
    dsimp [ψ, loop.normalize],
    apply cont_diff.sub,
    apply hγ_diff.comp₃ hg.fst'.snd' cont_diff_fst cont_diff_snd.snd,
    apply cont_diff_average,
    exact hγ_diff.comp₃ hg.fst'.snd'.fst' cont_diff_fst.fst' cont_diff_snd },
  { exact cont_diff_const.mul (π.cont_diff.comp hx) },
end

lemma remainder_c0_small_on {K : set E} (hK : is_compact K)
  (hγ_diff : 𝒞 1 ↿γ) {ε : ℝ} (ε_pos : 0 < ε) :
  ∀ᶠ N in at_top, ∀ x ∈ K, ∥R N γ x∥ < ε :=
begin
  have : ∀ N : ℝ, R N γ = 𝒯 N (loop.diff γ),
  { intro N,
    exact remainder_eq π N hγ_diff },
  simp_rw (λ N, remainder_eq π N hγ_diff),
  let g : ℝ → E → loop (E →L[ℝ] F) := λ t, (loop.diff γ),
  have g_le : ∀ x (t : ℝ), t ≤ 0 → g t x = g 0 x, from λ _ _ _, rfl,
  have g_ge : ∀ x (t : ℝ), t ≥ 1 → g t x = g 1 x, from λ _ _ _, rfl,
  have g_cont : continuous ↿g, from (loop.continuous_diff hγ_diff).snd',
  apply (corrugation.c0_small_on hK g_le g_ge g_cont ε_pos).mono,
  intros N H x x_in,
  exact H x x_in 0
end
