import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import SphereEversion.ToMathlib.Algebra.Ring.Periodic
import SphereEversion.ToMathlib.Analysis.ContDiff
import SphereEversion.Loops.Basic

/-!
# Delta mollifiers

A key ingredient in the proof of the reparametrization lemma is the existence of a smooth
approximation to the Dirac delta function. Such an approximation is a sequence of functions
`δ : ℕ × S¹ → S¹`, `(i, t) ↦ δᵢ t` such that:
 * `δᵢ` is smooth for all `i`,
 * `δᵢ` is non-negative for all `i`,
 * `∫ x in 0..1, (δᵢ x) = 1` for all `i`,
* `∫ x in 0..1, (δᵢ x) • f x → f 0`, as `i → ∞` for any continuous function `f` on `S¹`.

This file contains a construction `approxDirac` of such a family `δ` together with code which
packages this into the precise form required for the proof of the reparametrization lemma:
`deltaMollifier`, `Loop.mollify`.

The key ingredients are the existence of smooth "bump functions" and a powerful theory of
convolutions.
-/


noncomputable section

open Set Function MeasureTheory.MeasureSpace ContinuousLinearMap
open scoped Topology Filter Convolution ContDiff

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
section

/-! ## Bump family

In this section we construct `bump (n : ℕ)`, a bump function with support in
`Ioo (-1/(n+2)) (1/(n+2))`.
-/


/-- `bump n` is a bump function on `ℝ` which has support `Ioo (-(1/(n+2))) (1/(n+2))`
and equals one on `Icc (-(1/(n+3))) (1/(n+3))`.
-/
def bump (n : ℕ) : ContDiffBump (0 : ℝ) where
  rIn := 1 / (n + 3)
  rOut := 1 / (n + 2)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    apply one_div_lt_one_div_of_lt
    · exact_mod_cast Nat.succ_pos _
    · exact_mod_cast lt_add_one (n + 2)

theorem support_bump (n : ℕ) : support (bump n) = Ioo (-((1 : ℝ) / (n + 2))) (1 / (n + 2)) := by
  rw [(bump n).support_eq, Real.ball_eq_Ioo, zero_sub, zero_add, bump]

theorem support_bump_subset (n : ℕ) : support (bump n) ⊆ Ioc (-(1 / 2)) (1 / 2) := by
  have ineg : 1 / (n + 2 : ℝ) ≤ 1 / 2 := by apply one_div_le_one_div_of_le <;> norm_num
  rw [support_bump n]
  exact Ioo_subset_Ioc_self.trans (Ioc_subset_Ioc (neg_le_neg ineg) ineg)

theorem support_shifted_normed_bump_subset (n : ℕ) (t : ℝ) :
    (support fun x ↦ (bump n).normed volume (x - t)) ⊆ Ioc (t - 1 / 2) (t + 1 / 2) := by
  change support ((bump n).normed volume ∘ (· - t)) ⊆ _
  rw [Function.support_comp_eq_preimage, (bump n).support_normed_eq, ← (bump n).support_eq]
  refine (preimage_mono (support_bump_subset n)).trans ?_
  simp [sub_eq_add_neg, add_comm]

end

section

/-! # Periodize

In this section we turn any function `f : ℝ → E` into a 1-periodic function
`fun t : ℝ ↦ ∑ᶠ n : ℤ, f (t+n)`.
-/


variable {M : Type*} [AddCommMonoid M]

/-- Turn a function into a 1-periodic function. If its support lies in a (non-closed) interval
of length 1, then this will be that function made periodic with period 1. -/
def periodize (f : ℝ → M) (t : ℝ) : M :=
  ∑ᶠ n : ℤ, f (t + n)

theorem periodic_periodize (f : ℝ → M) : Periodic (periodize f) 1 := by
  intro t
  unfold periodize
  have : (fun n : ℤ ↦ f (t + 1 + ↑n)) = fun n ↦ f (t + (n + 1 : ℤ)) := by
    ext n; simp_rw [Int.cast_add, Int.cast_one, add_assoc, add_comm]
  simp_rw [this]
  let e := Equiv.addRight (1 : ℤ)
  let F : ℤ → M := fun n ↦ f (t + n)
  change ∑ᶠ n : ℤ, F (e n) = ∑ᶠ n : ℤ, f (t + ↑n)
  apply finsum_comp_equiv

theorem periodize_nonneg {f : ℝ → ℝ} (h : ∀ t, 0 ≤ f t) (t : ℝ) : 0 ≤ periodize f t := by
  unfold periodize
  obtain (H | H) := (support fun i : ℤ ↦ f (t + i)).finite_or_infinite
  · rw [finsum_eq_sum _ H]
    exact Finset.sum_nonneg fun i _ ↦ h _
  · rwa [finsum_of_infinite_support]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

@[fun_prop]
theorem ContDiff.periodize {f : ℝ → E} {n : ℕ∞} (h : ContDiff ℝ n f) (h' : HasCompactSupport f) :
    ContDiff ℝ n (periodize f) := by
  refine contDiff_iff_contDiffAt.mpr fun x ↦ contDiffAt_finsum ?_ ?_
  · intro y
    set N := Ioo (y - 1) (y + 1)
    refine ⟨N, (nhds_basis_Ioo_pos y).mem_of_mem zero_lt_one, ?_⟩
    let e := fun i : ℤ ↦ Equiv.addRight (i : ℝ)
    change {i : ℤ | ((support fun x : ℝ ↦ f (e i x)) ∩ N).Nonempty}.Finite
    have hsupp : ∀ i : ℤ, (support fun x : ℝ ↦ f (e i x)) = e i ⁻¹' support f := fun _ ↦ rfl
    have hsupp' : ∀ i, (e i ⁻¹' support f ∩ N).Nonempty ↔ (support f ∩ e i '' N).Nonempty := by
      intro i
      conv_lhs => rw [← (e i).preimage_image N, ← preimage_inter]
      rw [(e i).surjective.nonempty_preimage]
    simp_rw [hsupp, hsupp', inter_comm (support f)]
    refine (ProperlyDiscontinuousVAdd.finite_disjoint_inter_image
      (isCompact_Icc : IsCompact <| Icc (y - 1) (y + 1)) h').subset ?_
    intro i hi
    rw [mem_setOf_eq, ← nonempty_iff_ne_empty]
    apply Nonempty.mono _ hi
    gcongr
    · rw [show (e i : ℝ → ℝ) = VAdd.vadd i by ext x; exact add_comm x i]
      exact image_mono Ioo_subset_Icc_self
    exact subset_tsupport f
  · fun_prop

theorem periodize_comp_sub (f : ℝ → M) (x t : ℝ) :
    periodize (fun x' ↦ f (x' - t)) x = periodize f (x - t) := by
  simp_rw [periodize, sub_add_eq_add_sub]

theorem periodize_smul_periodic (f : ℝ → ℝ) {g : ℝ → E} (hg : Periodic g 1) (t : ℝ) :
    periodize f t • g t = periodize (fun x ↦ f x • g x) t := by
  dsimp only [periodize]
  rw [finsum_smul]
  congr 1
  ext n
  rw [OnePeriodic.add_int hg]

open MeasureTheory

theorem integral_periodize (f : ℝ → E) {a : ℝ} (hf : support f ⊆ Ioc a (a + 1)) :
    ∫ t in a..a + 1, periodize f t = ∫ t in a..a + 1, f t := by
  apply intervalIntegral.integral_congr_ae
  have : ∀ᵐ x : ℝ, x ∈ uIoc a (a + 1) → x ∈ Ioo a (a + 1) := by
    rw [uIoc_of_le (le_add_of_nonneg_right (zero_le_one : (0 : ℝ) ≤ 1))]
    have : ∀ᵐ x : ℝ, x ≠ a + 1 := by simp [ae_iff]
    apply this.mono
    rintro x (x_ne : x ≠ a + 1) ⟨hx, hx'⟩
    exact ⟨hx, x_ne.le_iff_lt.mp hx'⟩
  apply this.mono
  intro t ht ht'
  specialize ht ht'
  dsimp only [periodize]
  have : (support fun n : ℤ ↦ f (t + n)) ⊆ ({0} : Finset ℤ) := fun n hn ↦ by
    suffices n = 0 by simpa
    replace hn : t + n ∈ Ioc a (a + 1) := hf (mem_support.mpr hn)
    cases ht
    cases hn
    have : -(1 : ℝ) < n := by linarith
    have : -1 < n := mod_cast this
    have : (n : ℝ) < 1 := by linarith
    norm_cast at this
    linarith
  simp [finsum_eq_sum_of_support_subset _ this]

-- if convenient we could set `[c,d] = [0,1]`
theorem intervalIntegral_periodize_smul (f : ℝ → ℝ) (γ : Loop E) {a b c d : ℝ} (h : b ≤ a + 1)
    (h2 : d = c + 1) (hf : support f ⊆ Ioc a b) :
    ∫ t in c..d, periodize f t • γ t = ∫ t, f t • γ t := by
  rw [h2]
  have : (support fun t ↦ f t • γ t) ⊆ Ioc a (a + 1) := by
    erw [support_smul]
    exact (inter_subset_left.trans hf).trans (Ioc_subset_Ioc_right h)
  rw [← intervalIntegral.integral_eq_integral_of_support_subset this]
  simp_rw [periodize_smul_periodic _ γ.periodic,
    Function.Periodic.intervalIntegral_add_eq (periodic_periodize fun x : ℝ ↦ f x • γ x) c a]
  exact integral_periodize _ this

end

section DeltaApprox

/-! ## An approximate Dirac "on the circle". -/


/-- A periodized bump function, which we can view as a function from `𝕊¹ → ℝ`. As `n → ∞` this
tends to the Dirac delta function located at `0`. -/
def approxDirac (n : ℕ) : ℝ → ℝ :=
  periodize <| (bump n).normed volume

theorem periodic_approxDirac (n : ℕ) : Periodic (approxDirac n) 1 := periodic_periodize _

theorem approxDirac_nonneg (n : ℕ) (t : ℝ) : 0 ≤ approxDirac n t :=
  periodize_nonneg (bump n).nonneg_normed t

@[fun_prop]
theorem contDiff_approxDirac (n : ℕ) : ContDiff ℝ ∞ (approxDirac n) :=
  (bump n).contDiff_normed.periodize (bump n).hasCompactSupport_normed

theorem approxDirac_integral_eq_one (n : ℕ) {a b : ℝ} (h : b = a + 1) :
    ∫ s in a..b, approxDirac n s = 1 := by
  have supp : support ((bump n).normed volume) ⊆ Ioc (-(1 / 2)) (-(1 / 2) + 1) := by
    rw [show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num,
      show support ((bump n).normed volume) = _ from (bump n).support_normed_eq, Real.ball_zero_eq,
      show (bump n).rOut = 1 / (n + 2 : ℝ) from rfl]
    have key : 1 / (n + 2 : ℝ) ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le
      · norm_num
      norm_cast
      norm_num
    exact (Ioo_subset_Ioo (neg_le_neg key) key).trans Ioo_subset_Ioc_self
  rw [approxDirac, h,
    Function.Periodic.intervalIntegral_add_eq (periodic_periodize _) a (-(1 / 2 : ℝ)),
    integral_periodize _ supp, intervalIntegral.integral_eq_integral_of_support_subset supp]
  exact (bump n).integral_normed

end DeltaApprox

section VersionOfDeltaMollifierUsingN

/-- A sequence of functions that converges to the Dirac delta function located at `t`, with the
properties that this sequence is everywhere positive and -/
def deltaMollifier (n : ℕ) (t : ℝ) : ℝ → ℝ := fun x ↦
  n / (n + 1) * approxDirac n (x - t) + 1 / (n + 1)

variable {n : ℕ} {t : ℝ}

theorem deltaMollifier_periodic : Periodic (deltaMollifier n t) 1 := fun x ↦ by
  simp_rw [deltaMollifier, ← sub_add_eq_add_sub, periodic_approxDirac n (x - t)]

theorem deltaMollifier_pos (s : ℝ) : 0 < deltaMollifier n t s := by
  have := approxDirac_nonneg n (s - t)
  exact add_pos_of_nonneg_of_pos (by positivity) (by positivity)

@[fun_prop]
theorem contDiff_deltaMollifier : ContDiff ℝ ∞ (deltaMollifier n t) := by
  unfold deltaMollifier; fun_prop

open intervalIntegral

@[simp]
theorem deltaMollifier_integral_eq_one : ∫ s in (0)..1, deltaMollifier n t s = 1 := by
  simp_rw [deltaMollifier]
  rw [integral_comp_sub_right (fun x ↦ (n : ℝ) / (n + 1) * approxDirac n x + 1 / (n + 1)) t,
    integral_add, integral_const_mul, integral_const, zero_sub, sub_neg_eq_add, sub_add_cancel,
    one_smul, approxDirac_integral_eq_one, mul_one, ← add_div, div_self]
  · exact n.cast_add_one_pos.ne'
  · rw [sub_eq_add_neg, add_comm]
  · exact ((contDiff_approxDirac n).continuous.intervalIntegrable _ _).const_mul _
  · exact intervalIntegrable_const

/-- `γ.mollify n t` is a weighted average of `γ` using weights `deltaMollifier n t`.
This means that as `n → ∞` this value tends to `γ t`, but because `deltaMollifier n t` is positive,
we know that we can reparametrize `γ` to obtain a loop that has `γ.mollify n t` as its actual
average. -/
def Loop.mollify (γ : Loop F) (n : ℕ) (t : ℝ) : F :=
  ∫ s in (0)..1, deltaMollifier n t s • γ s

theorem Loop.mollify_eq_convolution (γ : Loop F) (hγ : Continuous γ) (t : ℝ) :
    γ.mollify n t =
      ((n : ℝ) / (n + 1)) • ((bump n).normed volume ⋆[lsmul ℝ ℝ]γ) t +
        ((1 : ℝ) / (n + 1)) • ∫ t in (0)..1, γ t := by
  simp_rw [Loop.mollify, deltaMollifier, add_smul, mul_smul]
  rw [integral_add]
  on_goal 1 =>
    simp_rw [integral_smul, approxDirac, ← periodize_comp_sub]
    rw [intervalIntegral_periodize_smul _ γ _ _ (support_shifted_normed_bump_subset n t)]
  · simp_rw [MeasureTheory.convolution_eq_swap, ← neg_sub t, (bump n).normed_neg, lsmul_apply]
  · linarith
  · rw [zero_add]
  · exact (continuous_const.smul
      (((contDiff_approxDirac n).continuous.comp (by fun_prop)).smul hγ)).intervalIntegrable _ _
  · apply Continuous.intervalIntegrable (by fun_prop)

end VersionOfDeltaMollifierUsingN
