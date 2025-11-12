import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

noncomputable section

open MeasureTheory Set

section

variable {E : Type*} [NormedAddCommGroup E]

-- lemma interval_integrable_of_integral_ne_zero
--   [complete_space E] [normed_space ℝ E] {a b : ℝ}
--   {f : ℝ → E} {μ : measure ℝ} (h : ∫ x in a..b, f x ∂μ ≠ 0) :
--   interval_integrable f μ a b :=
-- begin
--   contrapose! h,
--   exact interval_integral.integral_undef h,
-- end
-- lemma interval_integrable_norm_iff {f : ℝ → E} {μ : measure ℝ} {a b : ℝ}
--   (hf : ae_strongly_measurable f (μ.restrict (Ι a b))) :
--   interval_integrable (λ t, ‖f t‖) μ a b ↔ interval_integrable f μ a b :=
-- begin
--   simp_rw [interval_integrable_iff, integrable_on],
--   exact integrable_norm_iff hf
-- end
-- not ported

-- note: I always means Set.Icc...

theorem intervalIntegrable_of_nonneg_of_le {f g : ℝ → ℝ} {μ : Measure ℝ} {a b : ℝ}
    (hf : AEStronglyMeasurable f <| μ.restrict (Icc a b))
    (h : ∀ᵐ t ∂μ.restrict <| Icc a b, 0 ≤ f t ∧ f t ≤ g t) (hg : IntervalIntegrable g μ a b) :
    IntervalIntegrable f μ a b := by
  rw [intervalIntegrable_iff] at *
  apply Integrable.mono' hg hf (h.mono _)
  rintro t ⟨H, H'⟩
  change abs (f t) ≤ _
  rwa [abs_of_nonneg H]

variable [CompleteSpace E] [NormedSpace ℝ E] {a b : ℝ} {f : ℝ → E} {bound : ℝ → ℝ} {μ : Measure ℝ}

-- next 4 lemmas not ported (also unused)
namespace intervalIntegral

theorem integral_mono_of_le {f g : ℝ → ℝ} {a b : ℝ} {μ : Measure ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable f μ a b) (hg : IntervalIntegrable g μ a b)
    (hfg : f ≤ᵐ[μ.restrict (Icc a b)] g) : ∫ u in a..b, f u ∂μ ≤ ∫ u in a..b, g u ∂μ := by
  rw [uIoc_of_le hab] at hfg
  let H := hfg.filter_mono (ae_mono le_rfl)
  simpa only [integral_of_le hab] using setIntegral_mono_ae_restrict hf.1 hg.1 H

theorem integral_mono_of_le_of_nonneg {f g : ℝ → ℝ} {a b : ℝ} {μ : Measure ℝ} (hab : a ≤ b)
    (hf : AEStronglyMeasurable f <| μ.restrict (Icc a b))
    (hfnonneg : ∀ᵐ t ∂μ.restrict <| Ιcc a b, 0 ≤ f t) (hg : IntervalIntegrable g μ a b)
    (hfg : f ≤ᵐ[μ.restrict (Ιcc a b)] g) : ∫ u in a..b, f u ∂μ ≤ ∫ u in a..b, g u ∂μ := by
  apply integral_mono_of_le hab _ hg hfg
  have : ∀ᵐ t ∂μ.restrict <| Ι a b, 0 ≤ f t ∧ f t ≤ g t := hfnonneg.and hfg
  apply intervalIntegrable_of_nonneg_of_le hf this hg

theorem integral_antimono_of_le {f g : ℝ → ℝ} {a b : ℝ} {μ : Measure ℝ} (hab : b ≤ a)
    (hf : IntervalIntegrable f μ a b) (hg : IntervalIntegrable g μ a b)
    (hfg : f ≤ᵐ[μ.restrict (Ιcc a b)] g) : ∫ u in a..b, g u ∂μ ≤ ∫ u in a..b, f u ∂μ := by
  cases' hab.eq_or_lt with hab hab
  · simp [hab]
  · rw [uIoc_of_ge hab.le] at hfg
    rw [integral_symm b a, integral_symm b a]
    apply neg_le_neg
    apply integral_mono_of_le hab.le hf.symm hg.symm
    have : Ioc b a = uIoc b a := by rw [uIoc_of_le hab.le]
    rw [← this]
    exact hfg

theorem integral_antimono_of_le_of_nonneg {f g : ℝ → ℝ} {a b : ℝ} {μ : Measure ℝ} (hab : b ≤ a)
    (hf : AEStronglyMeasurable f <| μ.restrict (Ι a b))
    (hfnonneg : ∀ᵐ t ∂μ.restrict <| Ι a b, 0 ≤ f t) (hg : IntervalIntegrable g μ a b)
    (hfg : f ≤ᵐ[μ.restrict (Ι a b)] g) : ∫ u in a..b, g u ∂μ ≤ ∫ u in a..b, f u ∂μ := by
  apply integral_antimono_of_le hab _ hg hfg
  have : ∀ᵐ t ∂μ.restrict <| Ι a b, 0 ≤ f t ∧ f t ≤ g t := hfnonneg.and hfg
  apply intervalIntegrable_of_nonneg_of_le hf this hg

end intervalIntegral

section

open intervalIntegral

theorem norm_intervalIntegral_eq (f : ℝ → E) (a b : ℝ) (μ : Measure ℝ) :
    ‖∫ x in a..b, f x ∂μ‖ = ‖∫ x in Ι a b, f x ∂μ‖ := by
  simp_rw [intervalIntegral_eq_integral_uIoc, norm_smul]
  split_ifs <;> simp only [norm_neg, norm_one, one_mul]

end

theorem abs_intervalIntegral_eq (f : ℝ → ℝ) (a b : ℝ) (μ : Measure ℝ) :
    |∫ x in a..b, f x ∂μ| = |∫ x in Ι a b, f x ∂μ| :=
  norm_intervalIntegral_eq f a b μ

-- not ported
theorem intervalIntegrable_of_norm_sub_le {β : Type*} [NormedAddCommGroup β] {f₀ f₁ : ℝ → β}
    {g : ℝ → ℝ} {a b : ℝ} (hf₁_m : AEStronglyMeasurable f₁ (μ.restrict <| Ι a b))
    (hf₀_i : IntervalIntegrable f₀ μ a b) (hg_i : IntervalIntegrable g μ a b)
    (h : ∀ᵐ a ∂μ.restrict <| Ι a b, ‖f₀ a - f₁ a‖ ≤ g a) : IntervalIntegrable f₁ μ a b :=
  haveI : ∀ᵐ a ∂μ.restrict <| Ι a b, ‖f₁ a‖ ≤ ‖f₀ a‖ + g a := by
    apply h.mono
    intro a ha
    calc
      ‖f₁ a‖ ≤ ‖f₀ a‖ + ‖f₀ a - f₁ a‖ := norm_le_insert _ _
      _ ≤ ‖f₀ a‖ + g a := add_le_add_left ha _
  (hf₀_i.norm.add hg_i).mono_fun' hf₁_m this

end

-- section
-- variables {E : Type*} [normed_add_comm_group E] [normed_space ℝ E] [complete_space E]
-- open interval_integral
-- lemma integral_comp_add_right' {f : ℝ → E} (a b : ℝ) :
--   ∫ t in a..(b + a), f t = ∫ t in 0..b, f (t + a) :=
-- by simp [← integral_comp_add_right]
-- lemma integral_comp_add_left' {f : ℝ → E} (a b : ℝ) :
--   ∫ t in a..(a + b), f t = ∫ t in 0..b, f (t + a) :=
-- by simp [← integral_comp_add_left, add_comm]
-- end
