import measure_theory.integral.interval_integral
import measure_theory.integral.periodic

import to_mathlib.misc

noncomputable theory

open topological_space measure_theory filter first_countable_topology metric set function
open_locale topological_space filter nnreal big_operators interval

namespace continuous_linear_map

open interval_integral
variables {𝕜 E H F : Type*}
variables [is_R_or_C 𝕜] {μ : measure ℝ}
variables [normed_add_comm_group E] [normed_space 𝕜 E] [complete_space E]
variables [normed_space ℝ E] [is_scalar_tower ℝ 𝕜 E]
variables [normed_add_comm_group F] [normed_space 𝕜 F] [complete_space F]
variables [normed_space ℝ F] [is_scalar_tower ℝ 𝕜 F]
variables [normed_add_comm_group H] [normed_space 𝕜 H]

lemma interval_integral_apply {a b : ℝ} {φ : ℝ → H →L[𝕜] E} (φ_int : interval_integrable φ μ a b)
  (v : H) : (∫ x in a..b, φ x ∂μ) v = ∫ x in a..b, φ x v ∂μ :=
by simp_rw [interval_integral_eq_integral_interval_oc, ← integral_apply φ_int.def v,
  continuous_linear_map.coe_smul', pi.smul_apply]

end continuous_linear_map

section

variables {E : Type*} [normed_add_comm_group E]

lemma interval_integrable_of_integral_ne_zero
  [complete_space E] [normed_space ℝ E] {a b : ℝ}
  {f : ℝ → E} {μ : measure ℝ} (h : ∫ x in a..b, f x ∂μ ≠ 0) :
  interval_integrable f μ a b :=
begin
  contrapose! h,
  exact interval_integral.integral_undef h,
end

lemma interval_integrable_norm_iff {f : ℝ → E} {μ : measure ℝ} {a b : ℝ}
  (hf : ae_strongly_measurable f (μ.restrict (Ι a b))) :
  interval_integrable (λ t, ∥f t∥) μ a b ↔ interval_integrable f μ a b :=
begin
  simp_rw [interval_integrable_iff, integrable_on],
  exact integrable_norm_iff hf
end

lemma interval_oc_comm {α : Type*} [linear_order α] (a b : α) : Ι a b = Ι b a :=
begin
  dsimp [interval_oc],
  rw [min_comm, max_comm]
end

lemma interval_integrable_of_nonneg_of_le {f g : ℝ → ℝ} {μ : measure ℝ} {a b : ℝ}
  (hf : ae_strongly_measurable f $ μ.restrict (Ι a b))
  (h : ∀ᵐ t ∂(μ.restrict $ Ι a b), 0 ≤ f t ∧ f t ≤ g t)
  (hg : interval_integrable g μ a b) :
  interval_integrable f μ a b :=
begin
  rw interval_integrable_iff at *,
  apply integrable.mono' hg hf (h.mono _),
  rintro t ⟨H, H'⟩,
  change abs ( f t) ≤ _,
  rwa abs_of_nonneg H
end

lemma interval_integrable_of_norm_le {f : ℝ → E} {bound : ℝ → ℝ} {μ : measure ℝ} {a b : ℝ}
  (hf : ae_strongly_measurable f $ μ.restrict (Ι a b))
  (h : ∀ᵐ t ∂(μ.restrict $ Ι a b), ∥f t∥ ≤ bound t) (hbound : interval_integrable bound μ a b) :
  interval_integrable f μ a b :=
hbound.mono_fun' hf h

variables
  [complete_space E] [normed_space ℝ E]  {a b : ℝ} {f : ℝ → E} {bound : ℝ → ℝ}
  {μ : measure ℝ}

namespace interval_integral

lemma integral_mono_of_le
  {f g : ℝ → ℝ} {a b : ℝ} {μ : measure ℝ} (hab : a ≤ b)
  (hf : interval_integrable f μ a b)
  (hg : interval_integrable g μ a b)
  (hfg : f ≤ᵐ[μ.restrict (Ι a b)] g) :
  ∫ u in a..b, f u ∂μ ≤ ∫ u in a..b, g u ∂μ :=
begin
  rw interval_oc_of_le hab at hfg,
  let H := hfg.filter_mono (ae_mono le_rfl),
  simpa only [integral_of_le hab] using set_integral_mono_ae_restrict hf.1 hg.1 H
end

lemma integral_mono_of_le_of_nonneg
  {f g : ℝ → ℝ} {a b : ℝ} {μ : measure ℝ} (hab : a ≤ b)
  (hf : ae_strongly_measurable f $ μ.restrict (Ι a b))
  (hfnonneg : ∀ᵐ t ∂(μ.restrict $ Ι a b), 0 ≤ f t)
  (hg : interval_integrable g μ a b)
  (hfg : f ≤ᵐ[μ.restrict (Ι a b)] g) :
  ∫ u in a..b, f u ∂μ ≤ ∫ u in a..b, g u ∂μ :=
begin
  apply integral_mono_of_le hab _ hg hfg,
  have : ∀ᵐ t ∂(μ.restrict $ Ι a b), 0 ≤ f t ∧ f t ≤ g t,
  from hfnonneg.and hfg,
  apply interval_integrable_of_nonneg_of_le hf this hg,
end

lemma integral_antimono_of_le
  {f g : ℝ → ℝ} {a b : ℝ} {μ : measure ℝ} (hab : b ≤ a)
  (hf : interval_integrable f μ a b)
  (hg : interval_integrable g μ a b)
  (hfg : f ≤ᵐ[μ.restrict (Ι a b)] g) :
  ∫ u in a..b, g u ∂μ ≤ ∫ u in a..b, f u ∂μ :=
begin
  cases hab.eq_or_lt with hab hab,
  { simp [hab] },
  { rw interval_oc_of_lt hab at hfg,
    rw integral_symm b a,
    rw integral_symm b a,
    apply neg_le_neg,
    apply integral_mono_of_le hab.le hf.symm hg.symm,
    rwa [interval_oc_comm, interval_oc_of_lt hab] }
end

lemma integral_antimono_of_le_of_nonneg
  {f g : ℝ → ℝ} {a b : ℝ} {μ : measure ℝ} (hab : b ≤ a)
  (hf : ae_strongly_measurable f $ μ.restrict (Ι a b))
  (hfnonneg : ∀ᵐ t ∂(μ.restrict $ Ι a b), 0 ≤ f t)
  (hg : interval_integrable g μ a b)
  (hfg : f ≤ᵐ[μ.restrict (Ι a b)] g) :
  ∫ u in a..b, g u ∂μ ≤ ∫ u in a..b, f u ∂μ :=
begin
  apply integral_antimono_of_le hab _ hg hfg,
  have : ∀ᵐ t ∂(μ.restrict $ Ι a b), 0 ≤ f t ∧ f t ≤ g t,
  from hfnonneg.and hfg,
  apply interval_integrable_of_nonneg_of_le hf this hg,
end
end interval_integral

/- This should replace interval_integrable.mono_set in mathlib -/
lemma interval_integrable.mono_set' {E : Type*}
  [normed_add_comm_group E] {f : ℝ → E} {a b c d : ℝ} {μ : measure ℝ}
  (hf : interval_integrable f μ a b) (hsub : Ι c d ⊆ Ι a b) : interval_integrable f μ c d :=
hf.mono_set_ae $ eventually_of_forall hsub

lemma interval_integrable.const_mul
  {f : ℝ → ℝ} {a b : ℝ} {μ : measure ℝ}
  (hf : interval_integrable f μ a b) (c : ℝ) : interval_integrable (λ x, c * f x) μ a b :=
begin
  rw interval_integrable_iff at *,
  exact hf.const_mul c
end

lemma interval_integrable.mul_const
  {f : ℝ → ℝ} {a b : ℝ} {μ : measure ℝ}
  (hf : interval_integrable f μ a b) (c : ℝ) : interval_integrable (λ x, (f x)*c) μ a b :=
begin
  rw interval_integrable_iff at *,
  exact hf.mul_const c
end

lemma interval_integral.const_mul
  {f : ℝ → ℝ} {a b : ℝ} {μ : measure ℝ} (c : ℝ) : ∫ x in a..b, c*f x ∂μ = c*∫ x in a..b, f x ∂μ :=
begin
  erw mul_sub,
  simpa only [← integral_mul_left]
end

lemma interval_integral.mul_const
  {f : ℝ → ℝ} {a b : ℝ} {μ : measure ℝ} (c : ℝ) :
  ∫ x in a..b, f x * c ∂μ = (∫ x in a..b, f x ∂μ) * c :=
by simp_rw [mul_comm, ← interval_integral.const_mul]


lemma interval_integral.norm_integral_le_of_norm_le
  (h : ∀ᵐ t ∂(μ.restrict $ Ι a b), ∥f t∥ ≤ bound t)
  (hf : ae_strongly_measurable f (μ.restrict (Ι a b)) )
  (hbound : interval_integrable bound μ a b) :
  ∥∫ t in a..b, f t ∂μ∥ ≤ |∫ t in a..b, bound t ∂μ| :=
begin
  apply interval_integral.norm_integral_le_abs_integral_norm.trans,
  cases le_total a b with hab hab,
  { apply abs_le_abs_of_nonneg,
    { apply interval_integral.integral_nonneg_of_forall hab,
      exact λ t, norm_nonneg _ },
    apply interval_integral.integral_mono_of_le_of_nonneg hab hf.norm _ hbound h,
    simp },
  { apply abs_le_abs_of_nonpos,
    { rw [← neg_nonneg, ← interval_integral.integral_symm],
      apply interval_integral.integral_nonneg_of_forall hab,
      exact λ t, norm_nonneg _ },
    { apply interval_integral.integral_antimono_of_le_of_nonneg hab hf.norm _ hbound h,
      simp } }
end

lemma interval_integrable_of_norm_sub_le {β : Type*} [normed_add_comm_group β]
  {f₀ f₁ : ℝ → β} {g : ℝ → ℝ}
  {a b : ℝ}
  (hf₁_m : ae_strongly_measurable f₁ (μ.restrict $ Ι a b))
  (hf₀_i : interval_integrable f₀ μ a b)
  (hg_i : interval_integrable g μ a b)
  (h : ∀ᵐ a ∂(μ.restrict $ Ι a b), ∥f₀ a - f₁ a∥ ≤ g a) :
  interval_integrable f₁ μ a b :=
begin
  have : ∀ᵐ a ∂(μ.restrict $ Ι a b), ∥f₁ a∥ ≤ ∥f₀ a∥ + g a,
  { apply h.mono,
    intros a ha,
    calc ∥f₁ a∥ ≤ ∥f₀ a∥ + ∥f₀ a - f₁ a∥ : norm_le_insert _ _
    ... ≤ ∥f₀ a∥ + g a : add_le_add_left ha _ },
  exact interval_integrable_of_norm_le hf₁_m this (hf₀_i.norm.add hg_i)
end

end

section

variables {E : Type*} [normed_add_comm_group E] [normed_space ℝ E] [complete_space E]

open interval_integral

lemma integral_comp_add_right' {f : ℝ → E} (a b : ℝ) :
  ∫ t in a..(b + a), f t = ∫ t in 0..b, f (t + a) :=
by simp [← integral_comp_add_right]

lemma integral_comp_add_left' {f : ℝ → E} (a b : ℝ) :
  ∫ t in a..(a + b), f t = ∫ t in 0..b, f (t + a) :=
by simp [← integral_comp_add_left, add_comm]

end
