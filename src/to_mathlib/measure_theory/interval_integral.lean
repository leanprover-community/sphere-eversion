import measure_theory.integral.interval_integral

import to_mathlib.measure_theory.basic
import to_mathlib.misc

noncomputable theory

open topological_space measure_theory filter first_countable_topology metric set function
open_locale topological_space filter nnreal big_operators interval

namespace continuous_linear_map

open interval_integral
variables {α 𝕜 E H F : Type*}
variables [measurable_space α] [is_R_or_C 𝕜] {μ : measure α}
variables [measurable_space E] [normed_group E] [normed_space 𝕜 E] [borel_space E]
variables [second_countable_topology E] [complete_space E]
variables [normed_space ℝ E] [is_scalar_tower ℝ 𝕜 E]
variables [measurable_space F] [normed_group F] [normed_space 𝕜 F] [borel_space F]
variables [second_countable_topology F] [complete_space F]
variables [normed_space ℝ F] [is_scalar_tower ℝ 𝕜 F]
variables [normed_group H] [normed_space 𝕜 H] [second_countable_topology (H →L[𝕜] E)]

variables [linear_order α]

lemma interval_integral_apply {a b : α} {φ : α → H →L[𝕜] E} (φ_int : interval_integrable φ μ a b)
  (v : H) : (∫ a in a..b, φ a ∂μ) v = ∫ a in a..b, φ a v ∂μ :=
by simp_rw [interval_integral_eq_integral_interval_oc, ← integral_apply φ_int.def v,
  continuous_linear_map.coe_smul', pi.smul_apply]

end continuous_linear_map

section

variables {α E : Type*} [linear_order α] [measurable_space α]
  [measurable_space E] [normed_group E] [opens_measurable_space E]

lemma interval_integrable_norm_iff {f : α → E} {μ : measure α} {a b : α}
  (hf : ae_measurable f (μ.restrict (Ι a b))) :
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

lemma interval_integrable_of_nonneg_of_le {f g : α → ℝ} {μ : measure α} {a b : α}
  (hf : ae_measurable f $ μ.restrict (Ι a b))
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

lemma interval_integrable_of_norm_le {f : α → E} {bound : α → ℝ} {μ : measure α} {a b : α}
  (hf : ae_measurable f $ μ.restrict (Ι a b))
  (h : ∀ᵐ t ∂(μ.restrict $ Ι a b), ∥f t∥ ≤ bound t) (hbound : interval_integrable bound μ a b) :
  interval_integrable f μ a b :=
begin
  rw ← interval_integrable_norm_iff hf,
  apply interval_integrable_of_nonneg_of_le hf.norm (h.mono _) hbound,
  simp,
end

variables [second_countable_topology E]
  [complete_space E] [normed_space ℝ E] [borel_space E] {a b : α} {f : α → E} {bound : α → ℝ}
  {μ : measure α}

namespace interval_integral

lemma integral_mono_of_le {α : Type*} [linear_order α] [measurable_space α]
  {f g : α → ℝ} {a b : α} {μ : measure α} (hab : a ≤ b)
  (hf : interval_integrable f μ a b)
  (hg : interval_integrable g μ a b)
  (hfg : f ≤ᵐ[μ.restrict (Ι a b)] g) :
  ∫ u in a..b, f u ∂μ ≤ ∫ u in a..b, g u ∂μ :=
begin
  rw interval_oc_of_le hab at hfg,
  let H := hfg.filter_mono (ae_mono le_rfl),
  simpa only [integral_of_le hab] using set_integral_mono_ae_restrict hf.1 hg.1 H
end

lemma integral_mono_of_le_of_nonneg {α : Type*} [linear_order α] [measurable_space α]
  {f g : α → ℝ} {a b : α} {μ : measure α} (hab : a ≤ b)
  (hf : ae_measurable f $ μ.restrict (Ι a b))
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

lemma integral_antimono_of_le {α : Type*} [linear_order α] [measurable_space α]
  {f g : α → ℝ} {a b : α} {μ : measure α} (hab : b ≤ a)
  (hf : interval_integrable f μ a b)
  (hg : interval_integrable g μ a b)
  (hfg : f ≤ᵐ[μ.restrict (Ι a b)] g) :
  ∫ u in a..b, g u ∂μ ≤ ∫ u in a..b, f u ∂μ :=
begin
  cases eq_or_lt_of_le hab with hab hab,
  { simp [hab] },
  { rw interval_oc_of_lt hab at hfg,
    rw integral_symm b a,
    rw integral_symm b a,
    apply neg_le_neg,
    apply integral_mono_of_le hab.le hf.symm hg.symm,
    rwa [interval_oc_comm, interval_oc_of_lt hab] }
end

lemma integral_antimono_of_le_of_nonneg {α : Type*} [linear_order α] [measurable_space α]
  {f g : α → ℝ} {a b : α} {μ : measure α} (hab : b ≤ a)
  (hf : ae_measurable f $ μ.restrict (Ι a b))
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
lemma interval_integrable.mono_set' {α E : Type*} [linear_order α] [measurable_space α]
  [measurable_space E] [normed_group E] {f : α → E} {a b c d : α} {μ : measure α}
  (hf : interval_integrable f μ a b) (hsub : Ι c d ⊆ Ι a b) : interval_integrable f μ c d :=
interval_integrable_iff.mpr (hf.def.mono hsub le_rfl)

lemma interval_integrable.const_mul {α : Type*} [linear_order α] [measurable_space α]
  {f : α → ℝ} {a b : α} {μ : measure α}
  (hf : interval_integrable f μ a b) (c : ℝ) : interval_integrable (λ x, c*f x) μ a b :=
begin
  rw interval_integrable_iff at *,
  exact hf.const_mul c
end

lemma interval_integrable.mul_const {α : Type*} [linear_order α] [measurable_space α]
  {f : α → ℝ} {a b : α} {μ : measure α}
  (hf : interval_integrable f μ a b) (c : ℝ) : interval_integrable (λ x, (f x)*c) μ a b :=
begin
  rw interval_integrable_iff at *,
  exact hf.mul_const c
end

lemma interval_integral.const_mul {α : Type*} [linear_order α] [measurable_space α]
  {f : α → ℝ} {a b : α} {μ : measure α} (c : ℝ) : ∫ x in a..b, c*f x ∂μ = c*∫ x in a..b, f x ∂μ :=
begin
  erw mul_sub,
  simpa only [← integral_mul_left]
end

lemma interval_integral.mul_const {α : Type*} [linear_order α] [measurable_space α]
  {f : α → ℝ} {a b : α} {μ : measure α} (c : ℝ) :
  ∫ x in a..b, f x * c ∂μ = (∫ x in a..b, f x ∂μ) * c :=
by simp_rw [mul_comm, ← interval_integral.const_mul]


lemma interval_integral.norm_integral_le_of_norm_le
  (h : ∀ᵐ t ∂(μ.restrict $ Ι a b), ∥f t∥ ≤ bound t)
  (hf : ae_measurable f (μ.restrict (Ι a b)) )
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

lemma interval_integrable_of_norm_sub_le {β : Type*} [normed_group β] [measurable_space β]
  [opens_measurable_space β]
  {f₀ f₁ : α → β} {g : α → ℝ}
  {a b : α}
  (hf₁_m : ae_measurable f₁ (μ.restrict $ Ι a b))
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

variables {E : Type*} [measurable_space E] [normed_group E] [normed_space ℝ E] [borel_space E]
          [second_countable_topology E] [complete_space E]

open interval_integral

lemma integral_comp_add_right' {f : ℝ → E} (a b : ℝ) :
  ∫ t in a..(b + a), f t = ∫ t in 0..b, f (t + a) :=
by simp [← integral_comp_add_right]

lemma integral_comp_add_left' {f : ℝ → E} (a b : ℝ) :
  ∫ t in a..(a + b), f t = ∫ t in 0..b, f (t + a) :=
by simp [← integral_comp_add_left, add_comm]

/- TODO : in interval_integral.integral_add_adjacent_intervals, turn the middle point into an
  explicit parameter so that we don't have to state integrability before rewriting.

  In the next lemma, the assumption on `f` is a bit lazy but we will need it only for continuous
  functions anyway.
  -/

lemma interval_integral_periodic {f : ℝ → E} {T : ℝ} (hf_per : periodic f T)
  (hf : ∀ s t, interval_integrable f volume s t)
  (a : ℝ) : ∫ t in a..(a + T), f t = ∫ t in 0..T, f t :=
begin
  rw [← interval_integral.integral_add_adjacent_intervals (hf a 0) (hf 0 $ a + T),
      ← interval_integral.integral_add_adjacent_intervals (hf 0 T) (hf T $ a+T),
      integral_comp_add_right',
      interval_integral.integral_symm, funext (λ t, hf_per t)],
  abel
end
end
