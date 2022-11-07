import measure_theory.integral.interval_integral
import measure_theory.integral.periodic

noncomputable theory

open topological_space measure_theory filter first_countable_topology metric set function
open_locale topological_space filter nnreal big_operators interval

section

variables {E : Type*} [normed_add_comm_group E]

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
--   interval_integrable (λ t, ∥f t∥) μ a b ↔ interval_integrable f μ a b :=
-- begin
--   simp_rw [interval_integrable_iff, integrable_on],
--   exact integrable_norm_iff hf
-- end

-- not ported
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

variables
  [complete_space E] [normed_space ℝ E]  {a b : ℝ} {f : ℝ → E} {bound : ℝ → ℝ}
  {μ : measure ℝ}

-- next 4 lemmas not ported (also unused)
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
    rwa [interval_oc_swap, interval_oc_of_lt hab] }
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

section
open interval_integral
lemma norm_interval_integral_eq (f : ℝ → E) (a b : ℝ) (μ : measure ℝ) :
  ∥∫ x in a..b, f x ∂μ∥ = ∥∫ x in Ι a b, f x ∂μ∥ :=
begin
  simp_rw [interval_integral_eq_integral_interval_oc, norm_smul],
  split_ifs; simp only [norm_neg, norm_one, one_mul],
end
end

lemma abs_interval_integral_eq (f : ℝ → ℝ) (a b : ℝ) (μ : measure ℝ) :
  |∫ x in a..b, f x ∂μ| = |∫ x in Ι a b, f x ∂μ| :=
norm_interval_integral_eq f a b μ

-- not ported
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
  exact (hf₀_i.norm.add hg_i).mono_fun' hf₁_m this
end

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
