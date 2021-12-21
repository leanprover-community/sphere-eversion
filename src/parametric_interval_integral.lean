import measure_theory.integral.interval_integral
import analysis.calculus.parametric_integral
import algebra.module.ulift

import to_mathlib.calculus
import to_mathlib.measure_theory
import to_mathlib.topology.metric_space
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
variables {E : Type*} [normed_group E] [second_countable_topology E] [normed_space ℝ E]
  [complete_space E] [measurable_space E] [borel_space E]
  {H : Type*} [normed_group H] [normed_space ℝ H]
  [second_countable_topology $ H →L[ℝ] E]
  [borel_space $ H →L[ℝ] E]
  (ν : measure ℝ)

/-- Interval version of `has_fderiv_at_of_dominated_of_fderiv_le` -/
lemma has_fderiv_at_of_dominated_of_fderiv_le'' {F : H → ℝ → E} {F' : H → ℝ → (H →L[ℝ] E)} {x₀ : H}
  {a b : ℝ}
  {bound : ℝ → ℝ}
  {ε : ℝ}
  (ε_pos : 0 < ε)
  (hF_meas : ∀ᶠ x in 𝓝 x₀, ae_measurable (F x) $ ν.restrict (Ι a b))
  (hF_int : interval_integrable (F x₀) ν a b)
  (hF'_meas : ae_measurable (F' x₀) $ ν.restrict (Ι a b))
  (h_bound : ∀ᵐ t ∂ν, t ∈ Ι a b → ∀ x ∈ ball x₀ ε, ∥F' x t∥ ≤ bound t)
  (bound_integrable : interval_integrable bound ν a b)
  (h_diff : ∀ᵐ t ∂ν, t ∈ Ι a b → ∀ x ∈ ball x₀ ε, has_fderiv_at (λ x, F x t) (F' x t) x) :
  has_fderiv_at (λ x, ∫ t in a..b, F x t ∂ν) (∫ t in a..b, F' x₀ t ∂ν) x₀ :=
begin
  erw ae_interval_oc_iff' at h_diff h_bound,
  simp_rw [ae_measurable_interval_oc_iff, eventually_and] at hF_meas hF'_meas,
  exact (has_fderiv_at_integral_of_dominated_of_fderiv_le ε_pos hF_meas.1 hF_int.1 hF'_meas.1 h_bound.1
         bound_integrable.1 h_diff.1).sub
        (has_fderiv_at_integral_of_dominated_of_fderiv_le ε_pos hF_meas.2 hF_int.2 hF'_meas.2 h_bound.2
         bound_integrable.2 h_diff.2)
end



/-- Interval version of `has_fderiv_at_of_dominated_loc_of_lip` -/
lemma has_fderiv_at_of_dominated_loc_of_lip_interval {F : H → ℝ → E} {F' : ℝ → (H →L[ℝ] E)} {x₀ : H}
  {a b : ℝ}
  {bound : ℝ → ℝ}
  {ε : ℝ} (ε_pos : 0 < ε)
  (hF_meas : ∀ᶠ x in 𝓝 x₀, ae_measurable (F x) $ ν.restrict (Ι a b))
  (hF_int : interval_integrable (F x₀) ν a b)
  (hF'_meas : ae_measurable F' $ ν.restrict (Ι a b))
  (h_lip : ∀ᵐ t ∂(ν.restrict (Ι a b)),
    lipschitz_on_with (real.nnabs $ bound t) (λ x, F x t) (ball x₀ ε))
  (bound_integrable : interval_integrable bound ν a b)
  (h_diff : ∀ᵐ t ∂(ν.restrict (Ι a b)), has_fderiv_at (λ x, F x t) (F' t) x₀) :
  interval_integrable F' ν a b ∧
  has_fderiv_at (λ x, ∫ t in a..b, F x t ∂ν) (∫ t in a..b, F' t ∂ν) x₀ :=
begin
  simp_rw [ae_measurable_interval_oc_iff, eventually_and] at hF_meas hF'_meas,
  rw ae_interval_oc at h_lip h_diff,
  have H₁ := has_fderiv_at_integral_of_dominated_loc_of_lip ε_pos hF_meas.1 hF_int.1 hF'_meas.1
    h_lip.1 bound_integrable.1 h_diff.1,
  have H₂ := has_fderiv_at_integral_of_dominated_loc_of_lip ε_pos hF_meas.2 hF_int.2 hF'_meas.2
    h_lip.2 bound_integrable.2 h_diff.2,
  exact ⟨⟨H₁.1, H₂.1⟩, H₁.2.sub H₂.2⟩
end

end

section

open function

theorem continuous_parametric_integral_of_continuous
  {E : Type*} [normed_group E] [topological_space.second_countable_topology E] [normed_space ℝ E]
  [complete_space E] [measurable_space E] [borel_space E]
  {α : Type*} [topological_space α] [measurable_space α] [opens_measurable_space α]
  {μ : measure_theory.measure α} [is_locally_finite_measure μ]
  {X : Type*} [topological_space X] [first_countable_topology X] [locally_compact_space X]
  {F : X → α → E} (hF : continuous (λ p : X × α, F p.1 p.2))
  {s : set α} (hs : is_compact s) (hs' : measurable_set s):
  continuous (λ x, ∫ a in s, F x a ∂μ) :=
begin
  rw continuous_iff_continuous_at,
  intros x₀,
  rcases exists_compact_mem_nhds x₀ with ⟨U, U_cpct, U_nhds⟩,
  rcases (U_cpct.prod hs).bdd_above_norm hF with ⟨M, M_pos, hM⟩,
  apply continuous_at_of_dominated,
  { exact eventually_of_forall (λ x, (hF.comp (continuous.prod.mk x)).ae_measurable _) },
  { apply eventually.mono U_nhds (λ x x_in, _),
    apply ae_restrict_of_forall_mem hs',
    intros t t_in,
    exact hM (x, t) (set.mk_mem_prod x_in t_in) },
  { apply hs.integrable_const },
  { apply ae_of_all,
    intros a,
    apply (hF.comp $ continuous_id.prod_mk continuous_const).continuous_at }
end

end

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

open measure_theory

variables {α : Type*} [linear_order α] [measurable_space α] [topological_space α]
          [order_topology α] [opens_measurable_space α] [first_countable_topology α] {μ : measure α}
          {X : Type*} [topological_space X] [first_countable_topology X]
          {E : Type*} [measurable_space E] [normed_group E] [normed_space ℝ E] [borel_space E]
          [second_countable_topology E] [complete_space E]

lemma continuous_at_parametric_primitive_of_dominated
  {F : X → α → E} (bound : α → ℝ) (a b : α) {a₀ b₀ : α} {x₀ : X}
  (hF_meas : ∀ x, ae_measurable (F x) (μ.restrict $ Ι a b))
  (h_bound : ∀ᶠ x in 𝓝 x₀, ∀ᵐ t ∂(μ.restrict $ Ι a b), ∥F x t∥ ≤ bound t)
  (bound_integrable : interval_integrable bound μ a b)
  (h_cont : ∀ᵐ t ∂(μ.restrict $ Ι a b), continuous_at (λ x, F x t) x₀)
  (ha₀ : a₀ ∈ Ioo a b) (hb₀ : b₀ ∈ Ioo a b) (hμb₀ : μ {b₀} = 0) :
  continuous_at (λ p : X × α, ∫ (t : α) in a₀..p.2, F p.1 t ∂μ) (x₀, b₀) :=
begin
  have hsub₀ : Ι a₀ b₀ ⊆ Ι a b, from
    interval_oc_subset_of_mem_Ioc (mem_Ioc_of_Ioo ha₀) (mem_Ioc_of_Ioo hb₀),
  have Ioo_nhds : Ioo a b ∈ 𝓝 b₀, from Ioo_mem_nhds hb₀.1 hb₀.2,
  have Icc_nhds : Icc a b ∈ 𝓝 b₀, from Icc_mem_nhds hb₀.1 hb₀.2,
  have hx₀ : ∀ᵐ (t : α) ∂μ.restrict (Ι a b), ∥F x₀ t∥ ≤ bound t := (mem_of_mem_nhds h_bound : _),
  have : ∀ᶠ (p : X × α) in 𝓝 (x₀, b₀),
    ∫ s in a₀..p.2, F p.1 s ∂μ = ∫ s in a₀..b₀, F p.1 s ∂μ + ∫ s in b₀..p.2, F x₀ s ∂μ +
                                 ∫ s in b₀..p.2, (F p.1 s - F x₀ s) ∂μ,
  { rw nhds_prod_eq,
    apply mem_of_superset (prod_mem_prod h_bound Ioo_nhds),
    rintros ⟨x, t⟩ ⟨hx : ∀ᵐ (t : α) ∂μ.restrict (Ι a b), ∥F x t∥ ≤ bound t, ht : t ∈ Ioo a b⟩,
    dsimp {eta := ff},
    rw [interval_integral.integral_sub, add_assoc, add_sub_cancel'_right,
        interval_integral.integral_add_adjacent_intervals],
    { exact interval_integrable_of_norm_le ((hF_meas x).mono_set hsub₀)
            (ae_restrict_of_ae_restrict_of_subset hsub₀ hx)
            (bound_integrable.mono_set' hsub₀) },
    all_goals {
      have hsub : Ι b₀ t ⊆ Ι a b, from
        interval_oc_subset_of_mem_Ioc (mem_Ioc_of_Ioo hb₀) (mem_Ioc_of_Ioo ht),
      exact interval_integrable_of_norm_le ((hF_meas _).mono_set hsub)
            (ae_restrict_of_ae_restrict_of_subset hsub ‹_›) (bound_integrable.mono_set' hsub) } },
  rw continuous_at_congr this, clear this,
  refine continuous_at.add (continuous_at.add _ _) _,
  { change continuous_at ((λ x, ∫ (s : α) in a₀..b₀, F x s ∂μ) ∘ prod.fst) (x₀, b₀),
    apply continuous_at.comp _ continuous_at_fst,
    apply interval_integral.continuous_at_of_dominated_interval
            (eventually_of_forall $ λ x, (hF_meas x).mono_set hsub₀)
            (h_bound.mono $ λ  x, ae_mem_imp_of_ae_restrict_of_subset hsub₀)
            (bound_integrable.mono_set' hsub₀)
            (ae_mem_imp_of_ae_restrict_of_subset hsub₀ h_cont) },
  { change continuous_at ((λ t, ∫ (s : α) in b₀..t, F x₀ s ∂μ) ∘ prod.snd) (x₀, b₀),
    apply continuous_at.comp _ continuous_at_snd,
    apply continuous_within_at.continuous_at _ (Icc_mem_nhds hb₀.1 hb₀.2),
    apply interval_integral.continuous_within_at_primitive hμb₀,
    rw [min_eq_right hb₀.1.le, max_eq_right hb₀.2.le],
    exact interval_integrable_of_norm_le (hF_meas x₀) hx₀ bound_integrable },
  { suffices : tendsto (λ (x : X × α), ∫ s in b₀..x.2, F x.1 s - F x₀ s ∂μ) (𝓝 (x₀, b₀)) (𝓝 0),
      by simpa [continuous_at],
    have : ∀ᶠ p : X × α in 𝓝 (x₀, b₀),
      ∥∫ s in b₀..p.2, F p.1 s - F x₀ s ∂μ∥ ≤ |∫ (s : α) in b₀..p.2, 2* bound s ∂μ|,
    { rw nhds_prod_eq,
      apply mem_of_superset (prod_mem_prod h_bound Ioo_nhds),
      rintros ⟨x, t⟩ ⟨hx : ∀ᵐ t ∂μ.restrict (Ι a b), ∥F x t∥ ≤ bound t, ht : t ∈ Ioo a b⟩,
      have hsub : Ι b₀ t ⊆ Ι a b, from
        interval_oc_subset_of_mem_Ioc (mem_Ioc_of_Ioo hb₀) (mem_Ioc_of_Ioo ht),
      have H : ∀ᵐ (t : α) ∂μ.restrict (Ι b₀ t), ∥F x t - F x₀ t∥ ≤ 2*bound t,
      { apply (ae_restrict_of_ae_restrict_of_subset hsub (hx.and hx₀)).mono,
        rintros s ⟨hs₁, hs₂⟩,
        calc ∥F x s - F x₀ s∥ ≤ ∥F x s∥ + ∥F x₀ s∥ : norm_sub_le _ _
        ... ≤ 2 * bound s : by linarith only [hs₁, hs₂] },
      exact interval_integral.norm_integral_le_of_norm_le H
        (((hF_meas x).mono_set hsub).sub ((hF_meas x₀).mono_set hsub))
        ((bound_integrable.mono_set' hsub).const_mul 2) },
    apply squeeze_zero_norm' this,
    have : tendsto (λ t, ∫ (s : α) in b₀..t, 2 * bound s ∂μ) (𝓝 b₀) (𝓝 0),
    { suffices : continuous_at (λ t, ∫ (s : α) in b₀..t, 2 * bound s ∂μ) b₀,
      { convert this,
        simp },
      apply continuous_within_at.continuous_at _ Icc_nhds,
      apply interval_integral.continuous_within_at_primitive hμb₀,
      apply interval_integrable.const_mul,
      apply bound_integrable.mono_set',
      rw [min_eq_right hb₀.1.le, max_eq_right hb₀.2.le] },
    change tendsto (abs ∘ (λ t, ∫ (s : α) in b₀..t, 2*bound s ∂μ) ∘ prod.snd) (𝓝 (x₀, b₀)) _,
    have lim_abs : tendsto abs (𝓝 (0 : ℝ)) (𝓝 0),
    { conv { congr, skip, skip, rw ← abs_zero },
      exact continuous_abs.continuous_at },
    apply lim_abs.comp (this.comp _),
    rw nhds_prod_eq, apply tendsto_snd },
end
end

section
variables {α : Type*} [conditionally_complete_linear_order α] [no_bot_order α] [no_top_order α]
          [measurable_space α] [topological_space α]
          [order_topology α] [opens_measurable_space α] [first_countable_topology α] {μ : measure α}
          [is_locally_finite_measure μ] [has_no_atoms μ]
          {X : Type*} [topological_space X] [first_countable_topology X]
          {E : Type*} [measurable_space E] [normed_group E] [normed_space ℝ E] [borel_space E]
          [second_countable_topology E] [complete_space E]

lemma continuous_parametric_primitive_of_continuous
  [locally_compact_space X]
  {F : X → α → E} {a₀ : α}
  (hF : continuous (λ p : X × α, F p.1 p.2)) :
  continuous (λ p : X × α, ∫ t in a₀..p.2, F p.1 t ∂μ) :=
begin
  rw continuous_iff_continuous_at,
  rintros ⟨x₀, b₀⟩,
  rcases exists_compact_mem_nhds x₀ with ⟨U, U_cpct, U_nhds⟩,
  cases no_bot (min a₀ b₀) with a a_lt,
  cases no_top (max a₀ b₀) with b lt_b,
  rw lt_min_iff at a_lt,
  rw max_lt_iff at lt_b,
  have a₀_in : a₀ ∈ Ioo a b := ⟨a_lt.1, lt_b.1⟩,
  have b₀_in : b₀ ∈ Ioo a b := ⟨a_lt.2, lt_b.2⟩,
  obtain ⟨M : ℝ, M_pos : M > 0,
          hM : ∀ (x : X × α), x ∈ U.prod (Icc a b) → ∥(λ (p : X × α), F p.fst p.snd) x∥ ≤ M⟩ :=
    (U_cpct.prod (is_compact_Icc : is_compact $ Icc a b)).bdd_above_norm hF,
  refine continuous_at_parametric_primitive_of_dominated (λ t, M) a b _ _ _ _ a₀_in b₀_in
    (measure_singleton b₀),
  { intro x,
    apply (hF.comp (continuous.prod.mk x)).ae_measurable _ },
  { apply eventually.mono U_nhds (λ x (x_in : x ∈ U), _),
    refine ae_restrict_of_forall_mem measurable_set_Ioc _,
    intros t t_in,
    refine hM (x, t) ⟨x_in, (_ : t ∈ Icc a b)⟩,
    rw interval_oc_of_le (a_lt.1.trans lt_b.1).le at t_in,
    exact mem_Icc_of_Ioc t_in },
  { apply interval_integrable_const },
  { apply ae_of_all,
    intros a,
    apply (hF.comp $ continuous_id.prod_mk continuous_const).continuous_at }
end

theorem continuous_parametric_interval_integral_of_continuous
  [locally_compact_space X] {a₀ : α}
  {F : X → α → E} (hF : continuous (λ p : X × α, F p.1 p.2))
  {s : X → α} (hs : continuous s) :
  continuous (λ x, ∫ t in a₀..s x, F x t ∂μ) :=
show continuous ((λ p : X × α, ∫ t in a₀..p.2, F p.1 t ∂μ) ∘ (λ x, (x, s x))),
from (continuous_parametric_primitive_of_continuous hF).comp (continuous_id.prod_mk hs)

theorem continuous_parametric_interval_integral_of_continuous'
  [locally_compact_space X]
  {F : X → α → E} (hF : continuous (λ p : X × α, F p.1 p.2)) (a₀ b₀ : α) :
  continuous (λ x, ∫ t in a₀..b₀, F x t ∂μ) :=
continuous_parametric_interval_integral_of_continuous hF continuous_const


end


section
variables {E : Type*} [normed_group E] [normed_space ℝ E]
          [complete_space E] [second_countable_topology E]
          [measurable_space E] [borel_space E]
          {H : Type*} [normed_group H] [normed_space ℝ H]
          [finite_dimensional ℝ H]
/-!
We could weaken `finite_dimensional ℝ H` with `second_countable (H →L[ℝ] E)` if needed,
but that is less convenient to work with.
-/

open real continuous_linear_map asymptotics

/--
This statement is a new version using the continuity note in mathlib.
See commit `39e3f3f` for an older version
Maybe todo: let `a` depend on `x`.
-/
lemma has_fderiv_at_parametric_primitive_of_lip' (F : H → ℝ → E) (F' : ℝ → (H →L[ℝ] E)) {x₀ : H}
  {G' : H →L[ℝ] E}
  {bound : ℝ → ℝ}
  {s : H → ℝ}
  {ε : ℝ} (ε_pos : 0 < ε)
  {a a₀ b₀ : ℝ}
  {s' : H →L[ℝ] ℝ}
  (ha :  a ∈ Ioo a₀ b₀)
  (hsx₀ : s x₀ ∈ Ioo a₀ b₀)
  (hF_meas : ∀ x ∈ ball x₀ ε, ae_measurable (F x) (volume.restrict (Ioo a₀ b₀)))
  (hF_int : integrable_on (F x₀) (Ioo a₀ b₀))
  (hF_cont : continuous_at (F x₀) (s x₀))
  (hF'_meas : ae_measurable F' (volume.restrict $ Ι a (s x₀)))
  (h_lipsch : ∀ᵐ t ∂(volume.restrict $ Ioo a₀ b₀),
    lipschitz_on_with (nnabs $ bound t) (λ x, F x t) (ball x₀ ε))
  (bound_integrable : integrable_on bound (Ioo a₀ b₀))
  (bound_cont : continuous_at bound (s x₀))
  (bound_nonneg : ∀ t, 0 ≤ bound t) -- this is not really needed, but much more convenient
  (h_diff : ∀ᵐ a ∂volume.restrict (Ι a (s x₀)), has_fderiv_at (λ x, F x a) (F' a) x₀)
  (s_diff : has_fderiv_at s s' x₀)
  (hG' : (∫ t in a..s x₀, F' t) + (to_span_singleton ℝ (F x₀ (s x₀))).comp s' = G') :
  interval_integrable F' volume a (s x₀) ∧
  has_fderiv_at (λ x : H, ∫ t in a..s x, F x t) G' x₀ :=
begin
  subst hG',
  let φ : H → ℝ → E := λ x t, ∫ s in a..t, F x s,
  let ψ : H →L[ℝ] E := ∫ t in a..s x₀, F' t,
  have Ioo_nhds : Ioo a₀ b₀ ∈ 𝓝 (s x₀) := Ioo_mem_nhds hsx₀.1 hsx₀.2,
  have bound_int : ∀ {s u}, s ∈ Ioo a₀ b₀ → u ∈ Ioo a₀ b₀ → interval_integrable bound volume s u,
  { intros s u hs hu,
    exact (bound_integrable.mono_set $ interval_subset_Ioo hs hu).interval_integrable },
  have mem_nhds : ball x₀ ε ∩ (s ⁻¹' Ioo a₀ b₀) ∈ 𝓝 x₀ :=
  filter.inter_mem (ball_mem_nhds x₀ ε_pos) (s_diff.continuous_at.preimage_mem_nhds Ioo_nhds),
  have x₀_in : x₀ ∈ ball x₀ ε := mem_ball_self ε_pos,
  have hF_meas_ball : ∀ {x}, x ∈ ball x₀ ε → ∀ {s u}, s ∈ Ioo a₀ b₀ → u ∈ Ioo a₀ b₀ →
    ae_measurable (F x) (volume.restrict $ Ι s u),
  { intros x hx s u hs hu,
    exact (hF_meas x hx).mono_set (interval_oc_subset_Ioo hs hu) },
  have hF_int_ball : ∀ x ∈ ball x₀ ε, ∀ {s u}, s ∈ Ioo a₀ b₀ → u ∈ Ioo a₀ b₀ →
    interval_integrable (F x) volume s u,
  { intros x hx s u hs hu,
    have : integrable_on (F x) (Ioo a₀ b₀),
    { apply integrable_of_norm_sub_le (hF_meas x hx) hF_int (bound_integrable.mul_const (∥x - x₀∥)),
      apply h_lipsch.mono,
      intros t ht,
      rw norm_sub_rev,
      rw lipschitz_on_with_iff_norm_sub_le at ht,
      simpa [bound_nonneg t] using ht x hx x₀ x₀_in },
    exact (this.mono_set $ interval_subset_Ioo hs hu).interval_integrable },
  split,
  { apply interval_integrable_of_norm_le hF'_meas _ (bound_int ha hsx₀),
    replace h_lipsch : ∀ᵐ t ∂volume.restrict (Ι a (s x₀)),
      lipschitz_on_with (nnabs (bound t)) (λ (x : H), F x t) (ball x₀ ε),
      from ae_restrict_of_ae_restrict_of_subset (interval_oc_subset_Ioo ha hsx₀) h_lipsch,
    filter_upwards [h_lipsch, h_diff],
    intros t ht_lip ht_diff,
    rw show bound t = nnabs (bound t), by simp [bound_nonneg t],
    exact ht_diff.le_of_lip (ball_mem_nhds x₀ ε_pos) ht_lip },
  { have D₁ : has_fderiv_at (λ x, φ x (s x₀)) (∫ t in a..s x₀, F' t) x₀,
    { replace hF_meas : ∀ᶠ x in 𝓝 x₀, ae_measurable (F x) (volume.restrict (Ι a (s x₀))),
        from eventually.mono (ball_mem_nhds x₀ ε_pos) (λ x hx, hF_meas_ball hx ha hsx₀),
      replace hF_int : interval_integrable (F x₀) volume a (s x₀), from hF_int_ball x₀ x₀_in ha hsx₀,
      exact (has_fderiv_at_of_dominated_loc_of_lip_interval _ ε_pos hF_meas hF_int hF'_meas
              (ae_restrict_of_ae_restrict_of_subset (interval_oc_subset_Ioo ha hsx₀) h_lipsch)
              (bound_int ha hsx₀) h_diff).2 },
    have D₂ : has_fderiv_at (λ x, φ x₀ (s x)) ((to_span_singleton ℝ (F x₀ (s x₀))).comp s') x₀,
    { refine has_fderiv_at.comp _ _ s_diff,
      rw [has_fderiv_at_iff_has_deriv_at, to_span_singleton_apply, one_smul],
      exact interval_integral.integral_has_deriv_at_right (hF_int_ball x₀ x₀_in ha hsx₀)
        ⟨Ioo a₀ b₀, Ioo_nhds, (hF_meas x₀ x₀_in)⟩ hF_cont },
    have D₃ : has_fderiv_at (λ x, ∫ t in s x₀..s x, F x t - F x₀ t) 0 x₀,
    { apply is_O.has_fderiv_at _ one_lt_two,
      have O₁ : is_O (λ x, ∫ s in s x₀..s x, bound s) (λ x, ∥x - x₀∥) (𝓝 x₀),
      { have : is_O (λ x, s x - s x₀) (λ x, ∥x - x₀∥) (𝓝 x₀) := s_diff.is_O_sub.norm_right,
        refine is_O.trans _ this,
        show is_O ((λ t, ∫ s in s x₀..t, bound s) ∘ s) ((λ t, t - s x₀) ∘ s) (𝓝 x₀),
        refine is_O.comp_tendsto _ s_diff.continuous_at,
        have M : measurable_at_filter bound (𝓝 (s x₀)) volume,
        { use [Ioo a₀ b₀, Ioo_nhds, bound_integrable.1] },
        apply is_O.congr' _ eventually_eq.rfl
          (interval_integral.integral_has_deriv_at_right (bound_int ha hsx₀) M bound_cont).is_O,
        apply eventually.mono Ioo_nhds,
        rintros t ht,
        dsimp only {eta := false},
        rw interval_integral.integral_interval_sub_left (bound_int ha ht) (bound_int ha hsx₀) },
      have O₂ : is_O (λ x, ∥x - x₀∥) (λ x, ∥x - x₀∥) (𝓝 x₀), from is_O_refl _ _,
      have O₃ : is_O (λ x, ∫ (t : ℝ) in s x₀..s x, F x t - F x₀ t)
             (λ x, (∫ t' in s x₀..s x, bound t') * ∥x - x₀∥)
             (𝓝 x₀),
      { have bdd : ∀ᶠ x in 𝓝 x₀,
          ∥∫ s in s x₀..s x, F x s - F x₀ s∥ ≤ |∫ s in s x₀..s x, bound s |* ∥x - x₀∥,
        { apply eventually.mono mem_nhds,
          rintros x ⟨hx : x ∈ ball x₀ ε, hsx : s x ∈ Ioo a₀ b₀⟩,
          rw [← abs_of_nonneg (norm_nonneg $ x - x₀), ← abs_mul, ← interval_integral.mul_const],
          apply interval_integral.norm_integral_le_of_norm_le _ ((hF_meas_ball hx hsx₀ hsx).sub
            (hF_meas_ball x₀_in hsx₀ hsx))
            ((bound_int hsx₀ hsx).mul_const _),
          apply ae_restrict_of_ae_restrict_of_subset (interval_oc_subset_Ioo hsx₀ hsx),
          apply h_lipsch.mono,
          intros t ht,
          rw lipschitz_on_with_iff_norm_sub_le at ht,
          simp only [coe_nnabs] at ht,
          rw ← abs_of_nonneg (bound_nonneg t),
          exact ht x hx x₀ (mem_ball_self ε_pos) },
        rw ← is_O_norm_right,
        simp only [norm_eq_abs, abs_mul, abs_norm_eq_norm],
        exact bdd.is_O' },
      simp_rw pow_two,
      exact O₃.trans (O₁.mul O₂) },
    have : ∀ᶠ x in 𝓝 x₀, ∫ t in a..s x, F x t =
      φ x (s x₀) + φ x₀ (s x) + (∫ t in s x₀..s x, F x t - F x₀ t) - φ x₀ (s x₀),
    { apply eventually.mono mem_nhds,
      rintros x ⟨hx : x ∈ ball x₀ ε, hsx : s x ∈ Ioo a₀ b₀⟩,
      have int₁ : interval_integrable (F x₀) volume a (s x₀) := hF_int_ball x₀ x₀_in ha hsx₀,
      have int₂ : interval_integrable (F x₀) volume (s x₀) (s x) := hF_int_ball x₀ x₀_in hsx₀ hsx,
      have int₃ : interval_integrable (F x) volume a (s x₀) := hF_int_ball x hx ha hsx₀,
      have int₄ : interval_integrable (F x) volume (s x₀) (s x) := hF_int_ball x hx hsx₀ hsx,
      dsimp [φ] {eta := ff},
      rw [interval_integral.integral_sub int₄ int₂, add_sub,
          add_right_comm, sub_sub, interval_integral.integral_add_adjacent_intervals int₃ int₄],
      conv_rhs { congr, skip, rw add_comm },
      rw interval_integral.integral_add_adjacent_intervals int₁ int₂,
      abel },
    apply has_fderiv_at.congr_of_eventually_eq _ this,
    simpa using ((D₁.add D₂).add D₃).sub (has_fderiv_at_const (φ x₀ (s x₀)) x₀) }
end



local notation `D` := fderiv ℝ
local notation u ` ⬝ `:70 φ :=  continuous_linear_map.comp (continuous_linear_map.to_span_singleton ℝ u) φ
local notation `∂₁` := partial_fderiv_fst ℝ

/-
A version of the above lemma using Floris' style statement. This does not reuse the above lemma, but copies the proof.
-/

lemma has_fderiv_at_parametric_primitive_of_times_cont_diff' {F : H → ℝ → E} (hF : times_cont_diff ℝ 1 ↿F)
  {s : H → ℝ} (hs : times_cont_diff ℝ 1 s)
  (x₀ : H) (a : ℝ) :
  (interval_integrable (λ t, (fderiv ℝ $ λ x, F x t) x₀) volume a $ s x₀) ∧
  has_fderiv_at (λ x : H, ∫ t in a..s x, F x t)
    ((∫ t in a..s x₀, ∂₁F x₀ t) + (F x₀ (s x₀)) ⬝ (D s x₀))
    x₀ :=
begin
  set a₀ :=  min a (s x₀) - 1,
  set b₀ :=  max a (s x₀) + 1,
  have ha : a ∈ Ioo a₀ b₀,
  { dsimp [a₀, b₀],
    split,
    linarith [min_le_left a (s x₀)],
    linarith [le_max_left a (s x₀)] },
  have ht₀ : s x₀ ∈ Ioo a₀ b₀,
  { dsimp [a₀, b₀],
    split,
    linarith [min_le_right a (s x₀)],
    linarith [le_max_right a (s x₀)] },
  have cpct : is_compact ((closed_ball x₀ 1).prod $ Icc a₀ b₀),
      from (proper_space.is_compact_closed_ball x₀ 1).prod is_compact_Icc,
  obtain ⟨M, M_nonneg, F_bound⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ ball x₀ 1, ∀ t ∈ Ioo a₀ b₀, ∥F x t∥ ≤ M,
  { rcases cpct.bdd_above_norm hF.continuous with ⟨M, M_pos : 0 < M, hM⟩,
    use [M, M_pos.le],
    exact λ x x_in t t_in, hM (x, t) ⟨ball_subset_closed_ball x_in, mem_Icc_of_Ioo t_in⟩ },
  obtain ⟨K, F_lip⟩ : ∃ K, ∀ t ∈ Ioo a₀ b₀, lipschitz_on_with K (λ x, F x t) (ball x₀ 1),
  { have conv : convex ℝ ((closed_ball x₀ 1).prod $ Icc  a₀ b₀),
      from (convex_closed_ball x₀ 1).prod (convex_Icc a₀ b₀),
    rcases hF.lipschitz_on_with conv cpct with ⟨K, hK⟩,
    use K,
    intros t t_in,
    rw [show (λ (x : H), F x t) = (uncurry F) ∘ (λ x : H, (x, t)), by { ext, simp }, ← mul_one K],
    apply hK.comp ((lipschitz_with_prod_mk_right t).lipschitz_on_with $ ball x₀ 1),
    rintros ⟨x, s⟩ ⟨x', hx, h⟩, cases h,
    refine ⟨ball_subset_closed_ball hx, mem_Icc_of_Ioo t_in⟩ },
  have cont_x : ∀ x, continuous (F x),
    from λ x, hF.continuous.comp (continuous.prod.mk x),
  have int_Icc : ∀ x, integrable_on (F x) (Icc a₀ b₀),
    from λ x, (cont_x x).integrable_on_compact is_compact_Icc,
  have int_Ioo : ∀ x, integrable_on (F x) (Ioo a₀ b₀),
    from λ x, (int_Icc x).mono_set Ioo_subset_Icc_self,
  apply has_fderiv_at_parametric_primitive_of_lip' _ _ zero_lt_one ha ht₀
    (λ x hx, (cont_x x).ae_measurable _) (int_Ioo x₀) (cont_x x₀).continuous_at
    _ _ _ (continuous_at_const : continuous_at (λ (t : ℝ), (K : ℝ)) $ s x₀) (λ t, nnreal.coe_nonneg K),
  { apply ae_of_all,
    intro t,
    apply (times_cont_diff.has_strict_fderiv_at _ le_rfl).has_fderiv_at,
    rw show (λ x, F x t) = (uncurry F) ∘ (λ x, (x, t)), by { ext, simp },
    exact hF.comp ((times_cont_diff_prod_left t).of_le le_top) },
  { exact (times_cont_diff.has_strict_fderiv_at hs le_rfl).has_fderiv_at },
  { refl },
  { apply continuous.ae_measurable,
    have : (λ t, fderiv ℝ (λ (x : H), F x t) x₀) =
      ((λ φ : H × ℝ →L[ℝ] E, φ.comp (inl ℝ H ℝ)) ∘ (fderiv ℝ $ uncurry F) ∘ (λ t, (x₀, t))),
    { ext t,
      have : has_fderiv_at (λ e, F e t) ((fderiv ℝ (uncurry F) (x₀, t)).comp (inl ℝ H ℝ)) x₀,
        from has_fderiv_at.partial_fst (hF.has_strict_fderiv_at le_rfl).has_fderiv_at,
      rw [this.fderiv] },
    rw this, clear this,
    exact (inl ℝ H ℝ).comp_rightL.continuous.comp ((hF.continuous_fderiv le_rfl).comp $
      continuous.prod.mk x₀) },
  { refine ae_restrict_of_forall_mem measurable_set_Ioo _,
    swap,
    intros t t_in,
    rw nnabs_coe K,
    exact F_lip t t_in },
  { exact integrable_on_const.mpr (or.inr measure_Ioo_lt_top) }
end

end

section
universe variables u v
variables {E : Type (max u v)} [normed_group E] [normed_space ℝ E]
          [complete_space E] [second_countable_topology E]
          [measurable_space E] [borel_space E]
          {H : Type u} [normed_group H] [normed_space ℝ H]
          [finite_dimensional ℝ H]

open real continuous_linear_map asymptotics

local notation `D` := fderiv ℝ
local notation u ` ⬝ `:70 φ :=  continuous_linear_map.comp (continuous_linear_map.to_span_singleton ℝ u) φ
local notation `∂₁` := partial_fderiv_fst ℝ

/-- In this version the universe levels have a restriction.
Use `times_cont_diff_parametric_primitive_of_times_cont_diff'` instead. -/
lemma times_cont_diff_parametric_primitive_of_times_cont_diff'' {F : H → ℝ → E} {n : ℕ}
  (hF : times_cont_diff ℝ n ↿F)
  {s : H → ℝ} (hs : times_cont_diff ℝ n s)
  (a : ℝ) :
  times_cont_diff ℝ n (λ x : H, ∫ t in a..s x, F x t)  :=
begin
  tactic.unfreeze_local_instances,
  revert E F,
  induction n with n ih; introsI E F i₁ i₂ i₃ i₄ i₅ i₆ hF,
  { rw [with_top.coe_zero, times_cont_diff_zero] at *,
    exact continuous_parametric_interval_integral_of_continuous hF hs },
  { have hF₁ : times_cont_diff ℝ 1 (↿F), from hF.one_of_succ,
    have hs₁ : times_cont_diff ℝ 1 s, from hs.one_of_succ,
    rw times_cont_diff_succ_iff_fderiv,
    split,
    { exact λ x₀, ⟨_, (has_fderiv_at_parametric_primitive_of_times_cont_diff' hF₁ hs₁ x₀ a).2⟩ },
    { rw funext (λ x, (has_fderiv_at_parametric_primitive_of_times_cont_diff' hF₁ hs₁ x a).2.fderiv),
      apply times_cont_diff.add,
      { apply ih hs.of_succ,
        apply times_cont_diff.times_cont_diff_partial_fst,
        exact hF },
      { exact is_bounded_bilinear_map_smul_right.times_cont_diff.comp
          ((times_cont_diff_succ_iff_fderiv.mp hs).2.prod $ hF.of_succ.comp $ times_cont_diff_id.prod hs.of_succ) } } }
end

end

section

universe variables v u

variables {E : Type u}

-- set_option pp.universes true
-- note: we can almost certainly remove all `.{v}` below
open ulift

@[to_additive, simps apply] def monoid_hom.up [mul_one_class E] : E →* ulift E :=
⟨up, rfl, λ x y, rfl⟩
@[to_additive, simps] def monoid_hom.down [mul_one_class E] : ulift E →* E :=
⟨down, rfl, λ x y, rfl⟩

instance [normed_group E] : normed_group (ulift.{v} E) :=
normed_group.induced add_monoid_hom.down equiv.ulift.injective

instance {F} [normed_field F] [normed_group E] [normed_space F E] : normed_space F (ulift.{v} E) :=
{ norm_smul_le := by { rintro x ⟨y⟩, exact normed_space.norm_smul_le x y },
  ..ulift.module' }

instance {X} [topological_space X] [second_countable_topology X] :
  second_countable_topology (ulift.{v} X) :=
homeomorph.ulift.second_countable_topology

instance {X} [uniform_space X] : uniform_space (ulift.{v} X) :=
uniform_space.comap down ‹_›

lemma uniformity.ulift {X} [uniform_space X] :
  uniformity (ulift X) = comap (prod.map down down) (uniformity X) :=
uniformity_comap rfl

lemma uniform_continuous.ulift {X} [uniform_space X] :
  uniform_continuous (@homeomorph.ulift X _) :=
by { rw [uniform_continuous, uniformity.ulift], exact tendsto_comap }

lemma homeomorph.complete_space {X Y} [uniform_space X] [uniform_space Y] [complete_space Y]
  (φ : X ≃ₜ Y) (hφ : uniform_continuous φ) : complete_space X :=
begin
  constructor,
  intros f hf,
  obtain ⟨y, hy⟩ := complete_space.complete (hf.map hφ),
  refine ⟨φ.symm y, _⟩,
  rw [← φ.symm.map_nhds_eq],
  rw [map_le_iff_le_comap] at hy,
  convert hy,
  -- better lemma here would be useful
  exact map_eq_comap_of_inverse (funext φ.left_inv) (funext φ.right_inv)
end

instance {X} [uniform_space X] [complete_space X] : complete_space (ulift.{v} X) :=
homeomorph.complete_space homeomorph.ulift uniform_continuous.ulift

instance {E} [measurable_space E] : measurable_space (ulift.{v} E) :=
measurable_space.comap down ‹_›

instance {X} [measurable_space X] [topological_space X] [borel_space X] :
  borel_space (ulift.{v} X) :=
⟨by { rw [← borel_comap.symm, (borel_space.measurable_eq.symm : borel X = _)], refl }⟩

attribute [simps] mul_equiv.ulift

/-- `ulift M → M` is a linear equivalence. -/
@[simps {simp_rhs := tt}] def linear_equiv.ulift (R M : Type*)
  [semiring R] [add_comm_monoid M] [module R M] : ulift.{v} M ≃ₗ[R] M :=
{ map_smul' := λ x m, rfl, ..add_equiv.ulift }

/-- `ulift M → M` is a continuous linear equivalence -/
@[simps apply symm_apply {simp_rhs := tt}]
def continuous_linear_equiv.ulift (R M : Type*) [semiring R] [topological_space M]
  [add_comm_monoid M] [module R M] : ulift.{v} M ≃L[R] M :=
{ ..linear_equiv.ulift R M, ..homeomorph.ulift }

lemma times_cont_diff_up {F X : Type*} [nondiscrete_normed_field F] [normed_group X]
  [normed_space F X] {n : with_top ℕ} : times_cont_diff F n (@up X) :=
(continuous_linear_equiv.ulift F X).symm.times_cont_diff

lemma times_cont_diff_down {F X : Type*} [nondiscrete_normed_field F] [normed_group X]
  [normed_space F X] {n : with_top ℕ} : times_cont_diff F n (@down X) :=
(continuous_linear_equiv.ulift F X).times_cont_diff

lemma times_cont_diff_up_iff {F X Y : Type*} [nondiscrete_normed_field F] [normed_group X]
  [normed_space F X] [normed_group Y] [normed_space F Y] {n : with_top ℕ} (f : X → Y) :
  times_cont_diff F n (λ x, up (f x)) ↔ times_cont_diff F n f :=
(continuous_linear_equiv.ulift F Y).symm.comp_times_cont_diff_iff

variables [normed_group E] [normed_space ℝ E]
          [complete_space E] [second_countable_topology E]
          [measurable_space E] [borel_space E]
          {H : Type v} [normed_group H] [normed_space ℝ H]
          [finite_dimensional ℝ H]

lemma times_cont_diff_parametric_primitive_of_times_cont_diff'
  {F : H → ℝ → E} {n : ℕ} (hF : times_cont_diff ℝ n ↿F)
  {s : H → ℝ} (hs : times_cont_diff ℝ n s)
  (a : ℝ) :
  times_cont_diff ℝ n (λ x : H, ∫ t in a..s x, F x t) :=
begin
  have : times_cont_diff ℝ n (λ x : H, ∫ t in a..s x, up.{v} (F x t)) :=
    times_cont_diff_parametric_primitive_of_times_cont_diff''.{v u} (times_cont_diff_up.comp hF)
      hs a,
  change times_cont_diff ℝ n (λ x : H, ∫ t in a..s x,
    (continuous_linear_equiv.ulift ℝ E).symm.to_continuous_linear_map (F x t)) at this,
  have hFi : ∀ x, interval_integrable (F x) volume a (s x),
    from λ x, continuous.interval_integrable (hF.continuous.comp $ continuous.prod.mk x) _ _,
  simp_rw [continuous_linear_map.interval_integral_comp_comm
    (continuous_linear_equiv.ulift ℝ E).symm.to_continuous_linear_map (hFi _)] at this,
  simpa [times_cont_diff_up_iff] using this,
end

/- Should we directly prove the version below?-/

lemma times_cont_diff_parametric_primitive_of_times_cont_diff
  {F : H → ℝ → E} {n : with_top ℕ} (hF : times_cont_diff ℝ n ↿F)
  {s : H → ℝ} (hs : times_cont_diff ℝ n s)
  (a : ℝ) :
  times_cont_diff ℝ n (λ x : H, ∫ t in a..s x, F x t) :=
begin
  induction n using with_top.rec_top_coe,
  { rw times_cont_diff_top at *,
    exact λ n, times_cont_diff_parametric_primitive_of_times_cont_diff' (hF n) (hs n) a },
  { exact times_cont_diff_parametric_primitive_of_times_cont_diff' hF hs a },
end

local notation `∂₁` := partial_fderiv_fst ℝ

lemma times_cont_diff_parametric_integral_of_times_cont_diff
  {F : H → ℝ → E} {n : with_top ℕ} (hF : times_cont_diff ℝ n ↿F)
  (a b : ℝ) :
  times_cont_diff ℝ n (λ x : H, ∫ t in a..b, F x t) :=
times_cont_diff_parametric_primitive_of_times_cont_diff hF times_cont_diff_const a

lemma times_cont_diff.fderiv_parametric_integral
  {F : H → ℝ → E} (hF : times_cont_diff ℝ 1 ↿F)
  (a b : ℝ) :
  fderiv ℝ (λ x : H, ∫ t in a..b, F x t) = λ x : H, (∫ t in a..b, ∂₁F x t) :=
begin
  ext x₀,
  cases has_fderiv_at_parametric_primitive_of_times_cont_diff' hF times_cont_diff_const x₀ a with int h,
  rw [h.fderiv, fderiv_const],
  simp only [continuous_linear_map.comp_zero, add_zero, pi.zero_apply]
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
