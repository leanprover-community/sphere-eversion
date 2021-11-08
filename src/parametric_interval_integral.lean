import measure_theory.integral.interval_integral
import analysis.calculus.parametric_integral

noncomputable theory

open topological_space measure_theory filter first_countable_topology metric set
open_locale topological_space filter nnreal big_operators


-- Below is a capital iota
local notation `Ι` := set.interval_oc

section
variables {E : Type*} [normed_group E] [second_countable_topology E] [normed_space ℝ E]
  [complete_space E] [measurable_space E] [borel_space E]
  {H : Type*} [normed_group H] [normed_space ℝ H]
  [second_countable_topology $ H →L[ℝ] E]
  [borel_space $ H →L[ℝ] E]
  (ν : measure ℝ)

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
  exact (has_fderiv_at_of_dominated_of_fderiv_le ε_pos hF_meas.1 hF_int.1 hF'_meas.1 h_bound.1
         bound_integrable.1 h_diff.1).sub
        (has_fderiv_at_of_dominated_of_fderiv_le ε_pos hF_meas.2 hF_int.2 hF'_meas.2 h_bound.2
         bound_integrable.2 h_diff.2)
end

lemma ae_interval_oc {P : ℝ → Prop} {a b : ℝ} : 
  (∀ᵐ t ∂(ν.restrict $ Ι a b), P t) ↔ (∀ᵐ t ∂(ν.restrict $ Ioc a b), P t) ∧ ∀ᵐ t ∂(ν.restrict $ Ioc b a), P t:=
begin
  cases le_or_lt a b with h h,
  { simp [interval_oc_of_le h, Ioc_eq_empty_of_le h] },
  { simp [interval_oc_of_lt h, Ioc_eq_empty_of_le h.le] }
end

lemma has_fderiv_at_of_dominated_loc_of_lip_interval {F : H → ℝ → E} {F' : ℝ → (H →L[ℝ] E)} {x₀ : H}
  {a b : ℝ}
  {bound : ℝ → ℝ}
  {ε : ℝ} (ε_pos : 0 < ε)
  (hF_meas : ∀ᶠ x in 𝓝 x₀, ae_measurable (F x) $ ν.restrict (Ι a b))
  (hF_int : interval_integrable (F x₀) ν a b)
  (hF'_meas : ae_measurable F' $ ν.restrict (Ι a b))
  (h_lip : ∀ᵐ t ∂(ν.restrict (Ι a b)), lipschitz_on_with (real.nnabs $ bound t) (λ x, F x t) (ball x₀ ε))
  (bound_integrable : interval_integrable bound ν a b)
  (h_diff : ∀ᵐ t ∂(ν.restrict (Ι a b)), has_fderiv_at (λ x, F x t) (F' t) x₀) :
  interval_integrable F' ν a b ∧ has_fderiv_at (λ x, ∫ t in a..b, F x t ∂ν) (∫ t in a..b, F' t ∂ν) x₀ :=
begin
  simp_rw [ae_measurable_interval_oc_iff, eventually_and] at hF_meas hF'_meas,
  rw ae_interval_oc at h_lip h_diff,
  have H₁ := has_fderiv_at_of_dominated_loc_of_lip ε_pos hF_meas.1 hF_int.1 hF'_meas.1 h_lip.1 bound_integrable.1 h_diff.1,
  have H₂ := has_fderiv_at_of_dominated_loc_of_lip ε_pos hF_meas.2 hF_int.2 hF'_meas.2 h_lip.2 bound_integrable.2 h_diff.2,
  exact ⟨⟨H₁.1, H₂.1⟩, H₁.2.sub H₂.2⟩
end

end

section

open function

lemma is_compact.bdd_above_norm {X : Type*} [topological_space X] {E : Type*} [normed_group E]
  {s : set X} (hs : is_compact s) {f : X → E} (hf : continuous f) : ∃ M > 0, ∀ x ∈ s, ∥f x∥ ≤ M :=
begin
  cases (hs.image (continuous_norm.comp hf)).bdd_above with M hM,
  rcases s.eq_empty_or_nonempty with rfl | ⟨⟨x₀, x₀_in⟩⟩,
  { use [1, zero_lt_one],
    simp },
  { use M + 1,
    split,
    { linarith [(norm_nonneg (f x₀)).trans (hM (set.mem_image_of_mem (norm ∘ f) x₀_in))] },
    { intros x x_in,
      linarith [hM (set.mem_image_of_mem (norm ∘ f) x_in)] } }
end


lemma ae_restrict_of_forall_mem {α : Type*} [measurable_space α] {μ : measure α} {s : set α} {p : α → Prop}
    (hs : measurable_set s) (h : ∀ x ∈ s, p x) : ∀ᵐ (x : α) ∂μ.restrict s, p x :=
begin
  rw ae_restrict_iff' hs,
  exact ae_of_all _ h
end

lemma is_compact.integrable_const {α : Type*} [measurable_space α] [topological_space α]
  {E : Type*} [normed_group E] [measurable_space E]
  {s : set α} (hs : is_compact s) (c : E) (μ : measure α) [is_locally_finite_measure μ] :
  integrable (λ (x : α), c) (μ.restrict s) :=
begin
  rw integrable_const_iff,
  right,
  simpa only [set.univ_inter, measurable_set.univ, measure.restrict_apply] using hs.measure_lt_top
end

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
  repeat { rw [interval_integrable_iff, integrable_on] },
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
  {f : α → ℝ} {a b : α} {μ : measure α} (c : ℝ) : ∫ x in a..b, f x * c ∂μ = (∫ x in a..b, f x ∂μ) * c :=
by simp_rw [mul_comm, ← interval_integral.const_mul]

lemma abs_le_abs_of_nonneg {α : Type*} [add_comm_group α] [linear_order α]
   [covariant_class α α (+) (≤)] {a b : α}
  (ha : 0 ≤ a) (hab : a ≤ b) :
  |a| ≤ |b| :=
by rwa [abs_of_nonneg ha, abs_of_nonneg (ha.trans hab)]

lemma abs_le_abs_of_nonpos {α : Type*} [add_comm_group α] [linear_order α]
   [covariant_class α α (+) (≤)] {a b : α}
  (ha : a ≤ 0) (hab : b ≤ a) :
  |a| ≤ |b| :=
by { rw [abs_of_nonpos ha, abs_of_nonpos (hab.trans ha)], exact neg_le_neg_iff.mpr hab }


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

lemma interval_integrable_of_norm_sub_le {β : Type*} [normed_group β] [measurable_space β] [opens_measurable_space β] 
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

lemma interval_oc_subset_of_mem_Ioc {α : Type*} [linear_order α] {a b c d : α} (ha : a ∈ Ioc c d) (hb : b ∈ Ioc c d) :
  Ι a b ⊆ Ι c d :=
begin
   rw interval_oc_of_le (ha.1.le.trans ha.2),
   exact Ioc_subset_Ioc (le_min ha.1.le hb.1.le) (max_le ha.2 hb.2)
end

lemma interval_subset_Ioo  {α : Type*} [linear_order α] {a b c d : α} (ha : a ∈ Ioo c d) (hb : b ∈ Ioo c d) :
  interval a b ⊆ Ioo c d :=
λ t ⟨ht, ht'⟩, ⟨(lt_min ha.1 hb.1).trans_le ht, ht'.trans_lt (max_lt ha.2 hb.2)⟩

lemma interval_oc_subset_Ioo  {α : Type*} [linear_order α] {a b c d : α} (ha : a ∈ Ioo c d) (hb : b ∈ Ioo c d) :
  Ι a b ⊆ Ioo c d :=
λ t ⟨ht, ht'⟩, ⟨(lt_min ha.1 hb.1).trans ht, ht'.trans_lt (max_lt ha.2 hb.2)⟩

section

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
  have hsub₀ : Ι a₀ b₀ ⊆ Ι a b, from interval_oc_subset_of_mem_Ioc (mem_Ioc_of_Ioo ha₀) (mem_Ioc_of_Ioo hb₀),
  have Ioo_nhds : Ioo a b ∈ 𝓝 b₀, from Ioo_mem_nhds hb₀.1 hb₀.2,
  have Icc_nhds : Icc a b ∈ 𝓝 b₀, from Icc_mem_nhds hb₀.1 hb₀.2,
  have hx₀ : ∀ᵐ (t : α) ∂μ.restrict (Ι a b), ∥F x₀ t∥ ≤ bound t := (mem_of_mem_nhds h_bound : _),
  have : ∀ᶠ (p : X × α) in 𝓝 (x₀, b₀),
    ∫ s in a₀..p.2, F p.1 s ∂μ = ∫ s in a₀..b₀, F p.1 s ∂μ + ∫ s in b₀..p.2, F x₀ s ∂μ +
                                 ∫ s in b₀..p.2, (F p.1 s - F x₀ s) ∂μ,
  { rw nhds_prod_eq,
    apply mem_of_superset (prod_mem_prod h_bound Ioo_nhds),
    rintros ⟨x, t⟩ ⟨hx : ∀ᵐ (t : α) ∂μ.restrict (Ι a b), ∥F x t∥ ≤ bound t, ht : t ∈ Ioo a b⟩,
    dsimp,
    rw [interval_integral.integral_sub, add_assoc, add_sub_cancel'_right,
        interval_integral.integral_add_adjacent_intervals],
    { exact interval_integrable_of_norm_le ((hF_meas x).mono_set hsub₀)
            (ae_restrict_of_ae_restrict_of_subset hsub₀ hx)
            (bound_integrable.mono_set' hsub₀) },
    all_goals {
      have hsub : Ι b₀ t ⊆ Ι a b, from interval_oc_subset_of_mem_Ioc (mem_Ioc_of_Ioo hb₀) (mem_Ioc_of_Ioo ht),
      exact interval_integrable_of_norm_le ((hF_meas _).mono_set hsub)
            (ae_restrict_of_ae_restrict_of_subset hsub ‹_›) (bound_integrable.mono_set' hsub) } },

  rw continuous_at_congr this, clear this,
  refine continuous_at.add (continuous_at.add _ _) _,
  { change continuous_at ((λ x, ∫ (s : α) in a₀..b₀, F x s ∂μ) ∘ prod.fst) (x₀, b₀),
    apply continuous_at.comp _ continuous_at_fst,
    exact interval_integral.continuous_at_of_dominated_interval
            (eventually_of_forall $ λ x, (hF_meas x).mono_set hsub₀)
            (h_bound.mono $ λ  x, ae_restrict_of_ae_restrict_of_subset hsub₀)
            (bound_integrable.mono_set' hsub₀)
            (ae_restrict_of_ae_restrict_of_subset hsub₀ h_cont) },
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
      have hsub : Ι b₀ t ⊆ Ι a b, from interval_oc_subset_of_mem_Ioc (mem_Ioc_of_Ioo hb₀) (mem_Ioc_of_Ioo ht),
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
variables {α : Type*} [conditionally_complete_linear_order α]
          [measurable_space α] [topological_space α]
          [order_topology α]
          {G : Type*} [normed_group G] [measurable_space G]
          (μ : measure α) [is_locally_finite_measure μ]
          (c : G) (a b : α)

@[simp]
lemma interval_integrable_const : interval_integrable (λ t : α, c) μ a b:=
begin
  split ;
  exact integrable_on.mono_set (is_compact_Icc.integrable_const _ _)  Ioc_subset_Icc_self
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

end

section
open continuous_linear_map

lemma coprod_eq_add {R₁ : Type*} [semiring R₁] {M₁ : Type*} [topological_space M₁]
  [add_comm_monoid M₁] {M₂ : Type*} [topological_space M₂] [add_comm_monoid M₂]
  {M₃ : Type*} [topological_space M₃] [add_comm_monoid M₃] [module R₁ M₁]
  [module R₁ M₂] [module R₁ M₃] [has_continuous_add M₃]
    (f : M₁ →L[R₁] M₃) (g : M₂ →L[R₁] M₃) : f.coprod g = (f.comp $ fst R₁ M₁ M₂) + (g.comp $ snd R₁ M₁ M₂) :=
by { ext ; refl }

end

section

open asymptotics continuous_linear_map

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
          {E : Type*}  {F : Type*} [normed_group F]

lemma filter.eventually_le.is_O {f g h : E → F} {l : filter E} (hfg : (λ x, ∥f x∥) ≤ᶠ[l] (λ x, ∥g x∥)) (hh : is_O g h l) : is_O f h l :=
(is_O_iff.mpr ⟨1, by  simpa using hfg⟩).trans hh

lemma filter.eventually.is_O {f g h : E → F} {l : filter E} (hfg : ∀ᶠ x in l, ∥f x∥ ≤ ∥g x∥) (hh : is_O g h l) : is_O f h l :=
filter.eventually_le.is_O hfg hh

lemma filter.eventually.is_O' {f : E → F} {g : E → ℝ} {l : filter E}
  (hfg : ∀ᶠ x in l, ∥f x∥ ≤ g x) : is_O f g l :=
begin
  rw is_O_iff,
  use 1,
  apply hfg.mono,
  intros x h,
  rwa [real.norm_eq_abs, abs_of_nonneg ((norm_nonneg $ f x).trans h), one_mul]
end

variables [normed_group E] [normed_space 𝕜 E] [normed_space 𝕜 F]
          {G : Type*} [normed_group G] [normed_space 𝕜 G]

lemma asymptotics.is_O.eq_zero {f : E → F} {x₀ : E} {n : ℕ} (h : is_O f (λ x, ∥x - x₀∥^n) (𝓝 x₀)) (hn : 0 < n) :
  f x₀ = 0 :=
begin
  cases h.is_O_with with c hc,
  have:= mem_of_mem_nhds (is_O_with_iff.mp hc),
  simpa [zero_pow hn]
end

lemma is_o_pow_sub_pow_sub (x₀ : E) {n m : ℕ} (h : n < m) :
    is_o (λ (x : E), ∥x - x₀∥^m) (λ (x : E), ∥x - x₀∥^n) (𝓝 x₀) :=
begin
  have : tendsto (λ x, ∥x - x₀∥) (𝓝 x₀) (𝓝 0),
  { apply tendsto_norm_zero.comp,
    rw ← sub_self x₀,
    exact tendsto_id.sub tendsto_const_nhds },
  exact (is_o_pow_pow h).comp_tendsto this
end

lemma is_o_pow_sub_sub (x₀ : E) {m : ℕ} (h : 1 < m) :
    is_o (λ (x : E), ∥x - x₀∥^m) (λ (x : E), x - x₀) (𝓝 x₀) :=
by simpa only [is_o_norm_right, pow_one] using is_o_pow_sub_pow_sub x₀ h

lemma asymptotics.is_O_sub_prod_left (e₀ : E) (f₀ : F) (l : filter $ E × F) :
  is_O (λ p : E × F, p.1 - e₀) (λ p : E × F, p - (e₀, f₀)) l :=
is_O_of_le l (λ p, le_max_left _ _)

lemma asymptotics.is_O_sub_prod_right (e₀ : E) (f₀ : F) (l : filter $ E × F) :
  is_O (λ p : E × F, p.2 - f₀) (λ p : E × F, p - (e₀, f₀)) l :=
is_O_of_le l (λ p, le_max_right _ _)

lemma asymptotics.is_O_pow_sub_prod_left (e₀ : E) (f₀ : F) (l : filter $ E × F) (n : ℕ) :
  is_O (λ p : E × F, ∥p.1 - e₀∥^n) (λ p : E × F, ∥p - (e₀, f₀)∥^n) l :=
(is_O_norm_norm.mpr $ asymptotics.is_O_sub_prod_left e₀ f₀ l).pow n

lemma asymptotics.is_O_pow_sub_prod_right (e₀ : E) (f₀ : F) (l : filter $ E × F) (n : ℕ) :
  is_O (λ p : E × F, ∥p.2 - f₀∥^n) (λ p : E × F, ∥p - (e₀, f₀)∥^n) l :=
(is_O_norm_norm.mpr $ asymptotics.is_O_sub_prod_right e₀ f₀ l).pow n

lemma asymptotics.is_O.comp_fst {f : E → F} {n : ℕ} {e₀ : E} {l : filter E}
  (h : is_O f (λ e, ∥e - e₀∥^n) l) (g₀ : G) (l' : filter G) :
  is_O (λ p : E × G, f p.1) (λ p, ∥p - (e₀, g₀)∥^n) (l ×ᶠ l') :=
(h.comp_tendsto tendsto_fst).trans (asymptotics.is_O_pow_sub_prod_left _ _ _ _)

lemma asymptotics.is_O.comp_fst_one {f : E → F} {e₀ : E}  {l : filter E}
  (h : is_O f (λ e, ∥e - e₀∥) l) (g₀ : G) (l' : filter G) :
  is_O (λ p : E × G, f p.1) (λ p, ∥p - (e₀, g₀)∥) (l ×ᶠ l') :=
begin
  rw show (λ e, ∥e - e₀∥) = (λ e, ∥e - e₀∥^1), by { ext e, simp } at h,
  simpa using h.comp_fst g₀ l'
end

lemma asymptotics.is_O.comp_snd {f : G → F} {n : ℕ}  {g₀ : G} {l' : filter G}
  (h : is_O f (λ g, ∥g - g₀∥^n) l') (e₀ : E) (l : filter E) :
  is_O (λ p : E × G, f p.2) (λ p, ∥p - (e₀, g₀)∥^n) (l ×ᶠ l') :=
(h.comp_tendsto tendsto_snd).trans (asymptotics.is_O_pow_sub_prod_right _ _ _ _)

lemma asymptotics.is_O.comp_snd_one {f : G → F}  {g₀ : G} {l' : filter G}
  (h : is_O f (λ g, ∥g - g₀∥) l') (e₀ : E) (l : filter E) :
  is_O (λ p : E × G, f p.2) (λ p, ∥p - (e₀, g₀)∥) (l ×ᶠ l') :=
begin
  rw show (λ g, ∥g - g₀∥) = (λ g, ∥g - g₀∥^1), by { ext g, simp } at h,
  simpa using h.comp_snd e₀ l
end

lemma asymptotics.is_O.has_fderiv_at {f : E → F} {x₀ : E} {n : ℕ} (h : is_O f (λ x, ∥x - x₀∥^n) (𝓝 x₀)) (hn : 1 < n) :
  has_fderiv_at f (0 : E →L[𝕜] F) x₀ :=
begin
  change is_o _ _ _,
  simp only [h.eq_zero (zero_lt_one.trans hn), sub_zero, zero_apply],
  exact h.trans_is_o (is_o_pow_sub_sub x₀ hn)
end

lemma has_deriv_at.is_O {f : E → F} {x₀ : E} {f' : E →L[𝕜] F} (h : has_fderiv_at f f' x₀) :
  is_O (λ x, f x - f x₀) (λ x, x - x₀) (𝓝 x₀) :=
by simpa using h.is_O.add (is_O_sub f' (𝓝 x₀) x₀)

end

-- TODO: change argument order in ae_measurable.mono_set to allow dot notation

section
variables {E : Type*} [normed_group E] [normed_space ℝ E]
          [complete_space E] [second_countable_topology E]
          [measurable_space E] [borel_space E]
          {H : Type*} [normed_group H] [normed_space ℝ H]
          [second_countable_topology $ H →L[ℝ] E]

open real continuous_linear_map asymptotics

lemma of_eventually_nhds {X : Type*} [topological_space X] {P : X → Prop} {x₀ : X} (h : ∀ᶠ x in 𝓝 x₀, P x) : P x₀ :=
mem_of_mem_nhds h

lemma has_fderiv_at_parametric_primitive_of_lip {F : H → ℝ → E} {F' : ℝ → (H →L[ℝ] E)} {x₀ : H}
  {bound : ℝ → ℝ} {t₀ : ℝ}
  {ε : ℝ} (ε_pos : 0 < ε)
  {a a₀ b₀ : ℝ}
  (ha :  a ∈ Ioo a₀ b₀)
  (ht₀ : t₀ ∈ Ioo a₀ b₀)
  (hF_meas : ∀ x ∈ ball x₀ ε, ae_measurable (F x) (volume.restrict (Ioo a₀ b₀)))
  (hF_int : integrable_on (F x₀) (Ioo a₀ b₀))
  (hF_cont : continuous_at (F x₀) t₀)
  (hF'_meas : ae_measurable F' (volume.restrict $ Ι a t₀))
  (h_lipsch : ∀ᵐ t ∂(volume.restrict $ Ioo a₀ b₀), lipschitz_on_with (nnabs $ bound t) (λ x, F x t) (ball x₀ ε))
  (bound_integrable : integrable_on bound (Ioo a₀ b₀))
  (bound_cont : continuous_at bound t₀)
  (bound_nonneg : ∀ t, 0 ≤ bound t) -- this is not really needed, but much more convenient
  (h_diff : ∀ᵐ a ∂volume.restrict (Ι a t₀), has_fderiv_at (λ x, F x a) (F' a) x₀) :
  interval_integrable F' volume a t₀ ∧
  has_fderiv_at (λ p : H × ℝ, ∫ t in a..p.2, F p.1 t)
    (coprod (∫ t in a..t₀, F' t) (to_span_singleton ℝ $ F x₀ t₀)) (x₀, t₀) :=
begin
  let φ : H → ℝ → E := λ x t, ∫ s in a..t, F x s,
  let ψ : H →L[ℝ] E := ∫ t in a..t₀, F' t,
  let p₁ := fst ℝ H ℝ,
  let p₂ := snd ℝ H ℝ,
  have Ioo_nhds := Ioo_mem_nhds ht₀.1 ht₀.2,
  have bound_int : ∀ {s u}, s ∈ Ioo a₀ b₀ → u ∈ Ioo a₀ b₀ → interval_integrable bound volume s u,
  { intros s u hs hu,
    exact (bound_integrable.mono_set $ interval_subset_Ioo hs hu).interval_integrable },
  have mem_nhds : (ball x₀ ε).prod (Ioo a₀ b₀) ∈ 𝓝 (x₀, t₀),
  { rw nhds_prod_eq,
    exact prod_mem_prod (ball_mem_nhds x₀ ε_pos) Ioo_nhds },
  have x₀_in := mem_ball_self ε_pos,
  have hF_meas_ball : ∀ {x}, x ∈ ball x₀ ε → ∀ {s u}, s ∈ Ioo a₀ b₀ → u ∈ Ioo a₀ b₀ → ae_measurable (F x) (volume.restrict $ Ι s u),
  { intros x hx s u hs hu,
    exact ae_measurable.mono_set (interval_oc_subset_Ioo hs hu) (hF_meas x hx) },
  have hF_int_ball : ∀ x ∈ ball x₀ ε, ∀ {s u}, s ∈ Ioo a₀ b₀ → u ∈ Ioo a₀ b₀ → interval_integrable (F x) volume s u,
  { intros x hx s u hs hu,
    have : integrable_on (F x) (Ioo a₀ b₀),
    { apply integrable_of_norm_sub_le (hF_meas x hx) hF_int (bound_integrable.mul_const (∥x - x₀∥)),
      apply h_lipsch.mono,
      intros t ht,
      rw norm_sub_rev,
      rw lipschitz_on_with_iff_norm_sub_le at ht,
      simpa [bound_nonneg t] using  ht x hx x₀ x₀_in },
    exact (this.mono_set $ interval_subset_Ioo hs hu).interval_integrable }, 
  split,
  { apply interval_integrable_of_norm_le hF'_meas _ (bound_int ha ht₀),
    replace h_lipsch : ∀ᵐ t ∂volume.restrict (Ι a t₀), lipschitz_on_with (nnabs (bound t)) (λ (x : H), F x t) (ball x₀ ε),
      from ae_restrict_of_ae_restrict_of_subset (interval_oc_subset_Ioo ha ht₀) h_lipsch,
    apply (h_lipsch.and h_diff).mono,
    rintros t ⟨ht_lip, ht_diff⟩,
    rw show bound t = nnabs (bound t), by simp [bound_nonneg t],
    exact ht_diff.le_of_lip (ball_mem_nhds _ ε_pos) ht_lip },
  { have D₁ : has_fderiv_at (λ x : H × ℝ, φ x.1 t₀) ((∫ t in a..t₀, F' t).comp p₁) (x₀, t₀),
    { rw show (λ x : H × ℝ, φ x.1 t₀) = (λ x, ∫ t in a..t₀, F x t) ∘ p₁, by { ext, refl },
      apply has_fderiv_at.comp,
      { replace hF_meas : ∀ᶠ x in 𝓝 x₀, ae_measurable (F x) (volume.restrict (Ι a t₀)),
          from eventually.mono (ball_mem_nhds x₀ ε_pos) (λ x hx, hF_meas_ball hx ha ht₀),
        rw [coe_fst'],
        replace hF_int : interval_integrable (F x₀) volume a t₀, from hF_int_ball x₀ x₀_in ha ht₀,
        exact (has_fderiv_at_of_dominated_loc_of_lip_interval _ ε_pos hF_meas hF_int hF'_meas 
                (ae_restrict_of_ae_restrict_of_subset (interval_oc_subset_Ioo ha ht₀) h_lipsch) (bound_int ha ht₀) h_diff).2 },
      { exact p₁.has_fderiv_at } },
    have D₂ : has_fderiv_at (λ x : H × ℝ, φ x₀ x.2) ((to_span_singleton ℝ (F x₀ t₀)).comp p₂) (x₀, t₀),
    { rw show (λ x : H × ℝ, φ x₀ x.2) = (λ t, ∫ s in a..t, F x₀ s) ∘ p₂, by { ext, refl },
      apply has_fderiv_at.comp,
      rw [has_fderiv_at_iff_has_deriv_at, to_span_singleton_apply, one_smul, coe_snd'],
      exact interval_integral.integral_has_deriv_at_right (hF_int_ball x₀ x₀_in ha ht₀) ⟨Ioo a₀ b₀, Ioo_nhds, (hF_meas x₀ x₀_in)⟩ hF_cont,
      exact p₂.has_fderiv_at },
    have D₃ : has_fderiv_at (λ x : H × ℝ, ∫ t in t₀..x.2, F x.fst t - F x₀ t) (0 : H × ℝ →L[ℝ] E) (x₀, t₀),
    { apply is_O.has_fderiv_at _ one_lt_two,
      have O₁ : is_O (λ t, ∫ s in t₀..t, bound s) (λ t, t - t₀) (𝓝 t₀),
      { have M : measurable_at_filter bound (𝓝 t₀) volume,
        { use [Ioo a₀ b₀, Ioo_nhds, bound_integrable.1] },
        apply is_O.congr' _ eventually_eq.rfl (interval_integral.integral_has_deriv_at_right (bound_int ha ht₀) M bound_cont).is_O,
        apply eventually.mono Ioo_nhds,
        rintros t ht,
        dsimp only {eta := false},
        rw interval_integral.integral_interval_sub_left (bound_int ha ht) (bound_int ha ht₀) },
      replace O₁ := (is_O_norm_right.mpr O₁).comp_snd_one x₀ (𝓝 x₀),
      rw ← nhds_prod_eq at O₁,
      have O₂ : is_O (λ p : H × ℝ, ∥p.1 - x₀∥) (λ p : H × ℝ, ∥p - (x₀, t₀)∥) (𝓝 (x₀, t₀)),
        from is_O_norm_norm.mpr (asymptotics.is_O_sub_prod_left x₀ t₀ _),
      have O₃ : is_O (λ (x : H × ℝ), ∫ (t : ℝ) in t₀..x.2, F x.1 t - F x₀ t)
             (λ (x : H × ℝ), (∫ s in t₀..x.2, bound s)* ∥x.1 - x₀∥)
             (𝓝 (x₀, t₀)),
      { have bdd : ∀ᶠ (p : H × ℝ) in 𝓝 (x₀, t₀), ∥∫ s in t₀..p.2, F p.1 s - F x₀ s∥ ≤ |∫ s in t₀..p.2, bound s |* ∥p.1 - x₀∥,
        { apply eventually.mono mem_nhds,
          rintros ⟨x, t⟩ ⟨hx : x ∈ _, ht : t ∈ _⟩,
          rw  [← abs_of_nonneg (norm_nonneg $ x - x₀), ← abs_mul, ← interval_integral.mul_const],
          apply interval_integral.norm_integral_le_of_norm_le _ ((hF_meas_ball hx ht₀ ht).sub (hF_meas_ball x₀_in ht₀ ht))
            ((bound_int ht₀ ht).mul_const _),
          apply ae_restrict_of_ae_restrict_of_subset (interval_oc_subset_Ioo ht₀ ht),
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
    have : ∀ᶠ (p : H × ℝ) in 𝓝 (x₀, t₀), ∫ t in a..p.2, F p.1 t = φ p.1 t₀ + φ x₀ p.2 + (∫ t in t₀..p.2, (F p.1 t - F x₀ t)) - φ x₀ t₀,
    { apply eventually.mono mem_nhds,
      rintros ⟨x, t⟩ ⟨hx : x ∈ _, ht : t ∈ _⟩,
      have int₁ : interval_integrable (F x₀) volume a t₀ := hF_int_ball x₀ x₀_in ha ht₀,
      have int₂ : interval_integrable (F x₀) volume t₀ t := hF_int_ball x₀ x₀_in ht₀ ht,
      have int₃ : interval_integrable (F x) volume a t₀ := hF_int_ball x hx ha ht₀,
      have int₄ : interval_integrable (F x) volume t₀ t := hF_int_ball x hx ht₀ ht,
      dsimp [φ],
      rw [interval_integral.integral_sub int₄ int₂, add_sub,
          add_right_comm, sub_sub, interval_integral.integral_add_adjacent_intervals int₃ int₄],
      conv_rhs { congr, skip, rw add_comm },
      rw interval_integral.integral_add_adjacent_intervals int₁ int₂,
      abel },
    apply has_fderiv_at.congr_of_eventually_eq _ this,
    simpa using ((D₁.add D₂).add D₃).sub (has_fderiv_at_const (φ x₀ t₀) (x₀, t₀)) }
end

lemma has_fderiv_at_parametric_primitive_of_times_cont_diff {F : H → ℝ → E} (hF : times_cont_diff ℝ 1 ↿F) 
  [finite_dimensional ℝ H] (x₀ : H) (a t₀ : ℝ) :
  (interval_integrable (λ t, (fderiv ℝ $ λ x, F x t) x₀) volume a t₀) ∧ 
  has_fderiv_at (λ p : H × ℝ, ∫ t in a..p.2, F p.1 t) (coprod (∫ t in a..t₀, (fderiv ℝ $ λ x, F x t) x₀) (to_span_singleton ℝ $ F x₀ t₀)) (x₀, t₀) :=
begin
  set a₀ :=  min a t₀ - 1,
  set b₀ :=  max a t₀ + 1,
  have ha : a ∈ Ioo a₀ b₀, sorry,
  have ht₀ : t₀ ∈ Ioo a₀ b₀, sorry,
  obtain ⟨M, M_nonneg, F_bound⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ ball x₀ 1, ∀ t ∈ Ioo a₀ b₀, ∥F x t∥ ≤ M,
  { 
    sorry },
  have cont_x : ∀ x, continuous (F x),
    from λ x, hF.continuous.comp (continuous.prod.mk x),
  have int_Icc : ∀ x, integrable_on (F x) (Icc a₀ b₀),
    from λ x, (cont_x x).integrable_on_compact is_compact_Icc,
  have int_Ioo : ∀ x, integrable_on (F x) (Ioo a₀ b₀),
    from λ x, (int_Icc x).mono_set Ioo_subset_Icc_self,
  apply has_fderiv_at_parametric_primitive_of_lip zero_lt_one ha ht₀ (λ x hx, (cont_x x).ae_measurable _) (int_Ioo x₀),
  exact (cont_x x₀).continuous_at,
  apply continuous.ae_measurable,
  
  all_goals { sorry }
end
end
