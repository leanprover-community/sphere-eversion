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
  {α : Type*} [topological_space α] [measurable_space α] [opens_measurable_space α] [t2_space α]
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
  [measurable_space E] [normed_group E]

lemma interval_integrable_iff_norm {f : α → E} {μ : measure α} {a b : α} :
  interval_integrable f μ a b ↔ interval_integrable (λ t, ∥f t∥) μ a b :=
sorry

lemma interval_integrable_of_le {f : α → E} {bound : α → ℝ} {μ : measure α} {a b : α}
  (h : ∀ᵐ t ∂(μ.restrict $ Ι a b), ∥f t∥ ≤ bound t) (hbound : interval_integrable bound μ a b) :
  interval_integrable f μ a b :=
begin

  sorry
end

variables [second_countable_topology E]
  [complete_space E] [normed_space ℝ E] [borel_space E] {a b : α} {f : α → E} {bound : α → ℝ}
  {μ : measure α}

lemma interval_integral.norm_integral_le_of_norm_le (h : ∀ᵐ t ∂(μ.restrict $ Ι a b), ∥f t∥ ≤ bound t) :
  ∥∫ t in a..b, f t ∂μ∥ ≤ |∫ t in a..b, bound t ∂μ| :=
begin
  apply interval_integral.norm_integral_le_abs_integral_norm.trans,
  cases le_total a b with hab hab,
  { apply (interval_integral.abs_integral_le_integral_abs hab).trans,
    sorry },
  { rw [interval_integral.integral_of_ge hab, interval_integral.integral_of_ge hab,
      abs_neg, abs_neg, abs_of_nonneg, abs_of_nonneg],
    {
      sorry },

    {
      sorry },
    {
      sorry } }
end




end

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
  have Ioo_nhds : Ioo a b ∈ 𝓝 b₀,
  {
    sorry },
  have Icc_nhds : Icc a b ∈ 𝓝 b₀,
  {
    sorry },
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
    {
      sorry },
    {
      sorry },
    {
      sorry },
    {
      sorry } },
  rw continuous_at_congr this, clear this,
  refine continuous_at.add (continuous_at.add _ _) _,
  { change continuous_at ((λ x, ∫ (s : α) in a₀..b₀, F x s ∂μ) ∘ prod.fst) (x₀, b₀),
    apply continuous_at.comp _ continuous_at_fst,
    change continuous_at (λ x, ∫ s in a₀..b₀, F x s ∂μ) x₀,
    sorry },
  { change continuous_at ((λ t, ∫ (s : α) in b₀..t, F x₀ s ∂μ) ∘ prod.snd) (x₀, b₀),
    apply continuous_at.comp _ continuous_at_snd,
    apply continuous_within_at.continuous_at _ Icc_nhds,
    apply interval_integral.continuous_within_at_primitive hμb₀,
    have  : interval (min b₀ a) (max b₀ b) ⊆ interval a b,
    {
      sorry },
    apply interval_integrable.mono_set _ this,
    exact interval_integrable_of_le hx₀ bound_integrable },
  { suffices : tendsto (λ (x : X × α), ∫ s in b₀..x.2, F x.1 s - F x₀ s ∂μ) (𝓝 (x₀, b₀)) (𝓝 0),
      by simpa [continuous_at],
    have : ∀ᶠ p : X × α in 𝓝 (x₀, b₀),
      ∥∫ s in b₀..p.2, F p.1 s - F x₀ s ∂μ∥ ≤ |∫ (s : α) in b₀..p.2, 2* bound s ∂μ|,
    { rw nhds_prod_eq,
      apply mem_of_superset (prod_mem_prod h_bound Ioo_nhds),
      rintros ⟨x, t⟩ ⟨hx : ∀ᵐ t ∂μ.restrict (Ι a b), ∥F x t∥ ≤ bound t, ht : t ∈ Ioo a b⟩,
      have H : ∀ᵐ (t : α) ∂μ.restrict (Ι b₀ t), ∥F x t - F x₀ t∥ ≤ 2*bound t,
      {
        sorry },
      exact interval_integral.norm_integral_le_of_norm_le H },
    apply squeeze_zero_norm' this,
    have : tendsto (λ t, ∫ (s : α) in b₀..t, 2 * bound s ∂μ) (𝓝 b₀) (𝓝 0),
    { suffices : continuous_at (λ t, ∫ (s : α) in b₀..t, 2 * bound s ∂μ) b₀,
      { convert this,
        simp },
      apply continuous_within_at.continuous_at _ Icc_nhds,
      apply interval_integral.continuous_within_at_primitive hμb₀,
      suffices : interval_integrable bound μ (min b₀ a) (max b₀ b),
      {
        sorry },
      apply bound_integrable.mono_set,
      sorry },
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
