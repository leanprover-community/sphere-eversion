import measure_theory.integral.interval_integral
import analysis.calculus.parametric_integral

noncomputable theory

open topological_space measure_theory filter first_countable_topology metric set
open_locale topological_space filter nnreal big_operators


-- Below is a capital iota
local notation `Ι` := set.interval_oc


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

variables {α : Type*} [linear_order α] [measurable_space α] [topological_space α]
          [order_topology α] [opens_measurable_space α] [first_countable_topology α] {μ : measure α}
          {X : Type*} [topological_space X] [first_countable_topology X]

lemma continuous_at_parametric_primitive_of_dominated {F : X → α → E} {bound : α → ℝ} {a b b₀ : α} {x₀ : X}
  (hF_meas : ∀ x, ae_measurable (F x) (μ.restrict $ Ι a b))
  (h_bound : ∀ᶠ x in 𝓝 x₀, ∀ᵐ t ∂(μ.restrict $ Ι a b), ∥F x t∥ ≤ bound t)
  (bound_integrable : interval_integrable bound μ a b)
  (h_cont : ∀ᵐ t ∂(μ.restrict $ Ι a b), continuous_at (λ x, F x t) x₀)
  (hb₀ : b₀ ∈ Ioo a b) :
  continuous_at (λ p : X × α, ∫ (t : α) in a..p.2, F p.1 t ∂μ) (x₀, b₀) :=
begin

  sorry
end

lemma continuous_parametric_primitive_of_continuous [locally_compact_space X]
  {F : X → α → E} {a : α}
  (hF : continuous (λ p : X × α, F p.1 p.2)) :
  continuous (λ p : X × α, ∫ t in a..p.2, F p.1 t ∂μ) :=
begin
  rw continuous_iff_continuous_at,
  rintros ⟨x₀, b₀⟩,
  rcases exists_compact_mem_nhds x₀ with ⟨U, U_cpct, U_nhds⟩,
  apply continuous_at_parametric_primitive_of_dominated,
  { intro x,
    apply (hF.comp (continuous.prod.mk x)).ae_measurable _ },
  { apply eventually.mono U_nhds (λ x x_in, _),
    /- have H : is_compact (Icc a $ b₀ + 1), sorry,
    rcases (U_cpct.prod H).bdd_above_norm hF with ⟨M, M_pos, hM⟩,
    apply ae_restrict_of_forall_mem,
    intros t t_in, -/
    sorry },
  {
    sorry },
  {
    sorry },
  {
    sorry },
  {
    sorry },
  {
    sorry },
end

end
