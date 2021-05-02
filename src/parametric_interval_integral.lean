import measure_theory.interval_integral
import parametric_integral

noncomputable theory

open topological_space measure_theory filter first_countable_topology metric
open_locale topological_space filter nnreal big_operators

section loc_integrable

variables {α : Type*} [measurable_space α] [topological_space α]

variables {E : Type*} [normed_group E] [measurable_space E]

/-- A function is locally integrable if it is integrable on each compact set. -/
def loc_integrable (f : α → E) (μ : measure α . volume_tac) := ∀ K, is_compact K → integrable_on f K μ

end loc_integrable

section interval_integrable
open set

variables {α : Type*} [linear_order α] {P : α → Prop} {a b : α}

/-- The open-closed interval with unordered bounds. -/
def interval_oc : α → α → set α := λ a b, Ioc (min a b) (max a b)

lemma interval_oc_of_le (h : a ≤ b) : interval_oc a b = Ioc a b :=
by simp [interval_oc, h]

lemma interval_oc_of_lt (h : b < a) : interval_oc a b = Ioc b a :=
by simp [interval_oc, le_of_lt h]

lemma forall_interval_oc_iff :
  (∀ x ∈ interval_oc a b, P x) ↔ (∀ x ∈ Ioc a b, P x) ∧ (∀ x ∈ Ioc b a, P x) :=
by { dsimp [interval_oc], cases le_total a b with hab hab ; simp [hab] }

variables {E : Type*} [measurable_space α] {μ : measure α} [normed_group E]

lemma ae_interval_oc_iff :
  (∀ᵐ x ∂μ, x ∈ interval_oc a b → P x) ↔ (∀ᵐ x ∂μ, x ∈ Ioc a b → P x) ∧ (∀ᵐ x ∂μ, x ∈ Ioc b a → P x) :=
by { dsimp [interval_oc], cases le_total a b with hab hab ; simp [hab] }

lemma ae_measurable_interval_oc_iff {μ : measure α} {β : Type*} [measurable_space β] {f : α → β} :
  (ae_measurable f $ μ.restrict $ interval_oc a b) ↔
  (ae_measurable f $ μ.restrict $ Ioc a b) ∧ (ae_measurable f $ μ.restrict $ Ioc b a) :=
by { dsimp [interval_oc], cases le_total a b with hab hab ; simp [hab] }


variables  [topological_space α] [opens_measurable_space α] [order_closed_topology α]

lemma ae_interval_oc_iff' : (∀ᵐ x ∂μ, x ∈ interval_oc a b → P x) ↔
  (∀ᵐ x ∂ (μ.restrict $ Ioc a b), P x) ∧ (∀ᵐ x ∂ (μ.restrict $ Ioc b a), P x) :=
begin
  simp_rw ae_interval_oc_iff,
  rw [ae_restrict_eq, eventually_inf_principal, ae_restrict_eq, eventually_inf_principal] ;
  exact measurable_set_Ioc,
end

end interval_integrable

-- Below is a capital iota
local notation `Ι` := interval_oc



section interval
variables {E : Type*} [normed_group E] [second_countable_topology E] [normed_space ℝ E]
  [complete_space E] [measurable_space E] [borel_space E]
variables {X : Type*} [topological_space X] 
variables {α : Type*} [measurable_space α] {μ : measure α}
variables [linear_order α]

lemma continuous_at_of_dominated_interval [first_countable_topology X] 
  {F : X → α → E} {x₀ : X} {bound : α → ℝ} {a b : α}
  (hF_meas : ∀ᶠ x in 𝓝 x₀, ae_measurable (F x) (μ.restrict $ Ι a b))
  (h_bound : ∀ᶠ x in 𝓝 x₀, ∀ᵐ t ∂(μ.restrict $ Ι a b), ∥F x t∥ ≤ bound t)
  (bound_integrable : interval_integrable bound μ a b)
  (h_cont : ∀ᵐ t ∂(μ.restrict $ Ι a b), continuous_at (λ x, F x t) x₀) :
  continuous_at (λn, ∫ t in a..b, F n t ∂μ) x₀ :=
begin
  have gc := first_countable_topology.nhds_generated_countable x₀,
  cases bound_integrable,
  cases le_or_gt a b with hab hab;
  [{ rw interval_oc_of_le hab at *,
     simp_rw interval_integral.integral_of_le hab },
   { rw interval_oc_of_lt hab at *,
     simp_rw interval_integral.integral_of_ge (le_of_lt hab),
     refine tendsto.neg _ }];
  apply tendsto_integral_filter_of_dominated_convergence bound gc hF_meas (mem_of_nhds hF_meas : _) h_bound,
  exact bound_integrable_left,
  exact h_cont,
  exact bound_integrable_right,
  exact h_cont
end

lemma continuous_of_dominated_interval [first_countable_topology X]
  {F : X → α → E} {bound : α → ℝ} {a b : α}
  (hF_meas : ∀ x, ae_measurable (F x) $ μ.restrict $ Ι a b)
  (h_bound : ∀ x, ∀ᵐ t ∂(μ.restrict $ Ι a b), ∥F x t∥ ≤ bound t)
  (bound_integrable : interval_integrable bound μ a b)
  (h_cont : ∀ᵐ t ∂(μ.restrict $ Ι a b), continuous (λ x, F x t)) :
  continuous (λn, ∫ t in a..b, F n t ∂μ) :=
continuous_iff_continuous_at.mpr (λ x₀, continuous_at_of_dominated_interval (eventually_of_forall hF_meas)
  (eventually_of_forall h_bound) ‹_› $ h_cont.mono $ λ _, continuous.continuous_at)

/- The next lemma uses the Lebesgue measure on ℝ. -/

/- lemma continuous_of_dominated_interval' {F : X → ℝ → E} {b : X → ℝ} {bound : ℝ → ℝ} {a : ℝ}
  {x₀ : X}
  (F_cont : ∀ᵐ t, continuous_at (λ x, F x t) x₀)
  (b_cont : continuous_at b x₀)
  (h_bound : ∀ᶠ x in 𝓝 x₀, ∀ t, ∥F x t∥ ≤ bound t)
  (h : loc_integrable bound) :
  continuous_at (λ x, ∫ t in a..b x, F x t) x₀ :=
begin

  sorry
end -/
end interval

variables (ν : measure ℝ)

local notation `I` := interval_oc

variables {E : Type*} [normed_group E] [second_countable_topology E] [normed_space ℝ E]
  [complete_space E] [measurable_space E] [borel_space E]
  {H : Type*} [normed_group H] [normed_space ℝ H]
  [second_countable_topology $ H →L[ℝ] E]
  [borel_space $ H →L[ℝ] E]

lemma has_fderiv_at_of_dominated_of_fderiv_le'' {F : H → ℝ → E} {F' : H → ℝ → (H →L[ℝ] E)} {x₀ : H}
  {a b : ℝ}
  {bound : ℝ → ℝ}
  {ε : ℝ}
  (ε_pos : 0 < ε)
  (hF_meas : ∀ᶠ x in 𝓝 x₀, ae_measurable (F x) $ ν.restrict (Ι a b))
  (hF_int : interval_integrable (F x₀) ν a b)
  (hF'_meas : ae_measurable (F' x₀) $ ν.restrict (Ι a b))
  (h_bound : ∀ᵐ t ∂ν, t ∈ I a b → ∀ x ∈ ball x₀ ε, ∥F' x t∥ ≤ bound t)
  (bound_integrable : interval_integrable bound ν a b)
  (h_diff : ∀ᵐ t ∂ν, t ∈ I a b → ∀ x ∈ ball x₀ ε, has_fderiv_at (λ x, F x t) (F' x t) x) :
  has_fderiv_at (λ x, ∫ t in a..b, F x t ∂ν) (∫ t in a..b, F' x₀ t ∂ν) x₀ :=
begin
  erw ae_interval_oc_iff' at h_diff h_bound,
  simp_rw [ae_measurable_interval_oc_iff, eventually_and] at hF_meas hF'_meas,
  exact (has_fderiv_at_of_dominated_of_fderiv_le ε_pos hF_meas.1 hF_int.1 hF'_meas.1 h_bound.1
         bound_integrable.1 h_diff.1).sub
        (has_fderiv_at_of_dominated_of_fderiv_le ε_pos hF_meas.2 hF_int.2 hF'_meas.2 h_bound.2
         bound_integrable.2 h_diff.2)
end
