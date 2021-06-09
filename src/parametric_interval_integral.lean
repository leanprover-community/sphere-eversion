import measure_theory.interval_integral
import analysis.calculus.parametric_integral

noncomputable theory

open topological_space measure_theory filter first_countable_topology metric
open_locale topological_space filter nnreal big_operators

section interval_integrable
open set

variables {α : Type*} [linear_order α] {P : α → Prop} {a b : α}

/-- The open-closed interval with unordered bounds. -/
def interval_oc : α → α → set α := λ a b, Ioc (min a b) (max a b)

-- Below is a capital iota
local notation `Ι` := interval_oc

lemma interval_oc_of_le (h : a ≤ b) : Ι a b = Ioc a b :=
by simp [interval_oc, h]

lemma interval_oc_of_lt (h : b < a) : Ι a b = Ioc b a :=
by simp [interval_oc, le_of_lt h]

lemma forall_interval_oc_iff :
  (∀ x ∈ Ι a b, P x) ↔ (∀ x ∈ Ioc a b, P x) ∧ (∀ x ∈ Ioc b a, P x) :=
by { dsimp [interval_oc], cases le_total a b with hab hab ; simp [hab] }

variables {E : Type*} [measurable_space α] {μ : measure α} [normed_group E]

lemma ae_interval_oc_iff :
  (∀ᵐ x ∂μ, x ∈ Ι a b → P x) ↔ (∀ᵐ x ∂μ, x ∈ Ioc a b → P x) ∧ (∀ᵐ x ∂μ, x ∈ Ioc b a → P x) :=
by { dsimp [interval_oc], cases le_total a b with hab hab ; simp [hab] }

lemma ae_measurable_interval_oc_iff {μ : measure α} {β : Type*} [measurable_space β] {f : α → β} :
  (ae_measurable f $ μ.restrict $ Ι a b) ↔
  (ae_measurable f $ μ.restrict $ Ioc a b) ∧ (ae_measurable f $ μ.restrict $ Ioc b a) :=
by { dsimp [interval_oc], cases le_total a b with hab hab ; simp [hab] }


variables  [topological_space α] [opens_measurable_space α] [order_closed_topology α]

lemma ae_interval_oc_iff' : (∀ᵐ x ∂μ, x ∈ Ι a b → P x) ↔
  (∀ᵐ x ∂ (μ.restrict $ Ioc a b), P x) ∧ (∀ᵐ x ∂ (μ.restrict $ Ioc b a), P x) :=
begin
  simp_rw ae_interval_oc_iff,
  rw [ae_restrict_eq, eventually_inf_principal, ae_restrict_eq, eventually_inf_principal] ;
  exact measurable_set_Ioc,
end

variables  [second_countable_topology E] [complete_space E] [normed_space ℝ E]
  [measurable_space E] [borel_space E]

lemma interval_integrable.norm {f : α → E} {a b : α} (h : interval_integrable f μ a b) :
  interval_integrable (λ x, ∥f x∥) μ a b  :=
⟨h.1.norm, h.2.norm⟩

lemma interval_integral.congr_ae' {f g : α → E} (h : ∀ᵐ x ∂μ, x ∈ Ioc a b → f x = g x)
  (h' : ∀ᵐ x ∂μ, x ∈ Ioc b a → f x = g x) :
  ∫ (x : α) in a..b, f x ∂μ = ∫ (x : α) in a..b, g x ∂μ :=
by simp only [interval_integral, set_integral_congr_ae (measurable_set_Ioc) h,
              set_integral_congr_ae (measurable_set_Ioc) h']

lemma interval_integral.congr_ae {f g : α → E} (h : ∀ᵐ x ∂μ, x ∈ Ι a b → f x = g x) :
  ∫ (x : α) in a..b, f x ∂μ = ∫ (x : α) in a..b, g x ∂μ :=
interval_integral.congr_ae' (ae_interval_oc_iff.mp h).1 (ae_interval_oc_iff.mp h).2

lemma interval_integral.integral_zero_ae  {f : α → E} (h : ∀ᵐ x ∂μ, x ∈ Ι a b → f x = 0) :
  ∫ (x : α) in a..b, f x ∂μ = 0 :=
calc ∫ x in a..b, f x ∂μ = ∫ x in a..b, 0 ∂μ : interval_integral.congr_ae h
                     ... = 0                 : interval_integral.integral_zero

end interval_integrable

-- Below is a capital iota
local notation `Ι` := interval_oc



section interval
variables {E : Type*} [normed_group E] [second_countable_topology E] [normed_space ℝ E]
  [complete_space E] [measurable_space E] [borel_space E]
variables {X : Type*} [topological_space X]
variables {α : Type*} [measurable_space α] {μ : measure α}
variables [linear_order α]

open set

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
  apply tendsto_integral_filter_of_dominated_convergence bound gc hF_meas (mem_of_mem_nhds hF_meas : _) h_bound,
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

variables

lemma Iic_inter_Ioc {α : Type*} [linear_order α] {a₁ a₂ a₃ : α} (h : a₂ ∈ Ioc a₁ a₃) :
Iic a₂ ∩ Ioc a₁ a₃ = Ioc a₁ a₂ :=
begin
  ext x,
  change x ≤ a₂ ∧ a₁ < x ∧ x ≤ a₃ ↔ a₁ < x ∧ x ≤ a₂,
  split,
  rintros ⟨H, H', H''⟩,
  exact ⟨H', H⟩,
  rintros ⟨H, H'⟩,
  exact ⟨H', H, H'.trans h.2⟩,
end

lemma interval_integral_indicator [topological_space α] [opens_measurable_space α] [order_closed_topology α] [first_countable_topology α]
  {a₁ a₂ a₃ : α} (h : a₂ ∈ Ioc a₁ a₃) {f : α → E} :
  ∫ x in a₁..a₃, indicator {x | x ≤ a₂} f x ∂ μ = ∫ x in a₁..a₂, f x ∂ μ :=
begin
  have : {x | x ≤ a₂} ∩ Ioc a₁ a₃ = Ioc a₁ a₂, from Iic_inter_Ioc h,
  rw [interval_integral.integral_of_le h.1.le, interval_integral.integral_of_le (h.1.le.trans h.2),
      integral_indicator, measure.restrict_restrict, this],
  exact measurable_set_Iic,
  all_goals { apply measurable_set_Iic},
end

lemma continuous_at_primitive [topological_space α] [first_countable_topology α]
  [opens_measurable_space α] [order_topology α] {f : α → E}
  (h_int : ∀ a b : α, interval_integrable f μ a b) (a : α)
  {b₀ b₁ b₂ : α} (hb₁ : b₁ < b₀) (hb₂ : b₀ < b₂) (hb₀ : μ {b₀} = 0) :
  continuous_at (λ b, ∫ x in a .. b, f x ∂ μ) b₀ :=
begin
  have : (λ b, ∫ x in a..b, f x ∂μ) = (λ b, ∫ x in a..b₁, f x ∂μ) + (λ b, ∫ x in b₁..b, f x ∂μ),
  { ext b,
    exact (interval_integral.integral_add_adjacent_intervals (h_int _ _) (h_int _ _)).symm },
  rw this, clear this,
  refine continuous_const.continuous_at.add _,
  have : (λ b, ∫ x in b₁..b, f x ∂μ) =ᶠ[𝓝 b₀] λ b, ∫ x in b₁..b₂, indicator {x | x ≤ b} f x ∂ μ,
  from eventually_eq_of_mem (Ioo_mem_nhds hb₁ hb₂)
                          (λ b b_in, (interval_integral_indicator (Ioo_subset_Ioc_self b_in)).symm),
  rw  continuous_at_congr this, clear this,
  refine continuous_at_of_dominated_interval _ _ (h_int b₁ b₂).norm _,
  { apply eventually.mono (Ioo_mem_nhds hb₁ hb₂),
    intros x hx,
    erw [← ae_measurable_indicator_iff, measure.restrict_restrict, Iic_inter_Ioc],
    { exact (h_int _ _).2.ae_measurable },
    { simp [hb₁, hb₂, hx.1, hx.2.le] },
    exacts [measurable_set_Iic, measurable_set_Iic] },
  { refine eventually_of_forall (λ (x : α), eventually_of_forall (λ (t : α), _)),
    dsimp [indicator],
    split_ifs ; simp },
  { have : ∀ᵐ t ∂μ.restrict (Ι b₁ b₂), t < b₀ ∨ t > b₀,
    { apply ae_restrict_of_ae,
      apply eventually.mono (compl_mem_ae_iff.mpr hb₀),
      intros x hx,
      exact ne.lt_or_lt hx },
    apply this.mono,
    rintros x₀ (hx₀ | hx₀),
    { have : ∀ᶠ x in 𝓝 b₀, {t : α | t ≤ x}.indicator f x₀ = f x₀,
      { apply eventually.mono (Ioi_mem_nhds hx₀),
        intros x hx,
        simp [hx.le] },
      rw continuous_at_congr this,
      apply continuous_at_const },
    { have : ∀ᶠ x in 𝓝 b₀, {t : α | t ≤ x}.indicator f x₀ = 0,
      { apply eventually.mono (Iio_mem_nhds hx₀),
        intros x hx,
        simp [hx] },
      rw continuous_at_congr this,
      apply continuous_at_const } },
end

lemma continuous_primitive [no_bot_order α] [no_top_order α] [topological_space α]
  [first_countable_topology α] [opens_measurable_space α] [order_topology α] {f : α → E}
  (h_int : ∀ a b : α, interval_integrable f μ a b) (a : α) (hμ : ∀ x, μ {x} = 0):
  continuous (λ b, ∫ x in a .. b, f x ∂ μ) :=
begin
  rw continuous_iff_continuous_at,
  intro b₀,
  cases no_bot b₀ with b₁ hb₁,
  cases no_top b₀ with b₂ hb₂,
  exact continuous_at_primitive h_int a hb₁ hb₂ (hμ b₀)
end

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
