import measure_theory.interval_integral
import analysis.calculus.mean_value
import analysis.normed_space.finite_dimension

noncomputable theory

open topological_space measure_theory filter first_countable_topology metric
open_locale topological_space filter nnreal big_operators

@[simp]
lemma real.nnabs_of_nonneg {x : ℝ} (h : 0 ≤ x) : real.nnabs x = nnreal.of_real x :=
by { ext, simp [nnreal.coe_of_real x h, abs_of_nonneg h] }

lemma nnreal.coe_of_real_le (x : ℝ) : (nnreal.of_real x : ℝ) ≤ abs x :=
begin
  by_cases h : 0 ≤ x,
  { simp [h, nnreal.coe_of_real x h, le_abs_self] },
  { simp [nnreal.of_real, h, le_abs_self, abs_nonneg] }
end

section
variables (𝕜 : Type*) [nondiscrete_normed_field 𝕜]
          {E : Type*} [normed_group E] [normed_space 𝕜 E]
          (F : Type*) [normed_group F] [normed_space 𝕜 F]

lemma continuous_linear_map.continuous_apply (v : E) : continuous (continuous_linear_map.applyₗ 𝕜 F v) :=
begin
  apply (continuous_linear_map.applyₗ 𝕜 F v).continuous_of_bound,
  intro f,
  rw mul_comm,
  exact f.le_op_norm v,
end

end

section interval_integrable
open set

variables {α : Type*} [decidable_linear_order α] {P : α → Prop} {a b : α}

def interval_oc : α → α → set α := λ a b, Ioc (min a b) (max a b)

lemma forall_interval_oc_iff : 
  (∀ x ∈ interval_oc a b, P x) ↔ (∀ x ∈ Ioc a b, P x) ∧ (∀ x ∈ Ioc b a, P x) :=
by { dsimp [interval_oc], cases le_total a b with hab hab ; simp [hab] }

variables {E : Type*} [measurable_space α] {μ : measure α} [normed_group E] 

lemma ae_interval_oc__iff : 
  (∀ᵐ x ∂μ, x ∈ interval_oc a b → P x) ↔ (∀ᵐ x ∂μ, x ∈ Ioc a b → P x) ∧ (∀ᵐ x ∂μ, x ∈ Ioc b a → P x) :=
by { dsimp [interval_oc], cases le_total a b with hab hab ; simp [hab] }

variables  [topological_space α] [opens_measurable_space α] [order_closed_topology α]

lemma ae_interval_oc__iff' : (∀ᵐ x ∂μ, x ∈ interval_oc a b → P x) ↔ 
  (∀ᵐ x ∂ (μ.restrict $ Ioc a b), P x) ∧ (∀ᵐ x ∂ (μ.restrict $ Ioc b a), P x) :=
begin
  simp_rw ae_interval_oc__iff,
  rw [ae_restrict_eq, eventually_inf_principal, ae_restrict_eq, eventually_inf_principal] ;   
  exact is_measurable_Ioc
end

end interval_integrable

variables {α : Type*} [measurable_space α] {μ : measure α}


/-! # Integral with parameters -/

section

variables {E : Type*} [normed_group E] [second_countable_topology E] [normed_space ℝ E]
  [complete_space E] [measurable_space E] [borel_space E]

variables {X : Type*} [topological_space X] [first_countable_topology X]

lemma continuous_at_of_dominated {F : X → α → E} {x₀ : X} {bound : α → ℝ}
  (hF_meas : ∀ᶠ x in 𝓝 x₀, measurable (F x)) (h_bound : ∀ᶠ x in 𝓝 x₀, ∀ᵐ a ∂μ, ∥F x a∥ ≤ bound a)
  (bound_integrable : integrable bound μ) (h_cont : ∀ᵐ a ∂μ, continuous_at (λ x, F x a) x₀) :
  continuous_at (λn, ∫ a, F n a ∂μ) x₀ :=
tendsto_integral_filter_of_dominated_convergence bound
  (first_countable_topology.nhds_generated_countable x₀) ‹_› (mem_of_nhds hF_meas) ‹_› ‹_› ‹_›

lemma continuous_of_dominated {F : X → α → E} {x₀ : X} {bound : α → ℝ}
  (hF_meas : ∀ x, measurable (F x)) (h_bound : ∀ x, ∀ᵐ a ∂μ, ∥F x a∥ ≤ bound a)
  (bound_integrable : integrable bound μ) (h_cont : ∀ᵐ a ∂μ, continuous (λ x, F x a)) :
  continuous (λn, ∫ a, F n a ∂μ) :=
continuous_iff_continuous_at.mpr (λ x₀, continuous_at_of_dominated (eventually_of_forall hF_meas)
  (eventually_of_forall h_bound) ‹_› $ h_cont.mono $ λ _, continuous.continuous_at)

lemma integrable_of_norm_sub_le {f₀ f₁ : α → E} {g : α → ℝ}
  (hf₀_m : measurable f₀)
  (hf₀_i : integrable f₀ μ)
  (hg_m : measurable g)
  (hg_i : integrable g μ)
  (h : ∀ᵐ a ∂μ, ∥f₀ a - f₁ a∥ ≤ g a) :
  integrable f₁ μ :=
begin
  have : ∀ᵐ a ∂μ, ∥f₁ a∥ ≤ ∥f₀ a∥ + g a,
  { apply h.mono,
    intros a ha,
    calc ∥f₁ a∥ ≤ ∥f₀ a∥ + ∥f₀ a - f₁ a∥ : norm_le_insert _ _
    ... ≤ ∥f₀ a∥ + g a : add_le_add_left ha _ },
  exact integrable.mono' (hf₀_i.norm.add  hf₀_m.norm hg_m hg_i) this,
end

variables {H : Type*} [normed_group H] [normed_space ℝ H] [measurable_space H]
  [second_countable_topology $ H →L[ℝ] E] [measurable_space $ H →L[ℝ] E]
  [borel_space $ H →L[ℝ] E]

lemma measurable.apply_continuous_linear_map {φ : α → H →L[ℝ] E} (hφ : measurable φ) (v : H) :
  measurable (λ a, φ a v) :=
(continuous_linear_map.continuous_apply _ _ v).measurable.comp hφ

lemma measure_theory.integrable.apply_continuous_linear_map {φ : α → H →L[ℝ] E}
  (φ_meas : measurable φ) (φ_int : integrable φ μ) (v : H) : integrable (λ a, φ a v) μ :=
begin
  apply (φ_int.norm.mul_const _).mono',
  apply eventually_of_forall,
  intro a,
  exact (φ a).le_op_norm v,
end

lemma continuous_linear_map.apply_integral {φ : α → H →L[ℝ] E} (φ_meas : measurable φ)
  (φ_int : integrable φ μ) (v : H) : ∫ a, φ a v ∂μ = (∫ a, φ a ∂μ) v :=
(continuous_linear_map.apply ℝ E v).integral_comp_comm φ_meas φ_int

lemma measurable_abs : measurable (abs : ℝ → ℝ) :=
real.continuous_abs.measurable

lemma has_fderiv_at_of_dominated_loc_of_lip' {F : H → α → E} {F' : α → (H →L[ℝ] E)} {x₀ : H}
  {bound : α → ℝ}
  {ε : ℝ}
  (ε_pos : 0 < ε)
  (hF_meas : ∀ x ∈ ball x₀ ε, measurable (F x))
  (hF_int : integrable (F x₀) μ)
  (hF'_meas : measurable F')
  (h_lipsch : ∀ᵐ a ∂μ, lipschitz_on_with (real.nnabs $ bound a) (λ x, F x a) (ball x₀ ε))
  (bound_measurable : measurable (bound : α → ℝ))
  (bound_integrable : integrable (bound : α → ℝ) μ)
  (h_diff : ∀ᵐ a ∂μ, has_fderiv_at (λ x, F x a) (F' a) x₀) :
  integrable F' μ ∧ has_fderiv_at (λ x, ∫ a, F x a ∂μ) (∫ a, F' a ∂μ) x₀ :=
begin
  have x₀_in : x₀ ∈ ball x₀ ε := mem_ball_self ε_pos,
  have nneg : ∀ x, 0 ≤ ∥x - x₀∥⁻¹ := λ x, inv_nonneg.mpr (norm_nonneg _) ,
  set b : α → ℝ := λ a, abs (bound a),
  have b_meas : measurable b :=  measurable_abs.comp bound_measurable,
  have b_int : integrable b μ := bound_integrable.norm,
  have b_nonneg : ∀ a, 0 ≤ b a := λ a, abs_nonneg _,
  have hF_int' : ∀ x ∈ ball x₀ ε, integrable (F x) μ,
  { intros x x_in,
    have : ∀ᵐ a ∂μ, ∥F x₀ a - F x a∥ ≤ ε * ∥(bound a : ℝ)∥,
    { apply h_lipsch.mono,
      intros a ha,
      rw lipschitz_on_with_iff_norm_sub_le at ha,
      apply (ha x₀ x₀_in x x_in).trans,
      rw [mul_comm, nnreal.coe_nnabs, real.norm_eq_abs],
      rw [mem_ball, dist_eq_norm, norm_sub_rev] at x_in,
      exact mul_le_mul_of_nonneg_right (le_of_lt x_in) (abs_nonneg  _) },
    apply integrable_of_norm_sub_le (hF_meas x₀ x₀_in) hF_int _ _ this,
    exact measurable.const_mul (measurable_norm.comp bound_measurable) ε,
    apply integrable.const_mul bound_integrable.norm },
  have hF'_int : integrable F' μ,
  { have : ∀ᵐ a ∂μ, ∥F' a∥ ≤ b a,
    { apply (h_diff.and h_lipsch).mono,
      rintros a ⟨ha_diff, ha_lip⟩,
      exact ha_diff.le_of_lip (ball_mem_nhds _ ε_pos) ha_lip },
    exact b_int.mono' this },
  refine ⟨hF'_int, _⟩,
  have h_ball: ball x₀ ε ∈ 𝓝 x₀ := ball_mem_nhds x₀ ε_pos,
  have : ∀ᶠ x in 𝓝 x₀,
      ∥x - x₀∥⁻¹ * ∥∫ a, F x a ∂μ - ∫ a, F x₀ a ∂μ - (∫ a, F' a ∂μ) (x - x₀)∥ =
       ∥∫ a, ∥x - x₀∥⁻¹ • (F x a - F x₀ a  - F' a (x - x₀)) ∂μ∥,
  { apply mem_sets_of_superset (ball_mem_nhds _ ε_pos),
    intros x x_in,
    rw [set.mem_set_of_eq, ← norm_smul_of_nonneg (nneg _), integral_smul,
        integral_sub, integral_sub, continuous_linear_map.apply_integral hF'_meas hF'_int],
    exacts [hF_meas _ x_in,
            hF_int' x x_in,
            hF_meas _ x₀_in,
            hF_int,
            (hF_meas _ x_in).sub (hF_meas _ x₀_in),
            (hF_int' x x_in).sub (hF_meas _ x_in) (hF_meas _ x₀_in) hF_int,
            hF'_meas.apply_continuous_linear_map _,
            hF'_int.apply_continuous_linear_map hF'_meas _] },
  rw [has_fderiv_at_iff_tendsto, tendsto_congr' this, ← tendsto_zero_iff_norm_tendsto_zero,
      ← show ∫ (a : α), ∥x₀ - x₀∥⁻¹ • (F x₀ a - F x₀ a - (F' a) (x₀ - x₀)) ∂μ = 0, by simp],
  apply tendsto_integral_filter_of_dominated_convergence,
  { apply is_countably_generated_nhds },
  { filter_upwards [h_ball],
    intros x x_in,
    apply measurable.const_smul,
    exact ((hF_meas _ x_in).sub (hF_meas _ x₀_in)).sub (hF'_meas.apply_continuous_linear_map _) },
  { simp [measurable_const] },
  { apply mem_sets_of_superset h_ball,
    intros x hx,
    apply (h_diff.and h_lipsch).mono,
    rintros a ⟨ha_deriv, ha_bound⟩,
    show ∥∥x - x₀∥⁻¹ • (F x a - F x₀ a - F' a (x - x₀))∥ ≤ b a + ∥F' a∥,
    replace ha_bound : ∥F x a - F x₀ a∥ ≤ b a * ∥x - x₀∥,
    { rw lipschitz_on_with_iff_norm_sub_le at ha_bound,
      exact ha_bound _ hx _ x₀_in },
    calc ∥∥x - x₀∥⁻¹ • (F x a - F x₀ a - F' a (x - x₀))∥
    = ∥∥x - x₀∥⁻¹ • (F x a - F x₀ a) - ∥x - x₀∥⁻¹ • F' a (x - x₀)∥ : by rw smul_sub
    ... ≤  ∥∥x - x₀∥⁻¹ • (F x a - F x₀ a)∥ + ∥∥x - x₀∥⁻¹ • F' a (x - x₀)∥ : norm_sub_le _ _
    ... =  ∥x - x₀∥⁻¹ * ∥F x a - F x₀ a∥ + ∥x - x₀∥⁻¹ * ∥F' a (x - x₀)∥ : by { rw [norm_smul_of_nonneg, norm_smul_of_nonneg] ; exact nneg _}
    ... ≤  ∥x - x₀∥⁻¹ * (b a * ∥x - x₀∥) + ∥x - x₀∥⁻¹ * (∥F' a∥ * ∥x - x₀∥) : add_le_add _ _
    ... ≤ b a + ∥F' a∥ : _,
    exact mul_le_mul_of_nonneg_left ha_bound (nneg _),
    apply mul_le_mul_of_nonneg_left ((F' a).le_op_norm _) (nneg _),
    by_cases h : ∥x - x₀∥ = 0,
    { simpa [h] using add_nonneg (b_nonneg a) (norm_nonneg (F' a)) },
    { field_simp [h] } },
  { exact integrable.add b_meas b_int hF'_meas.norm hF'_int.norm },
  { apply h_diff.mono,
    intros a ha,
    suffices : tendsto (λ x, ∥x - x₀∥⁻¹ • (F x a - F x₀ a - F' a (x - x₀))) (𝓝 x₀) (𝓝 0),
    by simpa,
    rw tendsto_zero_iff_norm_tendsto_zero,
    have : (λ x, ∥x - x₀∥⁻¹ * ∥F x a - F x₀ a - F' a (x - x₀)∥) = λ x, ∥∥x - x₀∥⁻¹ • (F x a - F x₀ a - F' a (x - x₀))∥,
    { ext x,
      rw norm_smul_of_nonneg (nneg _) },
    rwa [has_fderiv_at_iff_tendsto, this] at ha },
end

lemma has_fderiv_at_of_dominated_loc_of_lip {F : H → α → E} {F' : α → (H →L[ℝ] E)} {x₀ : H}
  {bound : α → ℝ}
  {ε : ℝ}
  (ε_pos : 0 < ε)
  (hF_meas : ∀ᶠ x in 𝓝 x₀, measurable (F x))
  (hF_int : integrable (F x₀) μ)
  (hF'_meas : measurable F')
  (h_lip : ∀ᵐ a ∂μ, lipschitz_on_with (real.nnabs $ bound a) (λ x, F x a) (ball x₀ ε))
  (bound_measurable : measurable (bound : α → ℝ))
  (bound_integrable : integrable (bound : α → ℝ) μ)
  (h_diff : ∀ᵐ a ∂μ, has_fderiv_at (λ x, F x a) (F' a) x₀) :
  integrable F' μ ∧ has_fderiv_at (λ x, ∫ a, F x a ∂μ) (∫ a, F' a ∂μ) x₀ :=
begin
  obtain ⟨ε', ε'_pos, h'⟩ : ∃ ε' > 0, ∀ x ∈ ball x₀ ε', measurable (F x),
  by simpa using nhds_basis_ball.eventually_iff.mp hF_meas,
  set δ := min ε ε',
  have δ_pos : 0 < δ := lt_min ε_pos ε'_pos,
  replace h' : ∀ x, x ∈ ball x₀ δ → measurable (F x),
  { intros x x_in,
    exact h' _ (ball_subset_ball (min_le_right ε ε') x_in) },
  replace h_lip : ∀ᵐ (a : α) ∂μ, lipschitz_on_with (real.nnabs $ bound a) (λ x, F x a) (ball x₀ δ),
  { apply h_lip.mono,
    intros a lip,
    exact lip.mono (ball_subset_ball $ min_le_left ε ε') },
  apply has_fderiv_at_of_dominated_loc_of_lip' δ_pos  ; assumption
end


lemma has_fderiv_at_of_dominated_of_fderiv_le {F : H → α → E} {F' : H → α → (H →L[ℝ] E)} {x₀ : H}
  {bound : α → ℝ}
  {ε : ℝ}
  (ε_pos : 0 < ε)
  (hF_meas : ∀ᶠ x in 𝓝 x₀, measurable (F x))
  (hF_int : integrable (F x₀) μ)
  (hF'_meas : measurable (F' x₀))
  (h_bound : ∀ᵐ a ∂μ, ∀ x ∈ ball x₀ ε, ∥F' x a∥ ≤ bound a)
  (bound_measurable : measurable (bound : α → ℝ))
  (bound_integrable : integrable (bound : α → ℝ) μ)
  (h_diff : ∀ᵐ a ∂μ, ∀ x ∈ ball x₀ ε, has_fderiv_at (λ x, F x a) (F' x a) x) :
  has_fderiv_at (λ x, ∫ a, F x a ∂μ) (∫ a, F' x₀ a ∂μ) x₀ :=
begin
  have x₀_in : x₀ ∈ ball x₀ ε := mem_ball_self ε_pos,
  have diff_x₀ : ∀ᵐ a ∂μ, has_fderiv_at (λ x, F x a) (F' x₀ a) x₀ :=
    h_diff.mono (λ a ha, ha x₀ x₀_in),
  have : ∀ᵐ a ∂μ, lipschitz_on_with (real.nnabs (bound a)) (λ x, F x a) (ball x₀ ε),
  { apply (h_diff.and h_bound).mono,
    rintros a ⟨ha_deriv, ha_bound⟩,
    have bound_nonneg : 0 ≤ bound a := (norm_nonneg (F' x₀ a)).trans (ha_bound x₀ x₀_in),
    rw show real.nnabs (bound a) = nnreal.of_real (bound a), by simp [bound_nonneg],
    apply convex.lipschitz_on_with_of_norm_has_fderiv_within_le _ ha_bound (convex_ball _ _),
    intros x x_in,
    exact (ha_deriv x x_in).has_fderiv_within_at, },
  exact (has_fderiv_at_of_dominated_loc_of_lip ε_pos hF_meas hF_int hF'_meas this
        bound_measurable bound_integrable diff_x₀).2
end

open set

variables (ν : measure ℝ)

local notation `I` := interval_oc

lemma has_fderiv_at_of_dominated_of_fderiv_le'' {F : H → ℝ → E} {F' : H → ℝ → (H →L[ℝ] E)} {x₀ : H}
  {a b : ℝ}  
  {bound : ℝ → ℝ}
  {ε : ℝ}
  (ε_pos : 0 < ε)
  (hF_meas : ∀ᶠ x in 𝓝 x₀, measurable (F x))
  (hF_int : interval_integrable (F x₀) ν a b)
  (hF'_meas : measurable (F' x₀))
  (h_bound : ∀ᵐ t ∂ν, t ∈ I a b → ∀ x ∈ ball x₀ ε, ∥F' x t∥ ≤ bound t)
  (bound_measurable : measurable bound)
  (bound_integrable : interval_integrable bound ν a b)
  (h_diff : ∀ᵐ t ∂ν, t ∈ I a b → ∀ x ∈ ball x₀ ε, has_fderiv_at (λ x, F x t) (F' x t) x) :
  has_fderiv_at (λ x, ∫ t in a..b, F x t ∂ν) (∫ t in a..b, F' x₀ t ∂ν) x₀ :=
begin
  erw ae_interval_oc__iff' at h_diff h_bound,
  exact has_fderiv_at.sub
    (has_fderiv_at_of_dominated_of_fderiv_le ε_pos hF_meas hF_int.1 hF'_meas 
      h_bound.1 bound_measurable bound_integrable.1 h_diff.1)
    (has_fderiv_at_of_dominated_of_fderiv_le ε_pos hF_meas hF_int.2 hF'_meas 
      h_bound.2 bound_measurable bound_integrable.2 h_diff.2)
end


instance : measurable_space (ℝ →L[ℝ] E) := borel _

instance : borel_space (ℝ →L[ℝ] E) := ⟨rfl⟩

lemma has_deriv_at_of_dominated_loc_of_lip {F : ℝ → α → E} {F' : α → E} {x₀ : ℝ} {bound : α → ℝ}
  {ε : ℝ} (ε_pos : 0 < ε)
  (hF_meas : ∀ᶠ x in 𝓝 x₀, measurable (F x))
  (hF_int : integrable (F x₀) μ)
  (hF'_meas : measurable F')
  (h_lipsch : ∀ᵐ a ∂μ, lipschitz_on_with (real.nnabs $ bound a) (λ x, F x a) (ball x₀ ε))
  (bound_measurable : measurable (bound : α → ℝ))
  (bound_integrable : integrable (bound : α → ℝ) μ)
  (h_diff : ∀ᵐ a ∂μ, has_deriv_at (λ x, F x a) (F' a) x₀) :
  (integrable F' μ) ∧ has_deriv_at (λ x, ∫ a, F x a ∂μ) (∫ a, F' a ∂μ) x₀ :=
begin
  cases has_fderiv_at_of_dominated_loc_of_lip ε_pos hF_meas hF_int
    ((1 : ℝ →L[ℝ] ℝ).smul_rightL.continuous.measurable.comp hF'_meas) h_lipsch
    bound_measurable bound_integrable h_diff with hF'_int key,
  replace hF'_int : integrable F' μ, by  simpa [← integrable_norm_iff] using hF'_int,
  refine ⟨hF'_int, _⟩,
  simp_rw has_deriv_at_iff_has_fderiv_at at h_diff ⊢,
  change has_fderiv_at (λ (x : ℝ), integral μ (F x)) ((1 : ℝ →L[ℝ] ℝ).smul_rightL (∫ a, F' a ∂μ)) x₀,
  rwa ←  ((1 : ℝ →L[ℝ] ℝ).smul_rightL : E →L[ℝ] _).integral_comp_comm hF'_meas hF'_int
end

lemma has_deriv_at_of_dominated_loc_of_deriv_le {F : ℝ → α → E} {F' : ℝ → α → E} {x₀ : ℝ} {bound : α → ℝ} {ε : ℝ}
  (ε_pos : 0 < ε)
  (hF_meas : ∀ᶠ x in 𝓝 x₀, measurable (F x))
  (hF_int : integrable (F x₀) μ)
  (hF'_meas : measurable (F' x₀))
  (h_bound : ∀ᵐ a ∂μ, ∀ x ∈ ball x₀ ε, ∥F' x a∥ ≤ bound a)
  (bound_measurable : measurable (bound : α → ℝ))
  (bound_integrable : integrable bound μ)
  (h_diff : ∀ᵐ a ∂μ, ∀ x ∈ ball x₀ ε, has_deriv_at (λ x, F x a) (F' x a) x) :
  (integrable (F' x₀) μ) ∧ has_deriv_at (λn, ∫ a, F n a ∂μ) (∫ a, F' x₀ a ∂μ) x₀ :=
begin
  have x₀_in : x₀ ∈ ball x₀ ε := mem_ball_self ε_pos,
  have diff_x₀ : ∀ᵐ a ∂μ, has_deriv_at (λ x, F x a) (F' x₀ a) x₀ :=
    h_diff.mono (λ a ha, ha x₀ x₀_in),
  have : ∀ᵐ a ∂μ, lipschitz_on_with (real.nnabs (bound a)) (λ (x : ℝ), F x a) (ball x₀ ε),
  { apply (h_diff.and h_bound).mono,
    rintros a ⟨ha_deriv, ha_bound⟩,
    have bound_nonneg : 0 ≤ bound a := (norm_nonneg (F' x₀ a)).trans (ha_bound x₀ x₀_in),
    rw show real.nnabs (bound a) = nnreal.of_real (bound a), by simp [bound_nonneg],
    apply convex.lipschitz_on_with_of_norm_has_deriv_within_le (convex_ball _ _)
    (λ x x_in, (ha_deriv x x_in).has_deriv_within_at) ha_bound },
  exact has_deriv_at_of_dominated_loc_of_lip ε_pos hF_meas hF_int hF'_meas this
        bound_measurable bound_integrable diff_x₀
end

end
