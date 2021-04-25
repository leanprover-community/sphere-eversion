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



variables {α : Type*} [measurable_space α] {μ : measure α}


/-! # Integral with parameters -/

section

variables {E : Type*} [normed_group E] [second_countable_topology E] [normed_space ℝ E]
  [complete_space E] [measurable_space E] [borel_space E]

variables {X : Type*} [topological_space X] [first_countable_topology X]

lemma continuous_at_of_dominated {F : X → α → E} {x₀ : X} {bound : α → ℝ}
  (hF_meas : ∀ᶠ x in 𝓝 x₀, ae_measurable (F x) μ) (h_bound : ∀ᶠ x in 𝓝 x₀, ∀ᵐ a ∂μ, ∥F x a∥ ≤ bound a)
  (bound_integrable : integrable bound μ) (h_cont : ∀ᵐ a ∂μ, continuous_at (λ x, F x a) x₀) :
  continuous_at (λn, ∫ a, F n a ∂μ) x₀ :=
tendsto_integral_filter_of_dominated_convergence bound
  (first_countable_topology.nhds_generated_countable x₀) ‹_› (mem_of_nhds hF_meas : _) ‹_› ‹_› ‹_›

lemma continuous_of_dominated {F : X → α → E} {bound : α → ℝ}
  (hF_meas : ∀ x, ae_measurable (F x) μ) (h_bound : ∀ x, ∀ᵐ a ∂μ, ∥F x a∥ ≤ bound a)
  (bound_integrable : integrable bound μ) (h_cont : ∀ᵐ a ∂μ, continuous (λ x, F x a)) :
  continuous (λn, ∫ a, F n a ∂μ) :=
continuous_iff_continuous_at.mpr (λ x₀, continuous_at_of_dominated (eventually_of_forall hF_meas)
  (eventually_of_forall h_bound) ‹_› $ h_cont.mono $ λ _, continuous.continuous_at)

end

variables {E : Type*} [normed_group E] [measurable_space E] [borel_space E]

lemma integrable_of_norm_sub_le {f₀ f₁ : α → E} {g : α → ℝ}
  (hf₁_m : ae_measurable f₁ μ)
  (hf₀_i : integrable f₀ μ)
  (hg_i : integrable g μ)
  (h : ∀ᵐ a ∂μ, ∥f₀ a - f₁ a∥ ≤ g a) :
  integrable f₁ μ :=
begin
  have : ∀ᵐ a ∂μ, ∥f₁ a∥ ≤ ∥f₀ a∥ + g a,
  { apply h.mono,
    intros a ha,
    calc ∥f₁ a∥ ≤ ∥f₀ a∥ + ∥f₀ a - f₁ a∥ : norm_le_insert _ _
    ... ≤ ∥f₀ a∥ + g a : add_le_add_left ha _ },
  exact integrable.mono' (hf₀_i.norm.add hg_i) hf₁_m this
end

section
variables [normed_space ℝ E] {H : Type*} [normed_group H] [normed_space ℝ H]

lemma measurable.apply_continuous_linear_map {φ : α → H →L[ℝ] E} (hφ : measurable φ) (v : H) :
  measurable (λ a, φ a v) :=
(continuous_linear_map.apply ℝ E v).measurable.comp hφ

lemma ae_measurable.apply_continuous_linear_map {φ : α → H →L[ℝ] E} (hφ : ae_measurable φ μ) (v : H) :
  ae_measurable (λ a, φ a v) μ :=
(continuous_linear_map.apply ℝ E v).measurable.comp_ae_measurable hφ
end

variables [normed_space ℝ E] {H : Type*} [normed_group H] [normed_space ℝ H] [borel_space $ H →L[ℝ] E]

lemma measure_theory.integrable.apply_continuous_linear_map {φ : α → H →L[ℝ] E}
  (φ_int : integrable φ μ) (v : H) : integrable (λ a, φ a v) μ :=
(φ_int.norm.mul_const ∥v∥).mono' (φ_int.ae_measurable.apply_continuous_linear_map v)
  (eventually_of_forall $ λ a, (φ a).le_op_norm v)

variables [second_countable_topology E] [complete_space E] [second_countable_topology $ H →L[ℝ] E] 

lemma continuous_linear_map.apply_integral {φ : α → H →L[ℝ] E}
  (φ_int : integrable φ μ) (v : H) : ∫ a, φ a v ∂μ = (∫ a, φ a ∂μ) v :=
(continuous_linear_map.apply ℝ E v).integral_comp_comm φ_int

lemma measurable_abs : measurable (abs : ℝ → ℝ) :=
continuous_abs.measurable

lemma has_fderiv_at_of_dominated_loc_of_lip' {F : H → α → E} {F' : α → (H →L[ℝ] E)} {x₀ : H}
  {bound : α → ℝ}
  {ε : ℝ}
  (ε_pos : 0 < ε)
  (hF_meas : ∀ x ∈ ball x₀ ε, ae_measurable (F x) μ)
  (hF_int : integrable (F x₀) μ)
  (hF'_meas : ae_measurable F' μ)
  (h_lipsch : ∀ᵐ a ∂μ, lipschitz_on_with (real.nnabs $ bound a) (λ x, F x a) (ball x₀ ε))
  (bound_integrable : integrable (bound : α → ℝ) μ)
  (h_diff : ∀ᵐ a ∂μ, has_fderiv_at (λ x, F x a) (F' a) x₀) :
  integrable F' μ ∧ has_fderiv_at (λ x, ∫ a, F x a ∂μ) (∫ a, F' a ∂μ) x₀ :=
begin
  have x₀_in : x₀ ∈ ball x₀ ε := mem_ball_self ε_pos,
  have nneg : ∀ x, 0 ≤ ∥x - x₀∥⁻¹ := λ x, inv_nonneg.mpr (norm_nonneg _) ,
  set b : α → ℝ := λ a, abs (bound a),
  --have b_meas : measurable b :=  measurable_abs.comp bound_measurable,
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
    exact integrable_of_norm_sub_le (hF_meas x x_in) hF_int
      (integrable.const_mul bound_integrable.norm ε) this },
  have hF'_int : integrable F' μ,
  { have : ∀ᵐ a ∂μ, ∥F' a∥ ≤ b a,
    { apply (h_diff.and h_lipsch).mono,
      rintros a ⟨ha_diff, ha_lip⟩,
      exact ha_diff.le_of_lip (ball_mem_nhds _ ε_pos) ha_lip },
    exact b_int.mono' hF'_meas this },
  refine ⟨hF'_int, _⟩,
  have h_ball: ball x₀ ε ∈ 𝓝 x₀ := ball_mem_nhds x₀ ε_pos,
  have : ∀ᶠ x in 𝓝 x₀,
      ∥x - x₀∥⁻¹ * ∥∫ a, F x a ∂μ - ∫ a, F x₀ a ∂μ - (∫ a, F' a ∂μ) (x - x₀)∥ =
       ∥∫ a, ∥x - x₀∥⁻¹ • (F x a - F x₀ a  - F' a (x - x₀)) ∂μ∥,
  { apply mem_sets_of_superset (ball_mem_nhds _ ε_pos),
    intros x x_in,
    rw [set.mem_set_of_eq, ← norm_smul_of_nonneg (nneg _), integral_smul,
        integral_sub, integral_sub, continuous_linear_map.apply_integral hF'_int],
    exacts [hF_int' x x_in, hF_int, (hF_int' x x_in).sub hF_int,
            hF'_int.apply_continuous_linear_map _] },
  rw [has_fderiv_at_iff_tendsto, tendsto_congr' this, ← tendsto_zero_iff_norm_tendsto_zero,
      ← show ∫ (a : α), ∥x₀ - x₀∥⁻¹ • (F x₀ a - F x₀ a - (F' a) (x₀ - x₀)) ∂μ = 0, by simp],
  apply tendsto_integral_filter_of_dominated_convergence,
  { apply is_countably_generated_nhds },
  { filter_upwards [h_ball],
    intros x x_in,
    apply ae_measurable.const_smul,
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
  { exact b_int.add hF'_int.norm },
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
  (hF_meas : ∀ᶠ x in 𝓝 x₀, ae_measurable (F x) μ)
  (hF_int : integrable (F x₀) μ)
  (hF'_meas : ae_measurable F' μ)
  (h_lip : ∀ᵐ a ∂μ, lipschitz_on_with (real.nnabs $ bound a) (λ x, F x a) (ball x₀ ε))
  (bound_integrable : integrable (bound : α → ℝ) μ)
  (h_diff : ∀ᵐ a ∂μ, has_fderiv_at (λ x, F x a) (F' a) x₀) :
  integrable F' μ ∧ has_fderiv_at (λ x, ∫ a, F x a ∂μ) (∫ a, F' a ∂μ) x₀ :=
begin
  obtain ⟨ε', ε'_pos, h'⟩ : ∃ ε' > 0, ∀ x ∈ ball x₀ ε', ae_measurable (F x) μ,
  by simpa using nhds_basis_ball.eventually_iff.mp hF_meas,
  set δ := min ε ε',
  have δ_pos : 0 < δ := lt_min ε_pos ε'_pos,
  replace h' : ∀ x, x ∈ ball x₀ δ → ae_measurable (F x) μ,
  { intros x x_in,
    exact h' _ (ball_subset_ball (min_le_right ε ε') x_in) },
  replace h_lip : ∀ᵐ (a : α) ∂μ, lipschitz_on_with (real.nnabs $ bound a) (λ x, F x a) (ball x₀ δ),
  { apply h_lip.mono,
    intros a lip,
    exact lip.mono (ball_subset_ball $ min_le_left ε ε') },
  apply has_fderiv_at_of_dominated_loc_of_lip' δ_pos ; assumption
end


lemma has_fderiv_at_of_dominated_of_fderiv_le {F : H → α → E} {F' : H → α → (H →L[ℝ] E)} {x₀ : H}
  {bound : α → ℝ}
  {ε : ℝ}
  (ε_pos : 0 < ε)
  (hF_meas : ∀ᶠ x in 𝓝 x₀, ae_measurable (F x) μ)
  (hF_int : integrable (F x₀) μ)
  (hF'_meas : ae_measurable (F' x₀) μ)
  (h_bound : ∀ᵐ a ∂μ, ∀ x ∈ ball x₀ ε, ∥F' x a∥ ≤ bound a)
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
  exact (has_fderiv_at_of_dominated_loc_of_lip ε_pos hF_meas hF_int
                                               hF'_meas this bound_integrable diff_x₀).2
end

open set


lemma continuous.ae_measurable {α γ : Type*} [topological_space α] [measurable_space α]
  [opens_measurable_space α] [topological_space γ] [measurable_space γ]
  [borel_space γ] {f : α → γ} (h : continuous f) (μ : measure α): ae_measurable f μ :=
⟨f, h.measurable, eventually_eq.refl _ _⟩

lemma has_deriv_at_of_dominated_loc_of_lip {F : ℝ → α → E} {F' : α → E} {x₀ : ℝ} {bound : α → ℝ}
  {ε : ℝ} (ε_pos : 0 < ε)
  (hF_meas : ∀ᶠ x in 𝓝 x₀, ae_measurable (F x) μ)
  (hF_int : integrable (F x₀) μ)
  (hF'_meas : ae_measurable F' μ)
  (h_lipsch : ∀ᵐ a ∂μ, lipschitz_on_with (real.nnabs $ bound a) (λ x, F x a) (ball x₀ ε))
  (bound_integrable : integrable (bound : α → ℝ) μ)
  (h_diff : ∀ᵐ a ∂μ, has_deriv_at (λ x, F x a) (F' a) x₀) :
  (integrable F' μ) ∧ has_deriv_at (λ x, ∫ a, F x a ∂μ) (∫ a, F' a ∂μ) x₀ :=
begin
  have hm := (continuous_linear_map.smul_rightL ℝ ℝ E 1).continuous.measurable.comp_ae_measurable
             hF'_meas,
  cases has_fderiv_at_of_dominated_loc_of_lip ε_pos hF_meas hF_int hm h_lipsch bound_integrable
    h_diff with hF'_int key,
  replace hF'_int : integrable F' μ,
  { rw [← integrable_norm_iff hm] at hF'_int,
    simpa [integrable_norm_iff, hF'_meas] using hF'_int },
  refine ⟨hF'_int, _⟩,
  simp_rw has_deriv_at_iff_has_fderiv_at at h_diff ⊢,
  rwa continuous_linear_map.integral_comp_comm _ hF'_int at key,
end

lemma has_deriv_at_of_dominated_loc_of_deriv_le {F : ℝ → α → E} {F' : ℝ → α → E} {x₀ : ℝ} {bound : α → ℝ} {ε : ℝ}
  (ε_pos : 0 < ε)
  (hF_meas : ∀ᶠ x in 𝓝 x₀, ae_measurable (F x) μ)
  (hF_int : integrable (F x₀) μ)
  (hF'_meas : ae_measurable (F' x₀) μ)
  (h_bound : ∀ᵐ a ∂μ, ∀ x ∈ ball x₀ ε, ∥F' x a∥ ≤ bound a)
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
        bound_integrable diff_x₀
end

