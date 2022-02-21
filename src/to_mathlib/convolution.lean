import measure_theory.integral.interval_integral
import measure_theory.group.action
import measure_theory.measure.haar_lebesgue
import measure_theory.group.integration
import to_mathlib.measure_theory.parametric_interval_integral
import to_mathlib.topology.tsupport
import analysis.calculus.fderiv_measurable

noncomputable theory
open topological_space measure_theory measure_theory.measure function set
open_locale pointwise topological_space nnreal measure_theory
open filter (hiding map_map map_id map map_id')




-- section deriv_integral
-- open metric

-- variables {α : Type*} [measurable_space α] {μ : measure α} {𝕜 : Type*} [is_R_or_C 𝕜]
--           {E : Type*} [normed_group E] [normed_space ℝ E] [normed_space 𝕜 E]
--           [complete_space E] [second_countable_topology E]
--           [measurable_space E] [borel_space E]

-- lemma has_deriv_at_integral_of_dominated_of_deriv_le {F : 𝕜 → α → E} {F' : 𝕜 → α → E}
--   {x₀ : 𝕜} {bound : α → ℝ}
--   {ε : ℝ} (ε_pos : 0 < ε)
--   (hF_meas : ∀ᶠ x in 𝓝 x₀, ae_measurable (F x) μ)
--   (hF_int : integrable (F x₀) μ)
--   (hF'_meas : ae_measurable (F' x₀) μ)
--   (h_bound : ∀ᵐ a ∂μ, ∀ x ∈ ball x₀ ε, ∥F' x a∥ ≤ bound a)
--   (bound_integrable : integrable bound μ)
--   (h_diff : ∀ᵐ a ∂μ, ∀ x ∈ ball x₀ ε, has_deriv_at (λ x, F x a) (F' x a) x) :
--   has_deriv_at (λ x, ∫ a, F x a ∂μ) (∫ a, F' x₀ a ∂μ) x₀ :=
-- (has_deriv_at_integral_of_dominated_loc_of_deriv_le ε_pos hF_meas hF_int hF'_meas h_bound
--   bound_integrable h_diff).2

-- end deriv_integral

section

-- lemma times_cont_diff_primitive_of_times_cont_diff
--   {F : H → ℝ → E} {n : with_top ℕ} (hF : times_cont_diff ℝ n ↿F) (h2F : ∀ x, integrable (F x)) :
--   times_cont_diff ℝ n (λ x : H, ∫ t, F x t) :=
-- sorry

-- lemma fderiv_parametric_integral
--   {F : H → ℝ → E} {n : with_top ℕ} (hF : times_cont_diff ℝ n ↿F) (h2F : ∀ x, integrable (F x)) :
--   times_cont_diff ℝ n (λ x : H, ∫ t, F x t) :=
-- sorry
end

section

variables {α : Type*} [measurable_space α]
variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
variables {E : Type*} [normed_group E] [normed_space 𝕜 E] [measurable_space E] [borel_space E]
variables {F : Type*} [normed_group F] [normed_space 𝕜 F]
variables {G : Type*} [normed_group G] [measurable_space G] [opens_measurable_space G]
variables {μ : measure α}

@[simp] lemma map_id' : map (λ x, x) μ = μ :=
map_id

lemma integral_norm_eq_lintegral_nnnorm {f : α → G} (hf : ae_measurable f μ) :
  ∫ x, ∥f x∥ ∂μ = ennreal.to_real ∫⁻ x, ∥f x∥₊ ∂μ :=
begin
  rw integral_eq_lintegral_of_nonneg_ae _ hf.norm,
  { simp_rw [of_real_norm_eq_coe_nnnorm], },
  { refine ae_of_all _ _, simp_rw [pi.zero_apply, norm_nonneg, imp_true_iff] },
end


-- lemma measurable_continuous_linear_map  {φ : α → F →L[𝕜] E} :
--   measurable φ ↔ ∀ v : F, measurable (λ a, φ a v) :=
-- begin
--   refine ⟨λ h, h.apply_continuous_linear_map, _⟩,
--   intro h,
--   refine measurable_generate_from _,
--   intros t ht, dsimp at ht,
--   -- have := continuous_linear_map.apply 𝕜 F E,
-- end

end


open metric
section

variables {α : Type*} [measurable_space α]
[topological_space α] [opens_measurable_space α] {μ : measure α}
[is_locally_finite_measure μ]
  {𝕜 : Type*} [is_R_or_C 𝕜]
          {E : Type*} [normed_group E] [normed_space ℝ E]
          [complete_space E] [second_countable_topology E]
          [measurable_space E] [borel_space E]
          {H : Type*} [normed_group H] [normed_space ℝ H] [second_countable_topology $ H →L[ℝ] E]
          [proper_space H]





-- version similar to https://encyclopediaofmath.org/wiki/Parameter-dependent_integral#References
-- probably not useful
-- lemma has_fderiv_at_integral' {F : H → α → E} {bound : α → ℝ}
--   {x₀ : H}
--   -- (hF_int : integrable (F x₀) μ) -- we only need this for one value(!?)
--   (hF_int : ∀ᶠ x in 𝓝 x₀, integrable (F x) μ)
--   -- (h_diff : ∀ x, ∀ᵐ a ∂μ, times_cont_diff_at ℝ 1 (λ x, F x a) x)
--   (hF_bound : ∀ᵐ a ∂μ, ∀ x, ∥partial_fderiv_fst ℝ F x a∥ ≤ bound a)
--   (h_bound : integrable bound μ)
--   (h_diff : ∀ a, differentiable ℝ (λ x, F x a))
--   (h_cont : continuous (partial_fderiv_fst ℝ F x₀)) : -- is this assumption needed?
--   has_fderiv_at (λ x, ∫ a, F x a ∂μ) (∫ a, partial_fderiv_fst ℝ F x₀ a ∂μ) x₀ :=
-- begin
--   have h_fderiv : ∀ᵐ a ∂μ, ∀ x ∈ metric.ball x₀ 1,
--     has_fderiv_at (λ x, F x a) (partial_fderiv_fst ℝ F x a) x :=
--   eventually_of_forall (λ a x hx, (h_diff a).differentiable_at.has_fderiv_at),
--   have hf_meas : ∀ᶠ x in 𝓝 x₀, ae_measurable (F x) μ :=
--   hF_int.mono (λ x h, h.ae_measurable),
--   have h_meas: ae_measurable (λ a, fderiv ℝ (λ (x : H), F x a) x₀) μ :=
--   continuous.ae_measurable h_cont μ,
--   refine has_fderiv_at_integral_of_dominated_of_fderiv_le zero_lt_one hf_meas hF_int.self_of_nhds
--     h_meas (hF_bound.mono $ λ a h x hx, h x) h_bound h_fderiv
-- end

-- lemma times_cont_diff_one_integral {F : H → α → E}
--   (hF_int : ∀ x, integrable (F x) μ)
--   (hF'_int : ∀ x, integrable (λ a, partial_fderiv_fst ℝ F x a) μ)
--   (h_diff : ∀ a, differentiable ℝ (λ x, F x a))
--   (h_cont : continuous ↿(partial_fderiv_fst ℝ F)) :
--   times_cont_diff ℝ 1 (λ x, ∫ a, F x a ∂μ) :=
-- begin
--   simp_rw [times_cont_diff_one_iff_fderiv],
--   -- have : ∀ x, has_fderiv_at (λ x, ∫ a, F x a ∂μ) (∫ a, partial_fderiv_fst ℝ F x a ∂μ) x,
--   -- { intro x, refine has_fderiv_at_integral' hF_int },
--   -- refine ⟨λ x, ∫ a, partial_fderiv_fst ℝ F x a ∂μ, _, _⟩,
--   -- have h_fderiv : ∀ᵐ a ∂μ, ∀ x ∈ metric.ball x₀ 1,
--   --   has_fderiv_at (λ x, F x a) (partial_fderiv_fst ℝ F x a) x,
--   -- { exact eventually_of_forall
--   --     (λ a x hx, ((h_diff a).differentiable le_rfl).differentiable_at.has_fderiv_at) },
--   -- have hf_cont : ∀ a, continuous_on (λ x, ∥partial_fderiv_fst ℝ F x a∥) (closed_ball x₀ 1) :=
--   -- λ a x hx, ((h_diff a).continuous_fderiv le_rfl).continuous_within_at.norm,
--   -- -- probably need sigma-finiteness for this
--   -- obtain ⟨f, h1f, h2f⟩ : ∃ f : α → ℝ, integrable f μ ∧ ∀ a, 0 < f a := sorry,
--   -- have hf_meas : ∀ᶠ x in 𝓝 x₀, ae_measurable (F x) μ :=
--   -- eventually_of_forall (λ x, (hF_int x).ae_measurable),
--   -- have :=
--   -- λ a, (is_compact_closed_ball x₀ 1).exists_forall_ge (nonempty_closed_ball.mpr zero_le_one)
--   --   (hf_cont a),
--   -- choose y hy h2y using this,
--   -- have := has_fderiv_at_integral_of_dominated_of_fderiv_le zero_lt_one hf_meas (hF_int x₀)
--   --   (hF'_int x₀).ae_measurable
--   --   (eventually_of_forall $ λ a x hx, h2y a x $ ball_subset_closed_ball hx) _ h_fderiv,

--   -- obtain ⟨h1, h2⟩ :=
--   --   has_fderiv_at_integral_of_dominated_loc_of_lip zero_lt_one hf_meas (hF_int x₀)
--   --     (hF'_int x₀).ae_measurable _ ((hF'_int x₀).norm.add h1f) h_fderiv,
--   -- { sorry },
--   -- { refine eventually_of_forall (λ a, _),
--   --   -- have := (h_diff a).times_cont_diff_at,
--   --   have := (h_diff a).times_cont_diff_at.exists_lipschitz_on_with_of_nnnorm_lt (_ + ⟨f a, (h2f a).le⟩)
--   --     (lt_of_pos_right _ _), sorry }
--   all_goals { sorry },
-- end
-- #print is_compact.exists_forall_ge
-- version similar to https://encyclopediaofmath.org/wiki/Parameter-dependent_integral#References
-- lemma times_cont_diff_one_integral_compact
--  [topological_space α] [t2_space α] [opens_measurable_space α] [is_locally_finite_measure μ]
--   {F : H → α → E} {x₀ : H}
--   (h_diff : ∀ᵐ a ∂μ, times_cont_diff ℝ 1 (λ x, F x a))
--   (h_supp : ∀ a, has_compact_support (λ x, F x a))
--   (h2_supp : ∀ x, has_compact_support (F x)) :
--   has_fderiv_at (λ x, ∫ a, F x a ∂μ) (∫ a, partial_fderiv_fst ℝ F x₀ a ∂μ) x₀ :=
-- begin
--   have hF'_supp : ∀ a, has_compact_support (λ x, partial_fderiv_fst ℝ F x a) :=
--   λ a, (h_supp a).fderiv,
--   have hnF'_supp : ∀ a, has_compact_support (λ x, ∥ partial_fderiv_fst ℝ F x a ∥) :=
--   λ a, (hF'_supp a).norm,
--   have hF_cont : ∀ᶠ x in 𝓝 x₀, continuous (F x),
--   { sorry, },
--   have hF_int : ∀ᶠ x in 𝓝 x₀, integrable (F x) μ,
--   { exact hF_cont.mono (λ x h, h.integrable_of_compact_closure_support (h2_supp x)) },
--   let bound : α → ℝ := λ a, ⨆ x, ∥ partial_fderiv_fst ℝ F x a ∥,
--   have h_int : integrable bound μ,
--   { sorry },
--   sorry,
--   -- refine has_fderiv_at_integral' hF_int _ h_int h_diff,
--   -- refine h_diff.mono (λ a h x, _),
--   -- exact le_csupr (((h.continuous_fderiv le_rfl).norm).bdd_above_range_of_has_compact_support $ hnF'_supp a) x,
-- end

end

namespace measure_theory
section locally_integrable
variables {X E : Type*} [measurable_space X] [topological_space X]
variables [normed_group E] [measurable_space E] {f : X → E} {μ : measure X}

/-- A function `f : X → E` is locally integrable if it is integrable on all compact sets.
  See `measure_theory.locally_integrable_iff` for the justification of this name. -/
def locally_integrable (f : X → E) (μ : measure X . volume_tac) : Prop :=
∀ ⦃K⦄, is_compact K → integrable_on f K μ

lemma integrable.locally_integrable (hf : integrable f μ) : locally_integrable f μ :=
λ K hK, hf.integrable_on

lemma locally_integrable.ae_measurable [sigma_compact_space X] (hf : locally_integrable f μ) :
  ae_measurable f μ :=
begin
  rw [← @restrict_univ _ _ μ, ← Union_compact_covering, ae_measurable_Union_iff],
  exact λ i, (hf $ is_compact_compact_covering X i).ae_measurable
end

lemma locally_integrable_iff [locally_compact_space X] :
  locally_integrable f μ ↔ ∀ x : X, ∃ U ∈ 𝓝 x, integrable_on f U μ :=
begin
  refine ⟨λ hf x, _, λ hf K hK, _⟩,
  { obtain ⟨K, hK, h2K⟩ := exists_compact_mem_nhds x, exact ⟨K, h2K, hf hK⟩ },
  { refine is_compact.induction_on hK integrable_on_empty (λ s t hst h, h.mono_set hst)
      (λ s t hs ht, integrable_on_union.mpr ⟨hs, ht⟩) (λ x hx, _),
    obtain ⟨K, hK, h2K⟩ := hf x, exact ⟨K, nhds_within_le_nhds hK, h2K⟩ }
end

lemma continuous.locally_integrable [opens_measurable_space X] [t2_space X] [borel_space E]
  [is_locally_finite_measure μ] (hf : continuous f) : locally_integrable f μ :=
λ K hK, hf.integrable_on_compact hK


end locally_integrable
end measure_theory


variables {𝕜 G G₀ X M R E F : Type*}
  [measurable_space G] [measurable_space G] [measurable_space G₀] [measurable_space X]
  [normed_group E] [second_countable_topology E] [normed_space ℝ E]
  [complete_space E] [measurable_space E] [borel_space E]
  {μ : measure G}

namespace measure_theory

-- usable in `continuous.integrable_of_compact_closure_support`
lemma integrable_on_iff_integable_of_support_subset {μ : measure X} {f : X → E} {s : set X}
  (h1s : support f ⊆ s) (h2s : measurable_set s) :
  integrable_on f s μ ↔ integrable f μ :=
begin
  refine ⟨λ h, _, λ h, h.integrable_on⟩,
  rwa [← indicator_eq_self.2 h1s, integrable_indicator_iff h2s]
end

section smul
variables [group G] [mul_action G X] [has_measurable_smul G X]

@[to_additive]
def integral_smul_eq_self {μ : measure X} [smul_invariant_measure G X μ] (f : X → E) {m : G} :
  ∫ x, f (m • x) ∂μ = ∫ x, f x ∂μ :=
begin
  have h : measurable_embedding (λ x : X, m • x) :=
  (measurable_equiv.smul m).measurable_embedding,
  rw [← h.integral_map, map_smul]
end

end smul


section mul

variables [group G] [topological_space G] [topological_group G] [borel_space G] {A : set G}
variables {f : G → E}

@[to_additive]
lemma integral_div_right_eq_self (f : G → E) (μ : measure G) [is_mul_right_invariant μ] (x' : G) :
  ∫ x, f (x / x') ∂μ = ∫ x, f x ∂μ :=
by simp_rw [div_eq_mul_inv, integral_mul_right_eq_self f x'⁻¹]

@[to_additive]
lemma map_inv_absolutely_continuous [second_countable_topology G]
  (μ : measure G) [is_mul_left_invariant μ] [sigma_finite μ] :
  map has_inv.inv μ ≪ μ :=
begin
  refine absolutely_continuous.mk (λ s hs, _),
  rw [map_apply measurable_inv hs, measure_inv_null], exact id,
end

@[to_additive]
lemma absolutely_continuous_map_inv [second_countable_topology G]
  (μ : measure G) [is_mul_left_invariant μ] [sigma_finite μ] :
  μ ≪ map has_inv.inv μ :=
begin
  refine absolutely_continuous.mk (λ s hs, _),
  rw [map_apply measurable_inv hs, measure_inv_null], exact id
end

@[to_additive]
lemma map_mul_right_absolutely_continuous [second_countable_topology G]
  (μ : measure G) [is_mul_left_invariant μ] [sigma_finite μ] (g : G) :
  map (* g) μ ≪ μ :=
begin
  refine absolutely_continuous.mk (λ s hs, _),
  rw [map_apply (measurable_mul_const g) hs, measure_mul_right_null], exact id,
end

@[to_additive]
lemma absolutely_continuous_map_mul_right [second_countable_topology G]
  (μ : measure G) [is_mul_left_invariant μ] [sigma_finite μ] (g : G) :
  μ ≪ map (* g) μ :=
begin
  refine absolutely_continuous.mk (λ s hs, _),
  rw [map_apply (measurable_mul_const g) hs, measure_mul_right_null], exact id
end

@[to_additive]
lemma map_div_left_absolutely_continuous [second_countable_topology G]
  (μ : measure G) [is_mul_left_invariant μ] [sigma_finite μ] (g : G) :
  map (λ h, g / h) μ ≪ μ :=
begin
  simp_rw [div_eq_mul_inv],
  rw [← map_map (measurable_const_mul g) measurable_inv],
  refine ((map_inv_absolutely_continuous μ).map _).trans _,
  rw [map_mul_left_eq_self]
end

@[to_additive]
lemma absolutely_continuous_map_div_left [second_countable_topology G]
  (μ : measure G) [is_mul_left_invariant μ] [sigma_finite μ] (g : G) :
  μ ≪ map (λ h, g / h) μ :=
begin
  simp_rw [div_eq_mul_inv],
  rw [← map_map (measurable_const_mul g) measurable_inv],
  conv_lhs { rw [← map_mul_left_eq_self μ g] },
  apply (absolutely_continuous_map_inv μ).map
end

@[to_additive]
lemma integrable.comp_div_right [is_mul_right_invariant μ] (hf : integrable f μ)
  (g : G) : integrable (λ t, f (t / g)) μ :=
begin
  rw [← map_mul_right_eq_self μ g, integrable_map_measure, function.comp],
  { simp_rw [mul_div_cancel''], exact hf },
  { refine ae_measurable.comp_measurable _ (measurable_id.div_const g),
    simp_rw [map_map (measurable_id'.div_const g) (measurable_id'.mul_const g),
      function.comp, mul_div_cancel'', map_id'],
    exact hf.ae_measurable },
  exact measurable_mul_const g
end

end mul

namespace measure

/-- A measure is invariant under negation if `- μ = μ`. Equivalently, this means that for all
measurable `A` we have `μ (- A) = μ A`, where `- A` is the pointwise negation of `A`. -/
class is_neg_invariant [has_neg G] (μ : measure G) : Prop :=
(neg_eq_self : μ.neg = μ)

/-- A measure is invariant under inversion if `μ⁻¹ = μ`. Equivalently, this means that for all
measurable `A` we have `μ (A⁻¹) = μ A`, where `A⁻¹` is the pointwise inverse of `A`. -/
@[to_additive] class is_inv_invariant [has_inv G] (μ : measure G) : Prop :=
(inv_eq_self : μ.inv = μ)

@[simp, to_additive]
lemma inv_eq_self [has_inv G] (μ : measure G) [is_inv_invariant μ] : μ.inv = μ :=
is_inv_invariant.inv_eq_self

@[simp, to_additive]
lemma map_inv_eq_self [has_inv G] (μ : measure G) [is_inv_invariant μ] :
  map has_inv.inv μ = μ :=
is_inv_invariant.inv_eq_self

instance : is_neg_invariant (volume : measure ℝ) := ⟨real.map_volume_neg⟩

/-
@[to_additive]
lemma measure_preimage_inv' [has_inv G] [has_measurable_inv G] (μ : measure G)
  [is_inv_invariant μ] (hA : measurable_set A) : μ (has_inv.inv ⁻¹' A) = μ A :=
by rw [← map_apply measurable_inv hA, map_inv_eq_self μ]

@[to_additive]
lemma measure_inv' [has_inv G] [has_measurable_inv G] (μ : measure G) [is_inv_invariant μ]
  (hA : measurable_set A) : μ A⁻¹ = μ A :=
measure_preimage_inv' μ hA
-/

variables [group G] [has_measurable_mul G] [has_measurable_inv G] {A : set G} [is_inv_invariant μ]
  {f : G → E}

@[to_additive]
lemma measure_preimage_inv (μ : measure G) [is_inv_invariant μ] (A : set G) :
  μ (has_inv.inv ⁻¹' A) = μ A :=
by { conv_rhs { rw [← map_inv_eq_self μ] }, exact ((measurable_equiv.inv G).map_apply A).symm }

@[to_additive]
lemma measure_inv (μ : measure G) [is_inv_invariant μ]
  (A : set G) : μ A⁻¹ = μ A :=
measure_preimage_inv μ A

lemma measure_preimage_inv₀ [group_with_zero G₀] [has_measurable_inv G₀] (μ : measure G₀)
  [is_inv_invariant μ] (A : set G₀) : μ (has_inv.inv ⁻¹' A) = μ A :=
by { conv_rhs { rw [← map_inv_eq_self μ] }, exact ((measurable_equiv.inv G₀).map_apply A).symm }

lemma measure_inv₀ [group_with_zero G₀] [has_measurable_inv G₀] (μ : measure G₀)
  [is_inv_invariant μ] (A : set G₀) : μ A⁻¹ = μ A :=
by { conv_rhs { rw [← map_inv_eq_self μ] }, exact ((measurable_equiv.inv G₀).map_apply A).symm }

-- @[to_additive]
-- lemma integral_inv_eq_self [smul_invariant_measure _ _ μ] (f : G → E) : ∫ x, f (x⁻¹) ∂μ = ∫ x, f x ∂μ :=
-- begin
--   have h : measurable_embedding (λ x : G, x⁻¹) :=
--   (measurable_equiv.inv G).measurable_embedding,
--   rw [← h.integral_map, map_inv_eq_self]
-- end

end measure
open measure
variables [group G] [has_measurable_mul G] [has_measurable_inv G] {f : G → E}

-- div_inv_monoid
@[to_additive]
lemma map_div_left_eq_self (μ : measure G) [is_inv_invariant μ] [is_mul_left_invariant μ] (g : G) :
  map (λ t, g / t) μ = μ :=
begin
  simp_rw [div_eq_mul_inv],
  conv_rhs { rw [← map_mul_left_eq_self μ g, ← map_inv_eq_self μ] },
  exact (map_map (measurable_const_mul g) measurable_inv).symm
end

@[to_additive]
lemma map_mul_right_inv_eq_self (μ : measure G) [is_inv_invariant μ] [is_mul_left_invariant μ] (g : G) :
  map (λ t, (g * t)⁻¹) μ = μ :=
begin
  conv_rhs { rw [← map_inv_eq_self μ, ← map_mul_left_eq_self μ g] },
  exact (map_map measurable_inv (measurable_const_mul g)).symm
end

@[to_additive]
lemma integrable.comp_div_left [is_inv_invariant μ] [is_mul_left_invariant μ] (hf : integrable f μ)
  (g : G) : integrable (λ t, f (g / t)) μ :=
begin
  rw [← map_mul_right_inv_eq_self μ g⁻¹, integrable_map_measure, function.comp],
  { simp_rw [div_inv_eq_mul, mul_inv_cancel_left], exact hf },
  { refine ae_measurable.comp_measurable _ (measurable_id.const_div g),
    simp_rw [map_map (measurable_id'.const_div g) (measurable_id'.const_mul g⁻¹).inv,
      function.comp, div_inv_eq_mul, mul_inv_cancel_left, map_id'],
    exact hf.ae_measurable },
  exact (measurable_id'.const_mul g⁻¹).inv
end

@[to_additive]
lemma integral_inv_eq_self (f : G → E) (μ : measure G) [is_inv_invariant μ] :
  ∫ x, f (x⁻¹) ∂μ = ∫ x, f x ∂μ :=
begin
  have h : measurable_embedding (λ x : G, x⁻¹) :=
  (measurable_equiv.inv G).measurable_embedding,
  rw [← h.integral_map, map_inv_eq_self]
end

@[to_additive]
lemma integral_div_left_eq_self (f : G → E) (μ : measure G) [is_inv_invariant μ]
  [is_mul_left_invariant μ] (x' : G) : ∫ x, f (x' / x) ∂μ = ∫ x, f x ∂μ :=
by simp_rw [div_eq_mul_inv, integral_inv_eq_self (λ x, f (x' * x)) μ,
  integral_mul_left_eq_self f x']


end measure_theory
open measure_theory measure_theory.measure


section noncomm

variables {f f' : G → 𝕜} {g g' : G → E}
    {x x' : G} {y y' : 𝕜}
variables [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [smul_comm_class ℝ 𝕜 E]

/-- The convolution of `f` and `g` exists at `x` when the function `t ↦ f t * g (x - t)` is
  integrable. There are various conditions on `f` and `g` to prove this. -/
def convolution_exists_at [has_sub G] (f : G → 𝕜) (g : G → E) (x : G) (μ : measure G . volume_tac) :
  Prop :=
integrable (λ t, f t • g (x - t)) μ

/-- The convolution of `f` and `g` exists when the function `t ↦ f t * g (x - t)` is integrable
  for all `x : G`. There are various conditions on `f` and `g` to prove this. -/
def convolution_exists [has_sub G] (f : G → 𝕜) (g : G → E) (μ : measure G . volume_tac) :
  Prop :=
∀ x : G, convolution_exists_at f g x μ

/-- The convolution of two functions `f` and `g`. -/
def convolution [has_sub G] (f : G → 𝕜) (g : G → E) (μ : measure G . volume_tac) : G → E :=
λ x, ∫ t, f t • g (x - t) ∂μ

localized "notation f ` ⋆[`:67 μ:67 `] `:0 g:66 := convolution f g μ" in convolution
localized "notation f ` ⋆ `:67 g:11 := convolution f g measure_theory.measure_space.volume"
  in convolution

lemma convolution_exists_at.integrable [has_sub G] {x : G} (h : convolution_exists_at f g x μ) :
  integrable (λ t, f t • g (x - t)) μ :=
h

lemma convolution_def [has_sub G] : (f ⋆[μ] g) x = ∫ t, f t • g (x - t) ∂μ := rfl


-- todo: reduce type-class constraints
variables [add_comm_group G] [topological_space G] [topological_add_group G] [borel_space G]
  [second_countable_topology G]
  [is_add_left_invariant μ] [sigma_finite μ]
variables [measurable_space 𝕜] [borel_space 𝕜] [has_measurable_smul₂ 𝕜 E]

lemma convolution_exists_at.integrable_swap [is_neg_invariant μ] (h : convolution_exists_at f g x μ) :
  integrable (λ t, f (x - t) • g t) μ :=
by { convert h.comp_sub_left x, simp_rw [sub_sub_self], }

-- todo: make `comp_sub_left` an iff
lemma convolution_exists_at_iff_integrable_swap [is_neg_invariant μ] :
  convolution_exists_at f g x μ ↔ integrable (λ t, f (x - t) • g t) μ :=
begin
  refine ⟨λ h, h.integrable_swap, λ h, _⟩, convert h.comp_sub_left x, simp_rw [sub_sub_self],
end

lemma convolution_eq_swap [is_neg_invariant μ] : (f ⋆[μ] g) x = ∫ t, f (x - t) • g t ∂μ :=
by { simp_rw [convolution_def], rw [← integral_sub_left_eq_self _ μ x], simp_rw [sub_sub_self] }

lemma convolution_fn_eq_swap [is_neg_invariant μ] : f ⋆[μ] g = λ x, ∫ t, f (x - t) • g t ∂μ :=
funext $ λ x, convolution_eq_swap

lemma smul_convolution : (y • f) ⋆[μ] g = y • (f ⋆[μ] g) :=
by { ext, simp only [pi.smul_apply, convolution_def, ← integral_smul, smul_assoc] }

lemma convolution_smul : f ⋆[μ] (y • g) = y • (f ⋆[μ] g) :=
by { ext, simp only [pi.smul_apply, convolution_def, ← integral_smul, smul_comm y] }

lemma convolution_exists_at.distrib_add {x : G} (hfg : convolution_exists_at f g x μ)
  (hfg' : convolution_exists_at f g' x μ) : (f ⋆[μ] (g + g')) x = (f ⋆[μ] g) x + (f ⋆[μ] g') x :=
by { simp only [convolution_def, smul_add, pi.add_apply, integral_add hfg hfg'] }

lemma convolution_exists.distrib_add (hfg : convolution_exists f g μ)
  (hfg' : convolution_exists f g' μ) : f ⋆[μ] (g + g') = f ⋆[μ] g + f ⋆[μ] g' :=
by { ext, exact (hfg x).distrib_add (hfg' x) }

lemma convolution_exists.add_distrib (hfg : convolution_exists f g μ)
  (hfg' : convolution_exists f' g μ) : (f + f') ⋆[μ] g = f ⋆[μ] g + f' ⋆[μ] g :=
by { ext, simp only [convolution_def, add_smul, pi.add_apply, integral_add (hfg x) (hfg' x)] }

lemma continuous.convolution_integrand_snd (hf : continuous f) (hg : continuous g) (x : G) :
  continuous (λ t, f t • g (x - t)) :=
hf.smul (hg.comp $ continuous_const.sub continuous_id)

lemma continuous.convolution_integrand_swap_snd (hf : continuous f) (hg : continuous g) (x : G) :
  continuous (λ t, f (x - t) • g t) :=
(hf.comp $ continuous_const.sub continuous_id).smul hg

lemma ae_measurable.convolution_integrand_snd (hf : ae_measurable f μ) (hg : ae_measurable g μ)
  (x : G) : ae_measurable (λ t, f t • g (x - t)) μ :=
begin
  refine hf.smul (ae_measurable.comp_measurable _ $ measurable_id.const_sub x),
  exact hg.mono' (map_sub_left_absolutely_continuous μ x)
end

lemma ae_measurable.convolution_integrand_swap_snd (hf : ae_measurable f μ) (hg : ae_measurable g μ)
  (x : G) : ae_measurable (λ t, f (x - t) • g t) μ :=
begin
  refine (ae_measurable.comp_measurable _ $ measurable_id.const_sub x).smul hg,
  exact hf.mono' (map_sub_left_absolutely_continuous μ x)
end

lemma ae_measurable.convolution_integrand (hf : ae_measurable f μ) (hg : ae_measurable g μ) :
  ae_measurable (λ p : G × G, f p.2 • g (p.1 - p.2)) (μ.prod μ) :=
begin
  refine hf.snd.smul (ae_measurable.comp_measurable _ $ measurable_fst.sub measurable_snd),
  refine hg.mono' _,
  refine absolutely_continuous.mk (λ s hs h2s, _),
  rw [map_apply measurable_sub hs],
  sorry,
end

lemma measure_theory.integrable.convolution_integrand (hf : integrable f μ) (hg : integrable g μ) :
  integrable (λ p : G × G, f p.2 • g (p.1 - p.2)) (μ.prod μ) :=
begin
  -- We can also do this for nonabelian groups, but this exact proof doesn't work
  -- for that case (we use that `μ` is right invariant here)
  simp_rw [integrable_prod_iff' (hf.ae_measurable.convolution_integrand hg.ae_measurable)],
  refine ⟨eventually_of_forall (λ t, (hg.comp_sub_right t).smul (f t)), _⟩,
  simp_rw [norm_smul, integral_mul_left, integral_sub_right_eq_self (λ t, ∥ g t ∥) μ],
  exact hf.norm.mul_const _,
end

lemma integrable.ae_convolution_exists [sigma_finite μ]
  (hf : integrable f μ) (hg : integrable g μ) : ∀ᵐ x ∂μ, convolution_exists_at f g x μ :=
((integrable_prod_iff $ hf.ae_measurable.convolution_integrand hg.ae_measurable).mp $
  hf.convolution_integrand hg).1

lemma integrable.integrable_convolution (hf : integrable f μ) (hg : integrable g μ) :
  integrable (f ⋆[μ] g) μ :=
(hf.convolution_integrand hg).integral_prod_left

lemma continuous.convolution_integrand_fst (hg : continuous g) (t : G) :
  continuous (λ x, f t • g (x - t)) :=
continuous_const.smul (hg.comp $ continuous_id.sub continuous_const)

-- -- probably not that useful
-- lemma integrable.convolution_exists_of_bounded_range_left [sigma_compact_space G]
--   [is_neg_invariant μ]
--   (hbf : bounded (range f)) (hf : ae_measurable f μ)
--   (hcf : has_compact_support f) (hg : locally_integrable g μ) :
--   convolution_exists f g μ :=
-- begin
--   intro x₀,
--   -- let K := (λ t, x₀ - t) '' tsupport f,
--   -- have hK : is_compact K := sorry,
--   have h2f : bdd_above (range (norm ∘ f)) := sorry,
--   have : ∀ᵐ (t : G) ∂μ, ∥f t • g (x₀ - t)∥ ≤ (tsupport f).indicator (λ t, (⨆ i, ∥f i∥) * ∥g (x₀ - t)∥) t,
--   { refine eventually_of_forall _,
--     refine le_indicator (λ t ht, _) (λ t ht, _),
--     { rw [norm_smul],
--       refine mul_le_mul_of_nonneg_right (le_csupr h2f t) (norm_nonneg _) },
--     { have : t ∉ support f := mt (λ h, subset_closure h) ht,
--       rw [nmem_support.mp this, zero_smul, norm_zero] } },
--   refine integrable.mono' _ (hf.convolution_integrand_snd hg.ae_measurable x₀) this,
--   { rw [integrable_indicator_iff (is_closed_add_tsupport f).measurable_set],
--   refine (integrable.norm _).const_mul _, sorry }
-- end

-- probably not that useful
-- lemma integrable.convolution_exists_of_bounded_range_right [normed_space ℝ 𝕜] (hf : integrable f μ)
--   (hbg : bounded (range g)) (hg : ae_measurable g μ) : convolution_exists f g μ :=
-- begin
--   rcases hbg.subset_ball_lt 0 0 with ⟨C, h0C, hC⟩,
--   refine λ x, (hf.smul C).mono (hf.ae_measurable.convolution_integrand_snd hg x) _,
--   refine eventually_of_forall (λ t, _),
--   simp_rw [pi.smul_apply, norm_smul, real.norm_of_nonneg h0C.le, mul_comm C],
--   refine mul_le_mul_of_nonneg_left _ (norm_nonneg _),
--   rw [← dist_zero_right],
--   exact hC ⟨x - t, rfl⟩
-- end


lemma has_compact_support.convolution_exists_left_of_continuous_right [normed_space ℝ 𝕜]
  (hcf : has_compact_support f) (hf : integrable f μ) (hg : continuous g) :
  convolution_exists f g μ :=
begin
  intro x,
  have : is_compact ((λ t, x - t) ⁻¹' tsupport f),
  { simp_rw [sub_eq_add_neg],
    exact ((homeomorph.neg G).trans $ homeomorph.add_left x).compact_preimage.mpr hcf },
  obtain ⟨c, h0c, hc⟩ := (this.bdd_above_image hg.norm.continuous_on).exists_ge 0,
  simp_rw [mem_upper_bounds, ball_image_iff, mem_preimage] at hc,
  refine (hf.smul c).mono (hf.ae_measurable.convolution_integrand_snd (hg.ae_measurable _) x) _,
  refine eventually_of_forall (λ t, _),
  simp_rw [pi.smul_apply, norm_smul, real.norm_of_nonneg h0c, mul_comm c],
  cases eq_or_ne (f t) 0 with ht ht, { simp_rw [ht, norm_zero, zero_mul] },
  refine mul_le_mul_of_nonneg_left _ (norm_nonneg _),
  apply hc, rw [sub_sub_cancel], exact subset_closure ht
end

lemma has_compact_support.convolution_exists_left [is_neg_invariant μ] [sigma_compact_space G]
  [normed_space ℝ 𝕜] (hcf : has_compact_support f) (hf : continuous f)
    (hg : locally_integrable g μ) : convolution_exists f g μ :=
begin
  intro x₀,
  rw [convolution_exists_at_iff_integrable_swap],
  let K := (λ t, x₀ - t) ⁻¹' tsupport f,
  have hK : is_compact K,
  { change K with (λ t, x₀ - t) ⁻¹' tsupport f,
    simp_rw [sub_eq_add_neg],
    exact ((homeomorph.neg G).trans $ homeomorph.add_left x₀).compact_preimage.mpr hcf },
  -- we do a little bit of extra work so that we don't have to assume `t2_space G`
  have h2K : measurable_set K :=
  (is_closed_closure.preimage $ continuous_const.sub continuous_id).measurable_set,
  have : ∀ᵐ (t : G) ∂μ,
    ∥f (x₀ - t) • g t∥ ≤ K.indicator (λ t, (⨆ i, ∥f i∥) * ∥g t∥) t,
  { refine eventually_of_forall _,
    refine le_indicator (λ t ht, _) (λ t ht, _),
    { rw [norm_smul],
      refine mul_le_mul_of_nonneg_right
        (le_csupr (hf.norm.bdd_above_range_of_has_compact_support hcf.norm) $ x₀ - t)
        (norm_nonneg _) },
    { have : x₀ - t ∉ support f := mt (λ h, subset_closure h) ht,
      rw [nmem_support.mp this, zero_smul, norm_zero] } },
  refine integrable.mono' _ _ this,
  { rw [integrable_indicator_iff h2K], exact (hg hK).norm.const_mul _ },
  { exact ((hf.ae_measurable _).convolution_integrand_swap_snd hg.ae_measurable x₀) }
end

lemma has_compact_support.convolution_exists_right [sigma_compact_space G]
  (hf : locally_integrable f μ) (hcg : has_compact_support g) (hg : continuous g) :
  convolution_exists f g μ :=
begin
  intro x₀,
  let K := (λ t, x₀ - t) ⁻¹' tsupport g,
  have hK : is_compact K,
  { change K with (λ t, x₀ - t) ⁻¹' tsupport g,
    simp_rw [sub_eq_add_neg],
    exact ((homeomorph.neg G).trans $ homeomorph.add_left x₀).compact_preimage.mpr hcg },
  -- we do a little bit of extra work so that we don't have to assume `t2_space G`
  have h2K : measurable_set K :=
  (is_closed_closure.preimage $ continuous_const.sub continuous_id).measurable_set,
  have : ∀ᵐ (t : G) ∂μ,
    ∥f t • g (x₀ - t)∥ ≤ K.indicator (λ t, ∥f t∥ * ⨆ i, ∥g i∥) t,
  { refine eventually_of_forall _,
    refine le_indicator (λ t ht, _) (λ t ht, _),
    { rw [norm_smul],
      refine mul_le_mul_of_nonneg_left
        (le_csupr (hg.norm.bdd_above_range_of_has_compact_support hcg.norm) $ x₀ - t)
        (norm_nonneg _) },
    { have : x₀ - t ∉ support g := mt (λ h, subset_closure h) ht,
      rw [nmem_support.mp this, smul_zero, norm_zero] } },
  refine integrable.mono' _ _ this,
  { rw [integrable_indicator_iff h2K], exact (hf hK).norm.mul_const _ },
  { exact (hf.ae_measurable.convolution_integrand_snd (hg.ae_measurable _) x₀) }
end

-- not useful?
lemma bdd_above.continuous_convolution_left_of_integrable [is_neg_invariant μ]
  (hbf : bdd_above (range (λ x, ∥f x∥))) (hf : continuous f) (hg : integrable g μ) :
    continuous (f ⋆[μ] g) :=
begin
  have : ∀ (x : G), ∀ᵐ (t : G) ∂μ, ∥f (x - t) • g t∥ ≤ (⨆ i, ∥f i∥) * ∥g t∥,
  { refine λ x, eventually_of_forall (λ t, _),
    rw [norm_smul],
    refine mul_le_mul_of_nonneg_right (le_csupr hbf $ x - t) (norm_nonneg _) },
  rw [convolution_fn_eq_swap],
  refine continuous_of_dominated _ this (hg.norm.const_mul _) _,
  { exact (hf.ae_measurable μ).convolution_integrand_swap_snd hg.ae_measurable },
  exact eventually_of_forall (λ t,
    (hf.comp (continuous_id.sub continuous_const)).smul continuous_const),
end

/-- A version of `has_compact_support.continuous_convolution_left` that works if `G` is
  not locally compact but requires that `g` is integrable. -/
lemma has_compact_support.continuous_convolution_left_of_integrable [is_neg_invariant μ]
  (hcf : has_compact_support f) (hf : continuous f) (hg : integrable g μ) :
    continuous (f ⋆[μ] g) :=
(hf.norm.bdd_above_range_of_has_compact_support hcf.norm).continuous_convolution_left_of_integrable
  hf hg

lemma has_compact_support.convolution_integrand_bound_left (hcf : has_compact_support f)
  (hf : continuous f) {x t : G} {s : set G} (hx : x ∈ s) :
  ∥f (x - t) • g t∥ ≤ (s + - tsupport f).indicator (λ t, (⨆ i, ∥f i∥) * ∥g t∥) t :=
begin
  refine le_indicator (λ t ht, _) (λ t ht, _) t,
  { rw [norm_smul],
    refine mul_le_mul_of_nonneg_right
      (le_csupr (hf.norm.bdd_above_range_of_has_compact_support hcf.norm) $ x - t)
      (norm_nonneg _) },
  { have : x - t ∉ support f,
    { refine mt (λ hxt, _) ht, refine ⟨_, _, hx, neg_mem_neg.mpr (subset_closure hxt), _⟩,
      rw [neg_sub, add_sub_cancel'_right] },
    rw [nmem_support.mp this, zero_smul, norm_zero] }
end

lemma has_compact_support.convolution_integrand_bound_right (hcg : has_compact_support g)
  (hg : continuous g) {x t : G} {s : set G} (hx : x ∈ s) :
  ∥f t • g (x - t)∥ ≤ (s + - tsupport g).indicator (λ t, ∥f t∥ * (⨆ i, ∥g i∥)) t :=
begin
  refine le_indicator (λ t ht, _) (λ t ht, _) t,
  { rw [norm_smul],
    refine mul_le_mul_of_nonneg_left
      (le_csupr (hg.norm.bdd_above_range_of_has_compact_support hcg.norm) $ x - t)
      (norm_nonneg _) },
  { have : x - t ∉ support g,
    { refine mt (λ hxt, _) ht, refine ⟨_, _, hx, neg_mem_neg.mpr (subset_closure hxt), _⟩,
      rw [neg_sub, add_sub_cancel'_right] },
    rw [nmem_support.mp this, smul_zero, norm_zero] }
end

lemma has_compact_support.continuous_convolution_left [locally_compact_space G] [t2_space G]
  [is_neg_invariant μ]
  (hcf : has_compact_support f) (hf : continuous f) (hg : locally_integrable g μ) :
    continuous (f ⋆[μ] g) :=
begin
  rw [convolution_fn_eq_swap, continuous_iff_continuous_at],
  intro x₀,
  obtain ⟨K, hK, h2K⟩ := exists_compact_mem_nhds x₀,
  let L := K + - tsupport f,
  have hL : is_compact L := hK.add hcf.neg,
  have : ∀ᶠ x in 𝓝 x₀, ∀ᵐ (t : G) ∂μ,
    ∥f (x - t) • g t∥ ≤ L.indicator (λ t, (⨆ i, ∥f i∥) * ∥g t∥) t :=
  eventually_of_mem h2K (λ x hx, eventually_of_forall $
    λ t, hcf.convolution_integrand_bound_left hf hx),
  refine continuous_at_of_dominated _ this _ _,
  { exact eventually_of_forall ((hf.ae_measurable μ).convolution_integrand_swap_snd
      hg.ae_measurable) },
  { rw [integrable_indicator_iff hL.measurable_set], exact (hg hL).norm.const_mul _ },
  { exact eventually_of_forall (λ t,
      ((hf.comp (continuous_id.sub continuous_const)).smul continuous_const).continuous_at) }
end

lemma has_compact_support.continuous_convolution_right [locally_compact_space G] [t2_space G]
  [is_neg_invariant μ] (hf : locally_integrable f μ) (hcg : has_compact_support g)
    (hg : continuous g) : continuous (f ⋆[μ] g) :=
begin
  rw [continuous_iff_continuous_at],
  intro x₀,
  obtain ⟨K, hK, h2K⟩ := exists_compact_mem_nhds x₀,
  let L := K + - tsupport g,
  have hL : is_compact L := hK.add hcg.neg,
  have : ∀ᶠ x in 𝓝 x₀, ∀ᵐ (t : G) ∂μ,
    ∥f t • g (x - t)∥ ≤ L.indicator (λ t, ∥f t∥ * (⨆ i, ∥g i∥)) t :=
  eventually_of_mem h2K (λ x hx, eventually_of_forall $
    λ t, hcg.convolution_integrand_bound_right hg hx),
  refine continuous_at_of_dominated _ this _ _,
  { exact eventually_of_forall (hf.ae_measurable.convolution_integrand_snd (hg.ae_measurable μ)) },
  { rw [integrable_indicator_iff hL.measurable_set], exact (hf hL).norm.mul_const _ },
  { exact eventually_of_forall (λ t, (continuous_const.smul $
      hg.comp $ continuous_id.sub $ by apply continuous_const).continuous_at) }
end

lemma has_compact_support.convolution [t2_space G] (hcf : has_compact_support f)
  (hcg : has_compact_support g) : has_compact_support (f ⋆[μ] g) :=
begin
  refine compact_of_is_closed_subset (hcf.is_compact.add hcg) is_closed_closure _,
  refine closure_minimal (λ x h2x, _) (hcf.is_compact.add hcg).is_closed,
  refine set.add_subset_add subset_closure subset_closure _,
  by_contra hx,
  simp_rw [set.mem_add, not_exists, not_and] at hx,
  apply h2x,
  rw [convolution_def],
  convert integral_zero G E,
  ext t,
  rw [smul_eq_zero],
  classical,
  by_contra ht,
  simp_rw [not_or_distrib, ← ne.def, ← mem_support] at ht,
  refine hx _ _ ht.1 ht.2 _,
  rw [add_sub_cancel'_right]
end

end noncomm

open_locale convolution

section real
/-! The one-variable case -/

variables {f f' : ℝ → ℝ} {g g' : ℝ → E} {x x' : ℝ}
variables [normed_space ℝ E]
variables {n : with_top ℕ}

lemma has_compact_support.has_deriv_at_convolution_left
  (hcf : has_compact_support f) (hf : times_cont_diff ℝ 1 f)
  (hg : locally_integrable g) (x₀ : ℝ) : has_deriv_at (f ⋆ g) ((deriv f ⋆ g) x₀) x₀ :=
begin
  have h1 : ∀ x, ae_measurable (λ t, f (x - t) • g t) volume :=
  (hf.continuous.ae_measurable _).convolution_integrand_swap_snd hg.ae_measurable,
  have h2 : ∀ x, ae_measurable (λ t, deriv f (x - t) • g t) volume :=
  ((hf.continuous_deriv le_rfl).ae_measurable _).convolution_integrand_swap_snd hg.ae_measurable,
  have h3 : ∀ x t, has_deriv_at (λ x, f (x - t)) (deriv f (x - t)) x,
  { intros x t,
    simpa using (hf.differentiable le_rfl).differentiable_at.has_deriv_at.comp x
      ((has_deriv_at_id x).sub (has_deriv_at_const x t)) },
  let L := closed_ball x₀ 1 + - tsupport (deriv f),
  have hL : is_compact L := (is_compact_closed_ball x₀ 1).add hcf.deriv.neg,
  simp_rw [convolution_fn_eq_swap],
  refine (has_deriv_at_integral_of_dominated_loc_of_deriv_le zero_lt_one
    (eventually_of_forall h1) _ _ _ _ _).2,
  { exact (hcf.convolution_exists_left hf.continuous hg x₀).integrable_swap },
  { exact h2 x₀ },
  { exact L.indicator (λ t, (⨆ x, ∥deriv f x∥) * ∥g t∥) },
  { refine eventually_of_forall (λ t x hx, _),
    refine le_indicator (λ t ht, _) (λ t ht, _) t,
    { rw [norm_smul],
      refine mul_le_mul_of_nonneg_right _ (norm_nonneg _),
      exact le_csupr ((hf.continuous_deriv le_rfl).norm.bdd_above_range_of_has_compact_support
        hcf.deriv.norm) (x - t) },
    { have : x - t ∉ support (deriv f),
      { refine mt (λ hxt, _) ht,
        refine ⟨_, _, ball_subset_closed_ball hx, neg_mem_neg.mpr (subset_closure hxt), _⟩,
        rw [neg_sub, add_sub_cancel'_right] },
      rw [nmem_support.mp this, zero_smul, norm_zero] } },
  { rw [integrable_indicator_iff hL.measurable_set], exact (hg hL).norm.const_mul _ },
  { exact eventually_of_forall (λ t x hx, (h3 x t).smul_const _) },
end

lemma has_compact_support.has_deriv_at_convolution_right
  (hf : locally_integrable f) (hcg : has_compact_support g) (hg : times_cont_diff ℝ 1 g)
  (x₀ : ℝ) : has_deriv_at (f ⋆ g) ((f ⋆ deriv g) x₀) x₀ :=
begin
  have h1 : ∀ x, ae_measurable (λ t, f t • g (x - t)) volume :=
  hf.ae_measurable.convolution_integrand_snd (hg.continuous.ae_measurable _),
  have h2 : ∀ x, ae_measurable (λ t, f t • deriv g (x - t)) volume :=
  hf.ae_measurable.convolution_integrand_snd ((hg.continuous_deriv le_rfl).ae_measurable _),
  have h3 : ∀ x t, has_deriv_at (λ x, g (x - t)) (deriv g (x - t)) x,
  { intros x t,
  have h4 := (hg.differentiable le_rfl).differentiable_at.has_deriv_at,
  have h5 := ((has_deriv_at_id x).sub (has_deriv_at_const x t)),
  have h6 := @has_deriv_at.scomp _ _ _ _ _ x _ _ _ _ _ (λ x, x - t) _ _ _ h4 h5,
    simpa using h6 },
  let L := closed_ball x₀ 1 + - tsupport (deriv g),
  have hL : is_compact L := (is_compact_closed_ball x₀ 1).add hcg.deriv.neg,
  simp_rw [convolution],
  refine (has_deriv_at_integral_of_dominated_loc_of_deriv_le zero_lt_one
    (eventually_of_forall h1) _ _ _ _ _).2,
  { exact hcg.convolution_exists_right hf hg.continuous x₀ },
  { exact h2 x₀ },
  { exact L.indicator (λ t, ∥f t∥ * (⨆ x, ∥deriv g x∥)) },
  { refine eventually_of_forall (λ t x hx, _),
    refine le_indicator (λ t ht, _) (λ t ht, _) t,
    { rw [norm_smul],
      refine mul_le_mul_of_nonneg_left _ (norm_nonneg _),
      exact le_csupr ((hg.continuous_deriv le_rfl).norm.bdd_above_range_of_has_compact_support
        hcg.deriv.norm) (x - t) },
    { have : x - t ∉ support (deriv g),
      { refine mt (λ hxt, _) ht,
        refine ⟨_, _, ball_subset_closed_ball hx, neg_mem_neg.mpr (subset_closure hxt), _⟩,
        rw [neg_sub, add_sub_cancel'_right] },
      rw [nmem_support.mp this, smul_zero, norm_zero] } },
  { rw [integrable_indicator_iff hL.measurable_set], exact (hf hL).norm.mul_const _ },
  { exact eventually_of_forall (λ t x hx, (h3 x t).const_smul _) },
end

lemma times_cont_diff_convolution_left (hcf : has_compact_support f) (hf : times_cont_diff ℝ n f)
  (hg : locally_integrable g) : times_cont_diff ℝ n (f ⋆ g) :=
begin
  induction n using with_top.nat_induction with n ih ih generalizing f,
  { rw [times_cont_diff_zero] at hf ⊢,
    exact hcf.continuous_convolution_left hf hg },
  { have h : ∀ x, has_deriv_at (f ⋆ g) ((deriv f ⋆ g) x) x :=
      hcf.has_deriv_at_convolution_left hf.one_of_succ hg,
    rw times_cont_diff_succ_iff_deriv,
    split,
    { exact λ x₀, ⟨_, h x₀⟩ },
    { rw deriv_eq h, exact ih hcf.deriv (times_cont_diff_succ_iff_deriv.mp hf).2 } },
  { rw [times_cont_diff_top] at hf ⊢, exact λ n, ih n hcf (hf n) }
end

lemma times_cont_diff_convolution_right (hf : locally_integrable f) (hcg : has_compact_support g)
  (hg : times_cont_diff ℝ n g) : times_cont_diff ℝ n (f ⋆ g) :=
begin
  induction n using with_top.nat_induction with n ih ih generalizing g,
  { rw [times_cont_diff_zero] at hg ⊢,
    exact hcg.continuous_convolution_right hf hg },
  { have h : ∀ x, has_deriv_at (f ⋆ g) ((f ⋆ deriv g) x) x :=
      hcg.has_deriv_at_convolution_right hf hg.one_of_succ,
    rw times_cont_diff_succ_iff_deriv,
    split,
    { exact λ x₀, ⟨_, h x₀⟩ },
    { rw deriv_eq h, exact ih  hcg.deriv (times_cont_diff_succ_iff_deriv.mp hg).2 } },
  { rw [times_cont_diff_top] at hg ⊢, exact λ n, ih n hcg (hg n) }
end

-- lemma times_cont_diff_convolution_right (hf : continuous f) (hg : times_cont_diff 𝕜 n g) :
--   times_cont_diff 𝕜 n (f ⋆[μ] g) :=
-- times_cont_diff_parametric_primitive_of_times_cont_diff _ _ _

-- lemma times_cont_diff_convolution_left (hf : times_cont_diff 𝕜 n f) (hg : continuous g) :
--   times_cont_diff 𝕜 n (f ⋆[μ] g) :=
-- sorry

end real

section comm_group

variables  [nondiscrete_normed_field 𝕜] [measurable_space 𝕜] [borel_space 𝕜] [complete_space 𝕜]
  [normed_space ℝ 𝕜] [second_countable_topology 𝕜] [smul_comm_class ℝ 𝕜 𝕜]
  [add_comm_group G] [topological_space G] [topological_add_group G] [borel_space G]
  [second_countable_topology G] [sigma_finite μ]
  [is_neg_invariant μ] [is_add_left_invariant μ]
  {f g h : G → 𝕜} {x x' : G} {y y' : R}

lemma convolution_comm : f ⋆[μ] g = g ⋆[μ] f :=
by { ext, rw [convolution_eq_swap, convolution_def], simp_rw [smul_eq_mul, mul_comm] }

end comm_group

section is_R_or_C

variables [is_R_or_C 𝕜] --[measurable_space 𝕜] [borel_space 𝕜] [complete_space 𝕜]
  [normed_space ℝ 𝕜] [second_countable_topology 𝕜] [smul_comm_class ℝ 𝕜 𝕜]
  [add_comm_group G] [topological_space G] [topological_add_group G] [borel_space G]
  [second_countable_topology G] [sigma_finite μ]
  [is_neg_invariant μ] [is_add_left_invariant μ]
  {f g h : G → 𝕜} {x x' : G} {y y' : R}

lemma convolution_assoc : (f ⋆[μ] g) ⋆[μ] h = f ⋆[μ] (g ⋆[μ] h) :=
by { ext, simp_rw [convolution_def, ← integral_smul/-, ← integral_smul_const-/], sorry  }

end is_R_or_C

-- end measure_theory
