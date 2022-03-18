import measure_theory.integral.interval_integral
import measure_theory.group.action
import measure_theory.measure.haar_lebesgue
import measure_theory.group.integration
import to_mathlib.measure_theory.parametric_interval_integral
import analysis.calculus.fderiv_measurable
import analysis.calculus.specific_functions

noncomputable theory
open topological_space measure_theory function set measure_theory.measure
open_locale pointwise topological_space nnreal measure_theory
open filter (hiding map_map map_id map map_id')


/-!
This file defines the convolution on two vector values functions, with as domain a group `G` with a
Haar measure. These functions are "multiplied" in the integrand using some continuous bilinear map.

This seems to not be a common version in math (In Bourbaki and various other books on analysis the
functions are only valued in ℝ or ℂ).
It doesn't seem to exist in Isabelle (some results containing the word convolution, but not
convolution of functions:
https://arxiv.org/pdf/1702.04603.pdf
https://isabelle.in.tum.de/library/HOL/HOL-Probability/document.pdf )

This version is useful and necessary if we even want to write something like
`fderiv ℝ (f ⋆ g) = fderiv ℝ f ⋆ g` (this doesn't typecheck if `f ⋆ g` is only defined where `f` is
scalar-valued and `g` is vector-valued)

TODO:
* Generalize abelian groups to groups, where possible
* [maybe] generalize bilinear map to special bilinear map
* Currently the definition of `convolution` works better with measures that are right-invariant.
  Perhaps we should reverse this.

-/

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


open metric
section

variables {α : Type*} [measurable_space α]
-- [topological_space α]
-- [opens_measurable_space α]
{μ : measure α}
-- [is_locally_finite_measure μ]
  {𝕜 : Type*} [is_R_or_C 𝕜]
          {E : Type*} [normed_group E] [normed_space ℝ E] [normed_space 𝕜 E]
          [complete_space E] [second_countable_topology E]
          [measurable_space E] [borel_space E]
          {H : Type*} [normed_group H] --[normed_space ℝ H]
          [normed_space 𝕜 H]
          [second_countable_topology $ H →L[𝕜] E]
          -- [proper_space H]

-- maybe: make F' explicit
lemma has_fderiv_at_integral_of_dominated_of_fderiv_le' {F : H → α → E} (F' : H → α → (H →L[𝕜] E))
  {x₀ : H} {bound : α → ℝ}
  {ε : ℝ} (ε_pos : 0 < ε)
  (hF_meas : ∀ᶠ x in 𝓝 x₀, ae_measurable (F x) μ)
  (hF_int : integrable (F x₀) μ)
  (hF'_meas : ae_measurable (F' x₀) μ)
  (h_bound : ∀ᵐ a ∂μ, ∀ x ∈ ball x₀ ε, ∥F' x a∥ ≤ bound a)
  (bound_integrable : integrable (bound : α → ℝ) μ)
  (h_diff : ∀ᵐ a ∂μ, ∀ x ∈ ball x₀ ε, has_fderiv_at (λ x, F x a) (F' x a) x) :
  has_fderiv_at (λ x, ∫ a, F x a ∂μ) (∫ a, F' x₀ a ∂μ) x₀ :=
has_fderiv_at_integral_of_dominated_of_fderiv_le ε_pos hF_meas hF_int hF'_meas h_bound bound_integrable h_diff

-- version similar to https://encyclopediaofmath.org/wiki/Parameter-dependent_integral#References
-- probably not useful
-- lemma has_fderiv_at_integral' {F : H → α → E} {bound : α → ℝ}
--   {x₀ : H}
--   -- (hF_int : integrable (F x₀) μ) -- we only need this for one value(!?)
--   (hF_int : ∀ᶠ x in 𝓝 x₀, integrable (F x) μ)
--   -- (h_diff : ∀ x, ∀ᵐ a ∂μ, cont_diff_at ℝ 1 (λ x, F x a) x)
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

-- lemma cont_diff_one_integral {F : H → α → E}
--   (hF_int : ∀ x, integrable (F x) μ)
--   (hF'_int : ∀ x, integrable (λ a, partial_fderiv_fst ℝ F x a) μ)
--   (h_diff : ∀ a, differentiable ℝ (λ x, F x a))
--   (h_cont : continuous ↿(partial_fderiv_fst ℝ F)) :
--   cont_diff ℝ 1 (λ x, ∫ a, F x a ∂μ) :=
-- begin
--   simp_rw [cont_diff_one_iff_fderiv],
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
--   --   -- have := (h_diff a).cont_diff_at,
--   --   have := (h_diff a).cont_diff_at.exists_lipschitz_on_with_of_nnnorm_lt (_ + ⟨f a, (h2f a).le⟩)
--   --     (lt_of_pos_right _ _), sorry }
--   all_goals { sorry },
-- end
-- #print is_compact.exists_forall_ge
-- version similar to https://encyclopediaofmath.org/wiki/Parameter-dependent_integral#References
-- lemma cont_diff_one_integral_compact
--  [topological_space α] [t2_space α] [opens_measurable_space α] [is_locally_finite_measure μ]
--   {F : H → α → E} {x₀ : H}
--   (h_diff : ∀ᵐ a ∂μ, cont_diff ℝ 1 (λ x, F x a))
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

variables {𝕜 G G₀ X Y M R E E' E'' F : Type*}

section continuous_bilinear_map

variables [nondiscrete_normed_field 𝕜]
  [normed_group E] [normed_group E'] [normed_group E''] [normed_group F]
  [normed_space 𝕜 E] [normed_space 𝕜 E'] [normed_space 𝕜 E''] [normed_space 𝕜 F]

variables {f f' : G → E} {g g' : G → E'}
    {x x' : G} {y y' : E}

namespace continuous_linear_map

lemma map_add_left (L : E →L[𝕜] E' →L[𝕜] F) {x x' : E} {y : E'} : L (x + x') y = L x y + L x' y :=
by rw [L.map_add, continuous_linear_map.add_apply]

lemma map_add_right (L : E →L[𝕜] E' →L[𝕜] F) {x : E} {y y' : E'} : L x (y + y') = L x y + L x y' :=
(L x).map_add y y'

lemma map_smul_left (L : E →L[𝕜] E' →L[𝕜] F) {c : 𝕜} {x : E} {y : E'} : L (c • x) y = c • L x y :=
by rw [L.map_smul, smul_apply]

lemma map_smul_right (L : E →L[𝕜] E' →L[𝕜] F) {c : 𝕜} {x : E} {y : E'} : L x (c • y) = c • L x y :=
(L x).map_smul c y

lemma map_zero_left (L : E →L[𝕜] E' →L[𝕜] F) {y : E'} : L 0 y = 0 :=
by rw [L.map_zero, zero_apply]

lemma map_zero_right (L : E →L[𝕜] E' →L[𝕜] F) {x : E} : L x 0 = 0 :=
(L x).map_zero

lemma continuous₂ (L : E →L[𝕜] E' →L[𝕜] F) : continuous (uncurry (λ x y, L x y)) :=
L.is_bounded_bilinear_map.continuous

lemma continuous_comp₂ [topological_space X] (L : E →L[𝕜] E' →L[𝕜] F) {f : X → E} {g : X → E'}
  (hf : continuous f) (hg : continuous g) : continuous (λ x, L (f x) (g x)) :=
L.continuous₂.comp $ hf.prod_mk hg

lemma has_fderiv_at_const_left [normed_group X] [normed_space 𝕜 X]
  (L : E →L[𝕜] E' →L[𝕜] F) {f : X → E'} {f' : X →L[𝕜] E'}
  (x : X) {c : E} (hf : has_fderiv_at f f' x) : has_fderiv_at (λ x, L c (f x)) ((L c).comp f') x :=
(L c).has_fderiv_at.comp x hf

lemma has_fderiv_at_const_right [normed_group X] [normed_space 𝕜 X]
  (L : E →L[𝕜] E' →L[𝕜] F) {f : X → E} {f' : X →L[𝕜] E}
  (x : X) {c : E'}
  (hf : has_fderiv_at f f' x) : has_fderiv_at (λ x, L (f x) c) ((flip L c).comp f') x :=
(flip L).has_fderiv_at_const_left x hf

section

variables [measurable_space E] [measurable_space E'] [measurable_space F] [measurable_space X]
  [opens_measurable_space E] [opens_measurable_space E'] [second_countable_topology E]
  [second_countable_topology E'] [borel_space F]

lemma ae_measurable_comp₂ {μ : measure X} (L : E →L[𝕜] E' →L[𝕜] F) {f : X → E} {g : X → E'}
  (hf : ae_measurable f μ) (hg : ae_measurable g μ) : ae_measurable (λ x, L (f x) (g x)) μ :=
L.continuous₂.measurable.comp_ae_measurable $ hf.prod_mk hg

end


variables (E'')

/--  Apply the bilinear map pointwise on the second argument -/
@[simps apply]
def precompR (L : E →L[𝕜] E' →L[𝕜] F) : E →L[𝕜] (E'' →L[𝕜] E') →L[𝕜] (E'' →L[𝕜] F) :=
(continuous_linear_map.compL 𝕜 E'' E' F).comp L

/--  Apply the bilinear map pointwise on the second argument -/
def precompL (L : E →L[𝕜] E' →L[𝕜] F) : (E'' →L[𝕜] E) →L[𝕜] E' →L[𝕜] (E'' →L[𝕜] F) :=
(precompR E'' (flip L)).flip

end continuous_linear_map

end continuous_bilinear_map

section general_measure
variables
  [measurable_space G] [measurable_space G₀] [measurable_space X] [measurable_space Y]
  [normed_group E] [normed_group E'] [normed_group E''] [normed_group F]
  [normed_space ℝ E] [normed_space ℝ E'] [normed_space ℝ E'']
  {μ : measure G}

namespace measure_theory

section integrable
open measure topological_space
-- variables {f : G → E} {g : G} [measurable_space G] [normed_group E] [second_countable_topology E] [normed_space ℝ E] [complete_space E] [measurable_space E] [borel_space E] [normed_group F] [measurable_space F] [opens_measurable_space F] [group G] [has_measurable_mul G] [has_measurable_inv G]
variables [group G] [has_measurable_mul G] [has_measurable_inv G] [measurable_space F]
  [opens_measurable_space F]

variables (μ)
@[to_additive]
lemma integrable_comp_div_left (f : G → F)
  [is_inv_invariant μ] [is_mul_left_invariant μ] (g : G) :
  integrable (λ t, f (g / t)) μ ↔ integrable f μ :=
begin
  refine ⟨λ h, _, λ h, h.comp_div_left g⟩,
  convert h.comp_inv.comp_mul_left g⁻¹,
  simp_rw [div_inv_eq_mul, mul_inv_cancel_left]
end

end integrable

variables [normed_space ℝ F]
variables [second_countable_topology E] [complete_space E] [measurable_space E] [borel_space E]


section smul
variables [group G] [mul_action G X] [has_measurable_smul G X]

@[to_additive]
lemma integral_smul_eq_self {μ : measure X} [smul_invariant_measure G X μ] (f : X → E) {m : G} :
  ∫ x, f (m • x) ∂μ = ∫ x, f x ∂μ :=
begin
  have h : measurable_embedding (λ x : X, m • x) :=
  (measurable_equiv.smul m).measurable_embedding,
  rw [← h.integral_map, map_smul]
end

end smul


section mul

variables [group G] {A : set G}
variables {f : G → E}

section has_measurable_mul
variables [has_measurable_mul G]

@[to_additive]
lemma integral_div_right_eq_self
  (f : G → E) (μ : measure G) [is_mul_right_invariant μ] (x' : G) :
  ∫ x, f (x / x') ∂μ = ∫ x, f x ∂μ :=
by simp_rw [div_eq_mul_inv, integral_mul_right_eq_self f x'⁻¹]

end has_measurable_mul

section

variables [has_measurable_mul₂ G] [has_measurable_inv G]
variables (μ) [sigma_finite μ]

lemma quasi_measure_preserving.prod_of_right {α β γ} [measurable_space α] [measurable_space β]
  [measurable_space γ] {f : α × β → γ} {μ : measure α} {ν : measure β} {τ : measure γ}
  (hf : measurable f) [sigma_finite ν]
  (h2f : ∀ x, quasi_measure_preserving (λ y, f (x, y)) ν τ) :
  quasi_measure_preserving f (μ.prod ν) τ :=
begin
  refine ⟨hf, _⟩,
  refine absolutely_continuous.mk (λ s hs h2s, _),
  simp_rw [map_apply hf hs, prod_apply (hf hs), preimage_preimage, (h2f _).preimage_null h2s,
    lintegral_zero],
end

lemma quasi_measure_preserving.prod_of_left {α β γ} [measurable_space α] [measurable_space β]
  [measurable_space γ] {f : α × β → γ} {μ : measure α} {ν : measure β} {τ : measure γ}
  (hf : measurable f) [sigma_finite μ] [sigma_finite ν]
  (h2f : ∀ y, quasi_measure_preserving (λ x, f (x, y)) μ τ) :
  quasi_measure_preserving f (μ.prod ν) τ :=
begin
  refine ⟨hf, _⟩,
  refine absolutely_continuous.mk (λ s hs h2s, _),
  simp_rw [map_apply hf hs, prod_apply_symm (hf hs), preimage_preimage, (h2f _).preimage_null h2s,
    lintegral_zero],
end

@[to_additive]
lemma quasi_measure_preserving_div [is_mul_right_invariant μ] :
  quasi_measure_preserving (λ (p : G × G), p.1 / p.2) (μ.prod μ) μ :=
begin
  refine quasi_measure_preserving.prod_of_left measurable_div _,
  simp_rw [div_eq_mul_inv],
  refine λ y, ⟨measurable_mul_const y⁻¹, (map_mul_right_eq_self μ y⁻¹).absolutely_continuous⟩
end

variables [is_mul_left_invariant μ]

@[to_additive]
lemma map_inv_absolutely_continuous : map has_inv.inv μ ≪ μ :=
(quasi_measure_preserving_inv μ).absolutely_continuous

@[to_additive]
lemma absolutely_continuous_map_inv : μ ≪ map has_inv.inv μ :=
begin
  refine absolutely_continuous.mk (λ s hs, _),
  rw [map_apply measurable_inv hs, measure_inv_null], exact id
end

@[to_additive] lemma quasi_measure_preserving_mul_right (g : G) :
  quasi_measure_preserving (λ h : G, h * g) μ μ :=
begin
  refine ⟨measurable_mul_const g, absolutely_continuous.mk $ λ s hs, _⟩,
  rw [map_apply (measurable_mul_const g) hs, measure_mul_right_null], exact id,
end

@[to_additive]
lemma map_mul_right_absolutely_continuous (g : G) : map (* g) μ ≪ μ :=
(quasi_measure_preserving_mul_right μ g).absolutely_continuous

@[to_additive]
lemma absolutely_continuous_map_mul_right (g : G) : μ ≪ map (* g) μ :=
begin
  refine absolutely_continuous.mk (λ s hs, _),
  rw [map_apply (measurable_mul_const g) hs, measure_mul_right_null], exact id
end

@[to_additive] lemma quasi_measure_preserving_div_left (g : G) :
  quasi_measure_preserving (λ h : G, g / h) μ μ :=
begin
  refine ⟨measurable_const.div measurable_id, _⟩,
  simp_rw [div_eq_mul_inv],
  rw [← map_map (measurable_const_mul g) measurable_inv],
  refine ((map_inv_absolutely_continuous μ).map _).trans _,
  rw [map_mul_left_eq_self],
end

@[to_additive]
lemma map_div_left_absolutely_continuous (g : G) : map (λ h, g / h) μ ≪ μ :=
(quasi_measure_preserving_div_left μ g).absolutely_continuous

@[to_additive]
lemma absolutely_continuous_map_div_left (g : G) : μ ≪ map (λ h, g / h) μ :=
begin
  simp_rw [div_eq_mul_inv],
  rw [← map_map (measurable_const_mul g) measurable_inv],
  conv_lhs { rw [← map_mul_left_eq_self μ g] },
  apply (absolutely_continuous_map_inv μ).map,
end

end

end mul

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

end measure_theory



end general_measure

open measure_theory measure_theory.measure

section preparation

variables [nondiscrete_normed_field 𝕜]
variables [normed_group E] [normed_group E'] [normed_group E''] [normed_group F]
variables [normed_space 𝕜 E] [normed_space 𝕜 E'] [normed_space 𝕜 E''] [normed_space 𝕜 F]
variables {f f' : G → E} {g g' : G → E'}
variables {L : E →L[𝕜] E' →L[𝕜] F}

section
variables [add_group G] [topological_space G] [has_continuous_sub G]
lemma continuous.convolution_integrand_snd (hf : continuous f) (hg : continuous g) (x : G) :
  continuous (λ t, L (f t) (g (x - t))) :=
L.continuous_comp₂ hf (hg.comp $ continuous_const.sub continuous_id)

lemma continuous.convolution_integrand_swap_snd (hf : continuous f) (hg : continuous g) (x : G) :
  continuous (λ t, L (f (x - t)) (g t)) :=
L.continuous_comp₂ (hf.comp $ continuous_const.sub continuous_id) hg
end

section
variables [measurable_space G] {μ : measure G}
variables [measurable_space E'] [opens_measurable_space E']

lemma integral_norm_bilinear_le_right (g : G → E') (c : E) (hg : integrable g μ) :
  ∥∫ x, ∥L c (g x)∥ ∂μ∥ ≤ ∥L∥ * ∥c∥ * ∫ x, ∥g x∥ ∂μ :=
begin
  simp_rw [← integral_mul_left],
  rw [real.norm_of_nonneg],
  { exact integral_mono_of_nonneg (eventually_of_forall $ λ t, norm_nonneg _) (hg.norm.const_mul _)
      (eventually_of_forall $ λ t, L.le_op_norm₂ _ _) },
  exact integral_nonneg (λ x, norm_nonneg _),
end

end

end preparation

section before_diff

variables [nondiscrete_normed_field 𝕜]
  [measurable_space G] [measurable_space G₀] [measurable_space X]
  [normed_group E] [normed_group E'] [normed_group E''] [normed_group F]
  [normed_space 𝕜 E] [normed_space 𝕜 E'] [normed_space 𝕜 E''] [normed_space 𝕜 F]
  {μ : measure G}

variables {f f' : G → E} {g g' : G → E'}
    {x x' : G} {y y' : E}
-- variables [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [smul_comm_class 𝕜 𝕜 E]
variables {L : E →L[𝕜] E' →L[𝕜] F}

local notation x ` ◾ `:67 y := L x y -- maybe

variables [measurable_space F]

/-- The convolution of `f` and `g` exists at `x` when the function `t ↦ f t * g (x - t)` is
  integrable. There are various conditions on `f` and `g` to prove this. -/
def convolution_exists_at [has_sub G] (f : G → E) (g : G → E') (x : G) (L : E →L[𝕜] E' →L[𝕜] F)
  (μ : measure G . volume_tac) : Prop :=
integrable (λ t, L (f t) (g (x - t))) μ

/-- The convolution of `f` and `g` exists when the function `t ↦ f t * g (x - t)` is integrable
  for all `x : G`. There are various conditions on `f` and `g` to prove this. -/
def convolution_exists [has_sub G] (f : G → E) (g : G → E') (L : E →L[𝕜] E' →L[𝕜] F)
  (μ : measure G . volume_tac) : Prop :=
∀ x : G, convolution_exists_at f g x L μ

section

lemma convolution_exists_at.integrable [has_sub G] {x : G} (h : convolution_exists_at f g x L μ) :
  integrable (λ t, L (f t) (g (x - t))) μ :=
h

variables [add_group G]
-- variables [opens_measurable_space F]

variables (L)

variables [measurable_space E] [measurable_space E'] [borel_space E] [borel_space E']
  [second_countable_topology E] [second_countable_topology E']
variables [has_measurable_add₂ G] [has_measurable_neg G]
variables [sigma_finite μ] [is_add_left_invariant μ]
variables [borel_space F]

lemma ae_measurable.convolution_integrand_snd
  (hf : ae_measurable f μ) (hg : ae_measurable g μ)
  (x : G) : ae_measurable (λ t, L (f t) (g (x - t))) μ :=
begin
  refine L.ae_measurable_comp₂ hf (ae_measurable.comp_measurable _ $ measurable_id.const_sub x),
  exact hg.mono' (map_sub_left_absolutely_continuous μ x)
end

lemma ae_measurable.convolution_integrand_swap_snd (hf : ae_measurable f μ) (hg : ae_measurable g μ)
  (x : G) : ae_measurable (λ t, L (f (x - t)) (g t)) μ :=
begin
  refine L.ae_measurable_comp₂ (ae_measurable.comp_measurable _ $ measurable_id.const_sub x) hg,
  exact hf.mono' (map_sub_left_absolutely_continuous μ x)
end

variables {L}



end

variables [normed_space ℝ F]
variables [second_countable_topology F] [borel_space F] [complete_space F]

/-- The convolution of two functions `f` and `g`. -/
def convolution [has_sub G] (f : G → E) (g : G → E') (L : E →L[𝕜] E' →L[𝕜] F)
  (μ : measure G . volume_tac) : G → F :=
λ x, ∫ t, L (f t) (g (x - t)) ∂μ

localized "notation f ` ⋆[`:67 L:67 `; `:67 μ:67 `] `:0 g:66 := convolution f g L μ" in convolution
localized "notation f ` ⋆[`:67 L:67 `]`:0 g:66 := convolution f g L
  measure_theory.measure_space.volume" in convolution
localized "notation f ` ⋆ `:67 g:66 := convolution f g (continuous_linear_map.lsmul ℝ ℝ)
  measure_theory.measure_space.volume" in convolution

lemma convolution_def [has_sub G] : (f ⋆[L; μ] g) x = ∫ t, L (f t) (g (x - t)) ∂μ := rfl

section noncomm

variables [add_group G]

lemma smul_convolution [smul_comm_class ℝ 𝕜 F] [measurable_space 𝕜] [opens_measurable_space 𝕜]
  {y : 𝕜} : (y • f) ⋆[L; μ] g = y • (f ⋆[L; μ] g) :=
by { ext, simp only [pi.smul_apply, convolution_def, ← integral_smul, L.map_smul_left] }

lemma convolution_smul [smul_comm_class ℝ 𝕜 F] [measurable_space 𝕜] [opens_measurable_space 𝕜]
  {y : 𝕜} : f ⋆[L; μ] (y • g) = y • (f ⋆[L; μ] g) :=
by { ext, simp only [pi.smul_apply, convolution_def, ← integral_smul, L.map_smul_right] }

lemma convolution_exists_at.distrib_add {x : G} (hfg : convolution_exists_at f g x L μ)
  (hfg' : convolution_exists_at f g' x L μ) :
  (f ⋆[L; μ] (g + g')) x = (f ⋆[L; μ] g) x + (f ⋆[L; μ] g') x :=
by simp only [convolution_def, L.map_add_right, pi.add_apply, integral_add hfg hfg']

lemma convolution_exists.distrib_add (hfg : convolution_exists f g L μ)
  (hfg' : convolution_exists f g' L μ) : f ⋆[L; μ] (g + g') = f ⋆[L; μ] g + f ⋆[L; μ] g' :=
by { ext, exact (hfg x).distrib_add (hfg' x) }

lemma convolution_exists_at.add_distrib {x : G} (hfg : convolution_exists_at f g x L μ)
  (hfg' : convolution_exists_at f' g x L μ) :
  ((f + f') ⋆[L; μ] g) x = (f ⋆[L; μ] g) x + (f' ⋆[L; μ] g) x :=
by simp only [convolution_def, L.map_add_left, pi.add_apply, integral_add hfg hfg']

lemma convolution_exists.add_distrib (hfg : convolution_exists f g L μ)
  (hfg' : convolution_exists f' g L μ) : (f + f') ⋆[L; μ] g = f ⋆[L; μ] g + f' ⋆[L; μ] g :=
by { ext, exact (hfg x).add_distrib (hfg' x) }

end noncomm

section comm

variables [add_comm_group G] [topological_space G] [topological_add_group G]
variables [borel_space G]
variables [is_add_left_invariant μ]
variables [opens_measurable_space F]


lemma convolution_exists_at_flip  [is_neg_invariant μ] :
  convolution_exists_at g f x L.flip μ ↔ convolution_exists_at f g x L μ :=
begin
  convert integrable_comp_sub_left μ (λ t, L (f t) (g (x - t))) x,
  ext t,
  simp_rw [sub_sub_cancel],
  refl,
end

lemma convolution_exists_at.integrable_swap [is_neg_invariant μ] (h : convolution_exists_at f g x L μ) :
  integrable (λ t, L (f (x - t)) (g t)) μ :=
by { convert h.comp_sub_left x, simp_rw [sub_sub_self], }

lemma convolution_exists_at_iff_integrable_swap [is_neg_invariant μ] :
  convolution_exists_at f g x L μ ↔ integrable (λ t, L (f (x - t)) (g t)) μ :=
convolution_exists_at_flip.symm

variable (L)
/- commutativity of convolution -/
lemma convolution_flip [is_neg_invariant μ] : g ⋆[L.flip; μ] f = f ⋆[L; μ] g :=
by { ext1 x, simp_rw [convolution_def], rw [← integral_sub_left_eq_self _ μ x],
  simp_rw [sub_sub_self], refl }
variable {L}

lemma convolution_eq_swap [is_neg_invariant μ] : (f ⋆[L; μ] g) x = ∫ t, L (f (x - t)) (g t) ∂μ :=
by { rw [← convolution_flip], refl }


variables [measurable_space E] [measurable_space E'] [borel_space E] [borel_space E']
  [second_countable_topology E] [second_countable_topology E']

variables (L) [complete_space E] [complete_space E']
variables [second_countable_topology G] [sigma_finite μ]

section sigma_finite

lemma ae_measurable.convolution_integrand (hf : ae_measurable f μ) (hg : ae_measurable g μ) :
  ae_measurable (λ p : G × G, L (f p.2) (g (p.1 - p.2))) (μ.prod μ) :=
begin
  refine L.ae_measurable_comp₂ hf.snd
    (ae_measurable.comp_measurable _ $ measurable_fst.sub measurable_snd),
  refine hg.mono' (quasi_measure_preserving_sub μ).absolutely_continuous,
end

lemma measure_theory.integrable.convolution_integrand (hf : integrable f μ) (hg : integrable g μ) :
  integrable (λ p : G × G, L (f p.2) (g (p.1 - p.2))) (μ.prod μ) :=
begin
  -- We can also do this for nonabelian groups, but this exact proof doesn't work
  -- for that case (we use that `μ` is right invariant here)
  have h_meas : ae_measurable (λ (p : G × G), (L (f p.2)) (g (p.1 - p.2))) (μ.prod μ) :=
  hf.ae_measurable.convolution_integrand L hg.ae_measurable,
  have h2_meas : ae_measurable (λ (y : G), ∫ (x : G), ∥(L (f y)) (g (x - y))∥ ∂μ) μ :=
  h_meas.prod_swap.norm.integral_prod_right',
  simp_rw [integrable_prod_iff' (hf.ae_measurable.convolution_integrand L hg.ae_measurable)],
  refine ⟨eventually_of_forall (λ t, (L (f t)).integrable_comp (hg.comp_sub_right t)), _⟩,
  refine integrable.mono' _ h2_meas (eventually_of_forall $
    λ t, integral_norm_bilinear_le_right (λ x, g (x - t)) (f t) (hg.comp_sub_right t)),
  simp_rw [integral_sub_right_eq_self (λ t, ∥ g t ∥) μ],
  exact (hf.norm.const_mul _).mul_const _,
end

lemma integrable.ae_convolution_exists [sigma_finite μ]
  (hf : integrable f μ) (hg : integrable g μ) : ∀ᵐ x ∂μ, convolution_exists_at f g x L μ :=
((integrable_prod_iff $ hf.ae_measurable.convolution_integrand L hg.ae_measurable).mp $
  hf.convolution_integrand L hg).1

lemma integrable.integrable_convolution (hf : integrable f μ) (hg : integrable g μ) :
  integrable (f ⋆[L; μ] g) μ :=
(hf.convolution_integrand L hg).integral_prod_left

end sigma_finite

lemma continuous.convolution_integrand_fst (hg : continuous g) (t : G) :
  continuous (λ x, L (f t) (g (x - t))) :=
L.continuous_comp₂ continuous_const $ hg.comp $ continuous_id.sub continuous_const

-- -- probably not that useful
-- lemma integrable.convolution_exists_of_bounded_range_left [sigma_compact_space G]
--   [is_neg_invariant μ]
--   (hbf : bounded (range f)) (hf : ae_measurable f μ)
--   (hcf : has_compact_support f) (hg : locally_integrable g μ) :
--   convolution_exists f g L μ :=
-- begin
--   intro x₀,
--   -- let K := (λ t, x₀ - t) '' tsupport f,
--   -- have hK : is_compact K := sorry,
--   have h2f : bdd_above (range (norm ∘ f)) := sorry,
--   have : ∀ᵐ (t : G) ∂μ, ∥f t ◾ g (x₀ - t)∥ ≤ (tsupport f).indicator (λ t, (⨆ i, ∥f i∥) * ∥g (x₀ - t)∥) t,
--   { refine eventually_of_forall _,
--     refine le_indicator (λ t ht, _) (λ t ht, _),
--     { have hL : ∀ x y, ∥L x y∥ = ∥x∥ * ∥y∥ := sorry, rw [hL],
--       refine mul_le_mul_of_nonneg_right (le_csupr h2f t) (norm_nonneg _) },
--     { have : t ∉ support f := mt (λ h, subset_closure h) ht,
--       rw [nmem_support.mp this, L.map_zero_left, norm_zero] } },
--   refine integrable.mono' _ (hf.convolution_integrand_snd hg.ae_measurable x₀) this,
--   { rw [integrable_indicator_iff (is_closed_add_tsupport f).measurable_set],
--   refine (integrable.norm _).const_mul _, sorry }
-- end

-- probably not that useful
-- lemma integrable.convolution_exists_of_bounded_range_right [normed_space ℝ 𝕜] (hf : integrable f μ)
--   (hbg : bounded (range g)) (hg : ae_measurable g μ) : convolution_exists f g L μ :=
-- begin
--   rcases hbg.subset_ball_lt 0 0 with ⟨C, h0C, hC⟩,
--   refine λ x, (hf.smul C).mono (hf.ae_measurable.convolution_integrand_snd hg x) _,
--   refine eventually_of_forall (λ t, _),
--   have hL : ∀ x y, ∥L x y∥ = ∥x∥ * ∥y∥ := sorry,
--   simp_rw [pi.smul_apply, hL, real.norm_of_nonneg h0C.le, mul_comm C],
--   refine mul_le_mul_of_nonneg_left _ (norm_nonneg _),
--   rw [← dist_zero_right],
--   exact hC ⟨x - t, rfl⟩
-- end

lemma bdd_above.convolution_exists_at [sigma_compact_space G] {x₀ : G}
  (hf : integrable_on f (tsupport (λ t, L (f t) (g (x₀ - t)))) μ)
  (hmf : ae_measurable f μ)
  (hbg : bdd_above ((λ i, ∥g i∥) '' ((λ t, x₀ - t) ⁻¹' tsupport (λ t, L (f t) (g (x₀ - t))))))
  (hmg : ae_measurable g μ) :
    convolution_exists_at f g x₀ L μ :=
begin
  simp at hbg,
  let K := tsupport (λ t, L (f t) (g (x₀ - t))),
  have hK : measurable_set K := is_closed_closure.measurable_set,
  let K' := (λ t, x₀ - t) ⁻¹' K,
  have : ∀ᵐ (t : G) ∂μ,
    ∥L (f t) (g (x₀ - t))∥ ≤ K.indicator (λ t, ∥L∥ * ∥f t∥ * ⨆ i : K', ∥g i∥) t,
  { refine eventually_of_forall _,
    refine le_indicator (λ t ht, _) (λ t ht, _),
    { refine (L.le_op_norm₂ _ _).trans _,
      refine mul_le_mul_of_nonneg_left
        (le_csupr_set hbg $ mem_preimage.mpr _)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)),
      rwa sub_sub_cancel },
    { have : t ∉ support (λ t, L (f t) (g (x₀ - t))) := mt (λ h, subset_closure h) ht,
      rw [nmem_support.mp this, norm_zero] } },
  refine integrable.mono' _ _ this,
  { rw [integrable_indicator_iff hK], exact (hf.norm.const_mul _).mul_const _ },
  { exact (hmf.convolution_integrand_snd L hmg x₀) }
end

lemma has_compact_support.convolution_exists_at [sigma_compact_space G] {x₀ : G}
  (h : has_compact_support (λ t, L (f t) (g (x₀ - t)))) (hf : locally_integrable f μ)
  (hg : continuous g) : convolution_exists_at f g x₀ L μ :=
(((homeomorph.sub_left x₀).compact_preimage.mpr h).bdd_above_image hg.norm.continuous_on)
  .convolution_exists_at L (hf h) hf.ae_measurable (hg.ae_measurable μ)

lemma has_compact_support.convolution_exists_right [sigma_compact_space G]
  (hf : locally_integrable f μ) (hcg : has_compact_support g) (hg : continuous g) :
  convolution_exists f g L μ :=
begin
  intro x₀,
  refine has_compact_support.convolution_exists_at L _ hf hg,
  refine (hcg.comp_homeomorph (homeomorph.sub_left x₀)).mono _,
  refine λ t, mt (λ ht : g (x₀ - t) = 0, _),
  simp [ht]
end

lemma has_compact_support.convolution_exists_left_of_continuous_right [sigma_compact_space G]
  (hcf : has_compact_support f) (hf : locally_integrable f μ) (hg : continuous g) :
  convolution_exists f g L μ :=
begin
  intro x₀,
  refine has_compact_support.convolution_exists_at L _ hf hg,
  refine hcf.mono _,
  refine λ t, mt (λ ht : f t = 0, _),
  simp [ht]
end

lemma has_compact_support.convolution_exists_left [is_neg_invariant μ] [sigma_compact_space G]
  (hcf : has_compact_support f) (hf : continuous f) (hg : locally_integrable g μ) :
  convolution_exists f g L μ :=
begin
  intro x₀, rw [← convolution_exists_at_flip],
  exact hcf.convolution_exists_right L.flip hg hf x₀
end

-- lemma has_compact_support.convolution_exists_right_of_continuous_left
--   [is_neg_invariant μ] [sigma_compact_space G]
--   (hf : continuous f) (hcg : has_compact_support g) (hg : locally_integrable g μ) :
--   convolution_exists f g L μ :=
-- begin
--   intro x₀,
--   refine has_compact_support.convolution_exists_at L _ hf hg,
--   refine hcf.mono _,
--   refine λ t, mt (λ ht : f t = 0, _),
--   simp [ht]
-- end


lemma bdd_above.continuous_convolution_right_of_integrable
  (hf : integrable f μ) (hbg : bdd_above (range (λ x, ∥g x∥))) (hg : continuous g) :
    continuous (f ⋆[L; μ] g) :=
begin
  sorry
  -- have : ∀ (x : G), ∀ᵐ (t : G) ∂μ, ∥L (f t) (g (x - t))∥ ≤ ∥f (⨆ i, ∥f i∥) * ∥g t∥,
  -- { refine λ x, eventually_of_forall (λ t, _),
  --   have hL : ∀ x y, ∥L x y∥ = ∥x∥ * ∥y∥ := sorry,
  --   rw [hL],
  --   refine mul_le_mul_of_nonneg_left (le_csupr hbg $ x - t) (norm_nonneg _) },
  -- rw [← convolution_flip],
  -- refine continuous_of_dominated _ this (hg.norm.const_mul _) _,
  -- { exact (hf.ae_measurable μ).convolution_integrand_swap_snd L hg.ae_measurable },
  -- exact eventually_of_forall (λ t,
  --   L.continuous_comp₂ (hf.comp (continuous_id.sub continuous_const)) continuous_const),
end

-- not useful?
lemma bdd_above.continuous_convolution_left_of_integrable [is_neg_invariant μ]
  (hbf : bdd_above (range (λ x, ∥f x∥))) (hf : continuous f) (hg : integrable g μ) :
    continuous (f ⋆[L; μ] g) :=
begin
  have : ∀ (x : G), ∀ᵐ (t : G) ∂μ, ∥L (f (x - t)) (g t)∥ ≤ (⨆ i, ∥f i∥) * ∥g t∥,
  { refine λ x, eventually_of_forall (λ t, _),
    have hL : ∀ x y, ∥L x y∥ = ∥x∥ * ∥y∥ := sorry,
    rw [hL],
    refine mul_le_mul_of_nonneg_right (le_csupr hbf $ x - t) (norm_nonneg _) },
  rw [← convolution_flip],
  refine continuous_of_dominated _ this (hg.norm.const_mul _) _,
  { exact (hf.ae_measurable μ).convolution_integrand_swap_snd L hg.ae_measurable },
  exact eventually_of_forall (λ t,
    L.continuous_comp₂ (hf.comp (continuous_id.sub continuous_const)) continuous_const),
end

/-- A version of `has_compact_support.continuous_convolution_left` that works if `G` is
  not locally compact but requires that `g` is integrable. -/
lemma has_compact_support.continuous_convolution_left_of_integrable [is_neg_invariant μ]
  (hcf : has_compact_support f) (hf : continuous f) (hg : integrable g μ) :
    continuous (f ⋆[L; μ] g) :=
(hf.norm.bdd_above_range_of_has_compact_support hcf.norm).continuous_convolution_left_of_integrable L
  hf hg

lemma has_compact_support.convolution_integrand_bound_right (hcg : has_compact_support g)
  (hg : continuous g) {x t : G} {s : set G} (hx : x ∈ s) :
  ∥L (f t) (g (x - t))∥ ≤ (s + - tsupport g).indicator (λ t, ∥L∥ * ∥f t∥ * (⨆ i, ∥g i∥)) t :=
begin
  refine le_indicator (λ t ht, _) (λ t ht, _) t,
  { refine (L.le_op_norm₂ _ _).trans _,
    refine mul_le_mul_of_nonneg_left
        (le_csupr (hg.norm.bdd_above_range_of_has_compact_support hcg.norm) $ x - t)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) },
  { have : x - t ∉ support g,
    { refine mt (λ hxt, _) ht, refine ⟨_, _, hx, neg_mem_neg.mpr (subset_closure hxt), _⟩,
      rw [neg_sub, add_sub_cancel'_right] },
    rw [nmem_support.mp this, L.map_zero_right, norm_zero] }
end

lemma has_compact_support.convolution_integrand_bound_left (hcf : has_compact_support f)
  (hf : continuous f) {x t : G} {s : set G} (hx : x ∈ s) :
  ∥L (f (x - t)) (g t)∥ ≤ (s + - tsupport f).indicator (λ t, ∥L∥ * (⨆ i, ∥f i∥) * ∥g t∥) t :=
by { convert hcf.convolution_integrand_bound_right L.flip hf hx,
  simp_rw [L.op_norm_flip, mul_right_comm] }

lemma has_compact_support.continuous_convolution_right [locally_compact_space G] [t2_space G]
  (hf : locally_integrable f μ) (hcg : has_compact_support g)
  (hg : continuous g) : continuous (f ⋆[L; μ] g) :=
begin
  rw [continuous_iff_continuous_at],
  intro x₀,
  obtain ⟨K, hK, h2K⟩ := exists_compact_mem_nhds x₀,
  let K' := K + - tsupport g,
  have hK' : is_compact K' := hK.add hcg.neg,
  have : ∀ᶠ x in 𝓝 x₀, ∀ᵐ (t : G) ∂μ,
    ∥L (f t) (g (x - t))∥ ≤ K'.indicator (λ t, ∥L∥ * ∥f t∥ * (⨆ i, ∥g i∥)) t :=
  eventually_of_mem h2K (λ x hx, eventually_of_forall $
    λ t, hcg.convolution_integrand_bound_right L hg hx),
  refine continuous_at_of_dominated _ this _ _,
  { exact eventually_of_forall (hf.ae_measurable.convolution_integrand_snd L (hg.ae_measurable μ)) },
  { rw [integrable_indicator_iff hK'.measurable_set], exact ((hf hK').norm.const_mul _).mul_const _ },
  { exact eventually_of_forall (λ t, (L.continuous_comp₂ continuous_const $
      hg.comp $ continuous_id.sub $ by apply continuous_const).continuous_at) }
end

lemma has_compact_support.continuous_convolution_left [locally_compact_space G] [t2_space G]
  [is_neg_invariant μ]
  (hcf : has_compact_support f) (hf : continuous f) (hg : locally_integrable g μ) :
    continuous (f ⋆[L; μ] g) :=
by { rw [← convolution_flip], exact hcf.continuous_convolution_right L.flip hg hf }

lemma support_convolution_subset : support (f ⋆[L; μ] g) ⊆ tsupport f + tsupport g :=
begin
  intros x h2x,
  refine set.add_subset_add subset_closure subset_closure _,
  by_contra hx,
  simp_rw [set.mem_add, not_exists, not_and_distrib, nmem_support] at hx,
  apply h2x,
  rw [convolution_def],
  convert integral_zero G F,
  ext t,
  rcases hx t (x - t) with h|h|h,
  { rw [h, L.map_zero_left], },
  { rw [h, L.map_zero_right], },
  { simp_rw [add_sub_cancel'_right] at h, exact (h rfl).elim }
end

lemma has_compact_support.convolution [t2_space G] (hcf : has_compact_support f)
  (hcg : has_compact_support g) : has_compact_support (f ⋆[L; μ] g) :=
begin
  refine compact_of_is_closed_subset (hcf.is_compact.add hcg) is_closed_closure _,
  exact closure_minimal (support_convolution_subset L) (hcf.is_compact.add hcg).is_closed
end

end comm

end before_diff


open_locale convolution

section normed_space

variables [is_R_or_C 𝕜] --[complete_space 𝕜]
variables [normed_group E] [normed_space 𝕜 E]
variables [normed_group E'] [normed_space 𝕜 E']
variables [normed_group F] [normed_space ℝ F] [normed_space 𝕜 F] [smul_comm_class 𝕜 ℝ F]
variables [normed_group G] [normed_space ℝ G] [normed_space 𝕜 G] [smul_comm_class 𝕜 ℝ G]
variables {f f' : G → E} {g g' : G → E'} {x x' : 𝕜}
variables {n : with_top ℕ}
variables (L : E →L[𝕜] E' →L[𝕜] F)
variables [complete_space E] [second_countable_topology E] [measurable_space E] [borel_space E]
variables [complete_space E'] [second_countable_topology E'] [measurable_space E'] [borel_space E']
variables [complete_space F] [second_countable_topology F] [measurable_space F] [borel_space F]
variables [measurable_space G] [borel_space G] {μ : measure G} [second_countable_topology G]
variables [is_add_left_invariant μ] [sigma_finite μ]
variables [sigma_compact_space G] [proper_space G] [is_locally_finite_measure μ]

-- lemma convolution_mem_convex_hull [normed_space ℝ E'] {x₀ : G} :
--   (f ⋆[L; μ] g) x₀ ∈ convex_hull ℝ ((λ x, g '' support f) :=
-- sorry

lemma dist_convolution [normed_space ℝ E] {x₀ : G} {R ε : ℝ}
  (hf : support f ⊆ ball (0 : G) R)
  (hg : ∀ x ∈ ball x₀ R, dist (g x) (g x₀) < ε) : dist ((f ⋆[L; μ] g) x₀) (∫ (t : G), (L (f t)) (g x₀) ∂μ) < ε :=
sorry


/-- We can only simplify the RHS further if we assume `f` is integrable, but also if `L = (•)`. -/
lemma convolution_eq_right' [normed_space ℝ E] {x₀ : G} {R : ℝ}
  (hf : support f ⊆ ball (0 : G) R)
  (hg : ∀ x ∈ ball x₀ R, g x = g x₀) : (f ⋆[L; μ] g) x₀ = ∫ (t : G), (L (f t)) (g x₀) ∂μ :=
begin
  have h2 : ∀ t, L (f t) (g (x₀ - t)) = L (f t) (g x₀),
  { intro t, by_cases ht : t ∈ support f,
    { have h2t := hf ht,
      rw [mem_ball_zero_iff] at h2t,
      specialize hg (x₀ - t),
      rw [sub_eq_add_neg, add_mem_ball_iff_norm, norm_neg, ← sub_eq_add_neg] at hg,
      rw [hg h2t] },
    { rw [nmem_support] at ht,
      simp_rw [ht, L.map_zero_left] } },
  simp_rw [convolution_def, h2],
end

end normed_space


section inner_product_space
open finite_dimensional
variables {f' f : G → E} {g' g : G → E'} {x' x : 𝕜} {n : with_top ℕ} [is_R_or_C 𝕜] [normed_group E] [normed_space 𝕜 E] [normed_group E'] [normed_space ℝ E'] [normed_space 𝕜 E'] [normed_group F] [normed_space ℝ F] [normed_space 𝕜 F] [smul_comm_class 𝕜 ℝ F] [inner_product_space ℝ G] [normed_space 𝕜 G] [smul_comm_class 𝕜 ℝ G] [complete_space E] [second_countable_topology E] [measurable_space E] [borel_space E] [complete_space E'] [second_countable_topology E'] [measurable_space E'] [borel_space E'] [complete_space F] [second_countable_topology F] [measurable_space F] [borel_space F] [measurable_space G] [borel_space G] [second_countable_topology G] [normed_group E''] [normed_space ℝ E''] [normed_space 𝕜 E''] [smul_comm_class 𝕜 ℝ E''] [complete_space E''] [second_countable_topology E''] [measurable_space E''] [borel_space E''] {μ : measure G} (L : E →L[𝕜] E' →L[𝕜] F)
[is_add_left_invariant μ] [sigma_finite μ] [sigma_compact_space G] [proper_space G] [is_locally_finite_measure μ]
variables [finite_dimensional ℝ G]
variables [second_countable_topology E'] [is_scalar_tower ℝ 𝕜 E']
variables (φ : cont_diff_bump_of_inner (0 : G))

def _root_.cont_diff_bump_of_inner.normed {a : G} (φ : cont_diff_bump_of_inner a) (μ : measure G)
  (x : G) : ℝ :=
φ x / ∫ x, φ x ∂μ

lemma _root_.cont_diff_bump_of_inner.integral_normed {a : G} (φ : cont_diff_bump_of_inner a) :
  ∫ x, φ.normed μ x ∂μ = 1 :=
sorry

lemma _root_.cont_diff_bump_of_inner.normed.has_compact_support {a : G}
  (φ : cont_diff_bump_of_inner a) : has_compact_support (φ.normed μ) :=
sorry

open continuous_linear_map
lemma cont_diff_bump_of_inner.convolution_eq_right {x₀ : G}
  (h : ∀ x ∈ ball x₀ φ.R, g x = g x₀) : (φ ⋆[lsmul ℝ ℝ; μ] g : G → E') x₀ = integral μ φ • g x₀ :=
by simp_rw [convolution_eq_right' _ φ.support_eq.subset h, lsmul_apply, integral_smul_const]

lemma cont_diff_bump_of_inner.tendsto {x₀ : G} (hf : continuous f) :
  tendsto (λ N : ℝ, ((λ x, N ^ finrank ℝ G • φ.normed μ (N • x)) ⋆[lsmul ℝ ℝ; μ] g : G → E') x₀)
    at_top (𝓝 (g x₀)) :=
begin
  sorry
end

end inner_product_space

section normed_space

variables [is_R_or_C 𝕜] --[complete_space 𝕜]
variables [normed_group E] [normed_space 𝕜 E]
variables [normed_group E'] [normed_space 𝕜 E']
variables [normed_group F] [normed_space ℝ F] [normed_space 𝕜 F] [smul_comm_class 𝕜 ℝ F]
variables [normed_group G] [normed_space ℝ G] [normed_space 𝕜 G] [smul_comm_class 𝕜 ℝ G]
variables {f f' : G → E} {g g' : G → E'} {x x' : 𝕜}
variables {n : with_top ℕ}
variables (L : E →L[𝕜] E' →L[𝕜] F)
variables [complete_space E] [second_countable_topology E] [measurable_space E] [borel_space E]
variables [complete_space E'] [second_countable_topology E'] [measurable_space E'] [borel_space E']
variables [complete_space F] [second_countable_topology F] [measurable_space F] [borel_space F]
variables [measurable_space G] [borel_space G] {μ : measure G} [second_countable_topology G]
variables [is_add_left_invariant μ] [sigma_finite μ]
variables [sigma_compact_space G] [proper_space G] [is_locally_finite_measure μ]

lemma has_compact_support.has_fderiv_at_convolution_right [finite_dimensional 𝕜 G]
  (hf : locally_integrable f μ) (hcg : has_compact_support g) (hg : cont_diff 𝕜 1 g)
  (x₀ : G) : has_fderiv_at (f ⋆[L; μ] g) ((f ⋆[L.precompR G; μ] fderiv 𝕜 g) x₀) x₀ :=
begin
  set L' := L.precompR G,
  have h1 : ∀ᶠ x in 𝓝 x₀, ae_measurable (λ t, L (f t) (g (x - t))) μ :=
  eventually_of_forall (hf.ae_measurable.convolution_integrand_snd L (hg.continuous.ae_measurable _)),
  have h2 : ∀ x, ae_measurable (λ t, L' (f t) (fderiv 𝕜 g (x - t))) μ,
  { exact hf.ae_measurable.convolution_integrand_snd L' ((hg.continuous_fderiv le_rfl).ae_measurable _) },
  have h3 : ∀ x t, has_fderiv_at (λ x, g (x - t)) (fderiv 𝕜 g (x - t)) x,
  { intros x t,
    simpa using (hg.differentiable le_rfl).differentiable_at.has_fderiv_at.comp x
      ((has_fderiv_at_id x).sub (has_fderiv_at_const t x)) },
  let K' := closed_ball x₀ 1 + - tsupport (fderiv 𝕜 g),
  have hK' : is_compact K' := (is_compact_closed_ball x₀ 1).add (hcg.fderiv 𝕜).neg,
  refine has_fderiv_at_integral_of_dominated_of_fderiv_le
    zero_lt_one h1 _ (h2 x₀) _ _ _,
  { exact K'.indicator (λ t, ∥L'∥ * ∥f t∥ * (⨆ x, ∥fderiv 𝕜 g x∥)) },
  { exact hcg.convolution_exists_right L hf hg.continuous x₀ },
  { refine eventually_of_forall (λ t x hx, _),
    exact (hcg.fderiv 𝕜).convolution_integrand_bound_right L'
      (hg.continuous_fderiv le_rfl) (ball_subset_closed_ball hx) },
  { rw [integrable_indicator_iff hK'.measurable_set], exact ((hf hK').norm.const_mul _).mul_const _ },
  { refine eventually_of_forall (λ t x hx, L.has_fderiv_at_const_left x (h3 x t)) },
end

lemma has_compact_support.has_fderiv_at_convolution_left [finite_dimensional 𝕜 G]
  [is_neg_invariant μ]
  (hcf : has_compact_support f) (hf : cont_diff 𝕜 1 f)
  (hg : locally_integrable g μ) (x₀ : G) :
  has_fderiv_at (f ⋆[L; μ] g) ((fderiv 𝕜 f ⋆[L.precompL G; μ] g) x₀) x₀ :=
begin
  simp only [← convolution_flip] {single_pass := tt},
  exact hcf.has_fderiv_at_convolution_right L.flip hg hf x₀,
end

variables [normed_group E''] [normed_space ℝ E''] [normed_space 𝕜 E''] [smul_comm_class 𝕜 ℝ E'']
variables [complete_space E''] [second_countable_topology E''] [measurable_space E''] [borel_space E'']

lemma convolution_precompR_apply [finite_dimensional 𝕜 G] [finite_dimensional 𝕜 E'']
  {g : G → E'' →L[𝕜] E'}
  (hf : locally_integrable f μ) (hcg : has_compact_support g) (hg : continuous g)
  (x₀ : G) (x : E'') : (f ⋆[L.precompR E''; μ] g) x₀ x = (f ⋆[L; μ] (λ a, g a x)) x₀  :=
begin
  have := hcg.convolution_exists_right (L.precompR E'') hf hg x₀,
  simp_rw [convolution_def, continuous_linear_map.integral_apply this],
  refl,
end

lemma has_compact_support.cont_diff_convolution_right [finite_dimensional 𝕜 G]
  (hf : locally_integrable f μ) (hcg : has_compact_support g)
  (hg : cont_diff 𝕜 n g) : cont_diff 𝕜 n (f ⋆[L; μ] g) :=
begin
  induction n using with_top.nat_induction with n ih ih generalizing g,
  { rw [cont_diff_zero] at hg ⊢,
    exact hcg.continuous_convolution_right L hf hg },
  { have h : ∀ x, has_fderiv_at (f ⋆[L; μ] g) ((f ⋆[L.precompR G; μ] fderiv 𝕜 g) x) x :=
      hcg.has_fderiv_at_convolution_right L hf hg.one_of_succ,
    rw cont_diff_succ_iff_fderiv_apply,
    split,
    { exact λ x₀, ⟨_, h x₀⟩ },
    { simp_rw [fderiv_eq h, convolution_precompR_apply L hf (hcg.fderiv 𝕜)
        (hg.continuous_fderiv (with_top.le_add_self 1 n))],
      intro x,
      refine ih _ _,
      { refine @has_compact_support.comp_left _ _ _ _ _ _ (λ (G : _ →L[𝕜] _), G x) _
          (hcg.fderiv 𝕜) (continuous_linear_map.zero_apply x) },
      { revert x, rw [← cont_diff_clm_apply],
        exact (cont_diff_succ_iff_fderiv.mp hg).2 } } },
  { rw [cont_diff_top] at hg ⊢, exact λ n, ih n hcg (hg n) }
end

lemma has_compact_support.cont_diff_convolution_left [finite_dimensional 𝕜 G]
  [is_neg_invariant μ]
  (hcf : has_compact_support f) (hf : cont_diff 𝕜 n f)
  (hg : locally_integrable g μ) (x₀ : G) :
  cont_diff 𝕜 n (f ⋆[L; μ] g) :=
begin
  rw [← convolution_flip],
  exact hcf.cont_diff_convolution_right L.flip hg hf,
end

-- associativity is quite tedious to write down in full generality

-- variables [normed_group E''] [normed_space ℝ E''] [normed_space 𝕜 E''] [smul_comm_class 𝕜 ℝ E'']
-- variables [complete_space E''] [second_countable_topology E''] [measurable_space E''] [borel_space E'']
-- variables {h : G → E''}
-- variables {L₂ : F →L[𝕜] E'' →L[𝕜] F'}


-- lemma convolution_assoc : (f ⋆[L; μ] g) ⋆[L'; μ] h = f ⋆[L; μ] (g ⋆[L; μ] h) :=
-- by { ext, simp_rw [convolution_def, ← integral_smul/-, ← integral_smul_const-/], sorry  }

section bump

variables [finite_dimensional ℝ G]
variables [normed_space ℝ E'] [second_countable_topology E'] [is_scalar_tower ℝ 𝕜 E']
variables (φ : cont_diff_bump (0 : G))
open continuous_linear_map

lemma cont_diff_bump.convolution_eq_right {x₀ : G}
  (h : ∀ x ∈ euclidean.ball x₀ φ.R, g x = g x₀) :
  (φ ⋆[lsmul ℝ ℝ; μ] g : G → E') x₀ = integral μ φ • g x₀ :=
begin
  have := φ.to_cont_diff_bump_of_inner,
  rw [to_euclidean.map_zero] at this,
  -- refine this.convolution_eq_right,
  sorry
end


end bump

end normed_space



section real
/-! The one-variable case -/

variables [is_R_or_C 𝕜] --[complete_space 𝕜]
variables [normed_group E] [normed_space ℝ E] [normed_space 𝕜 E] [smul_comm_class 𝕜 ℝ E]
variables [normed_group E'] [normed_space ℝ E'] [normed_space 𝕜 E'] [smul_comm_class 𝕜 ℝ E']
variables [normed_group F] [normed_space ℝ F] [normed_space 𝕜 F] [smul_comm_class 𝕜 ℝ F]
variables {f f' : 𝕜 → E} {g g' : 𝕜 → E'} {x x' : 𝕜}
variables {n : with_top ℕ}
variables (L : E →L[𝕜] E' →L[𝕜] F)
variables [complete_space E] [second_countable_topology E] [measurable_space E] [borel_space E]
variables [complete_space E'] [second_countable_topology E'] [measurable_space E'] [borel_space E']
variables [complete_space F] [second_countable_topology F] [measurable_space F] [borel_space F]
variables {μ : measure 𝕜}
variables [is_add_left_invariant μ] [sigma_finite μ]
variables [is_locally_finite_measure μ]

lemma has_compact_support.has_deriv_at_convolution_right
  (hf : locally_integrable f μ) (hcg : has_compact_support g) (hg : cont_diff 𝕜 1 g)
  (x₀ : 𝕜) :
  has_deriv_at (f ⋆[L; μ] g) ((f ⋆[L; μ] deriv g) x₀) x₀ :=
begin
  convert (hcg.has_fderiv_at_convolution_right L hf hg x₀).has_deriv_at,
  rw [convolution_precompR_apply L hf (hcg.fderiv 𝕜) (hg.continuous_fderiv le_rfl)],
  refl,
end

lemma has_compact_support.has_deriv_at_convolution_left [is_neg_invariant μ]
  (hcf : has_compact_support f) (hf : cont_diff 𝕜 1 f)
  (hg : locally_integrable g μ) (x₀ : 𝕜) :
  has_deriv_at (f ⋆[L; μ] g) ((deriv f ⋆[L; μ] g) x₀) x₀ :=
begin
  simp only [← convolution_flip] {single_pass := tt},
  exact hcf.has_deriv_at_convolution_right L.flip hg hf x₀,
end

end real
