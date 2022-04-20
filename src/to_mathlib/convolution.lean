/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import measure_theory.integral.interval_integral
import measure_theory.group.action
import measure_theory.measure.haar_lebesgue
import measure_theory.group.integration
import analysis.calculus.parametric_integral
import to_mathlib.analysis.calculus
import order.filter.small_sets
import analysis.calculus.fderiv_measurable
import analysis.calculus.specific_functions

/-!
# Convolution of functions

This file defines the convolution on two functions, i.e. `x ↦ ∫ f(t)g(x - t) ∂t`.
In the general case, these functions can be vector-valued, and have an arbitrary (additive)
group as domain. We use a continuous bilinear operation `L` on these function values as
"multiplication". The domain must be equipped with a measure Haar measure `μ`
(though many individual results have weaker conditions on `μ`).

For many applications we can take `L = lsmul ℝ ℝ` or `L = lmul ℝ ℝ`.

We also define `convolution_exists` and `convolution_exists_at` to state that the convolution is
well-defined (everywhere or at a single point). These conditions are needed for pointwise
computations (e.g. `convolution_exists_at.distrib_add`), but are generally not stong enough for any
local (or global) properties of the convolution. For this we need stronger assumptions on `f`
and/or `g`, and generally if we impose stronger conditions on one of the functions, we can impose
weaker conditions on the other.
We have proven many of the properties of the convolution assuming one of these functions
has compact support (in which case the other function only needs to be locally integrable).
We still need to prove the properties for other pairs of conditions (e.g. both functions are
rapidly decreasing)

# Design Decisions

We use a bilinear map `L` to "multiply" the two functions in the integrand.
This generality has several advantages

* This allows us to compute the total derivative of the convolution, in case the functions are
  multivariate. The total derivative is again a convolution, but where the codomains of the
  functions can be higher-dimensional. See `has_compact_support.has_fderiv_at_convolution_right`.
* This allows us to use `@[to_additive]` everywhere (which would not be possible if we would use
  `mul`/`smul` in the integral, since `@[to_additive]` will incorrectly also try to additivize
  those definitions).
* We need to support the case where at least one of the functions is vector-valued, but if we use
  `smul` to multiply the functions, that would be an asymmetric definition.

# Main Definitions

* `convolution f g L μ x = (f ⋆[L, μ] g) x = ∫ t, L (f t) (g (x - t)) ∂μ` is the convolution of
  `f` and `g` w.r.t. the continuous bilinear map `L` and.
* `convolution_exists_at f g x L μ` states that the convolution `(f ⋆[L, μ] g) x` is well-defined
  (i.e. the integral exists).
* `convolution_exists f g L μ` states that the convolution `f ⋆[L, μ] g` is well-defined at each
  point.

# Main Results
* `has_compact_support.has_fderiv_at_convolution_right` and
  `has_compact_support.has_fderiv_at_convolution_left`: we can compute the total derivative
  of the convolution as a convolution with the total derivative of the right (left) function.
* `has_compact_support.cont_diff_convolution_right` and
  `has_compact_support.cont_diff_convolution_left`: the convolution is `𝒞ⁿ` if one of the functions
  is `𝒞ⁿ` with compact support and the other function in locally integrable.
* `convolution_tendsto_right`: Given a sequence of nonnegative normalized functions whose support
  tends to a small neighborhood around `0`, the convolution tends to the right argument.
  This is specialized to bump functions in `cont_diff_bump_of_inner.convolution_tendsto_right`.

# Notation

The following notations are localized in the locale `convolution`:
* `f ⋆[L, μ] g` for the convolution. Note: you have to use parentheses to apply the convolution
  to an argument: `(f ⋆[L, μ] g) x`.
* `f ⋆[L] g := f ⋆[L, volume] g`
* `f ⋆ g := f ⋆[lsmul ℝ ℝ] g`

# To do

* Prove properties about the convolution if both functions are rapidly decreasing.
* Use `@[to_additive]` everywhere

# Personal notes

This seems to not be a common version in math (In Bourbaki and various other books on analysis the
functions are only valued in ℝ or ℂ).
It doesn't seem to exist in Isabelle (some results containing the word convolution, but not
convolution of functions:
https://arxiv.org/pdf/1702.04603.pdf
https://isabelle.in.tum.de/library/HOL/HOL-Probability/document.pdf )

TODO:
* [maybe] generalize bilinear map to special bilinear map
* Currently the definition of `convolution` works better with measures that are right-invariant.
  Perhaps we should reverse this.

-/


noncomputable theory
open topological_space measure_theory function set measure_theory.measure
open finite_dimensional continuous_linear_map metric
open_locale pointwise topological_space nnreal measure_theory
open filter (hiding map_map map_id map map_id')

namespace measure_theory

lemma ae_strongly_measurable.comp_measurable'
  {α β γ : Type*} [topological_space β]
  {mγ : measurable_space γ} {mα : measurable_space α} {f : γ → α} {g : α → β}
  {μ : measure γ} {ν : measure α}
  (hg : ae_strongly_measurable g ν) (hf : measurable f)
  (h : μ.map f ≪ ν) :
  ae_strongly_measurable (g ∘ f) μ :=
(hg.mono' h).comp_measurable hf

lemma ae_strongly_measurable.fst {α β γ : Type*} [measurable_space α] [measurable_space β]
  [topological_space γ] {μ : measure α} {ν : measure β}
  [sigma_finite ν] {f : α → γ}
  (hf : ae_strongly_measurable f μ) : ae_strongly_measurable (λ (z : α × β), f z.1) (μ.prod ν) :=
hf.comp_measurable' measurable_fst prod_fst_absolutely_continuous

lemma ae_strongly_measurable.snd {α β γ : Type*} [measurable_space α] [measurable_space β]
  [topological_space γ] {μ : measure α} {ν : measure β}
  [sigma_finite ν] {f : β → γ}
  (hf : ae_strongly_measurable f ν) : ae_strongly_measurable (λ (z : α × β), f z.2) (μ.prod ν) :=
hf.comp_measurable' measurable_snd prod_snd_absolutely_continuous

end measure_theory

section op_norm

theorem continuous_linear_map.dist_le_op_norm {𝕜 𝕜₂ E F : Type*}
  [semi_normed_group E] [semi_normed_group F]
  [nondiscrete_normed_field 𝕜] [nondiscrete_normed_field 𝕜₂] [normed_space 𝕜 E] [normed_space 𝕜₂ F]
  {σ₁₂ : 𝕜 →+* 𝕜₂} [ring_hom_isometric σ₁₂]
  (f : E →SL[σ₁₂] F) (x y : E) : dist (f x) (f y) ≤ ∥f∥ * dist x y :=
by simp_rw [dist_eq_norm, ← map_sub, f.le_op_norm]

end op_norm



variables {𝕜 G G₀ X Y M R E E' E'' F : Type*}

section continuous_bilinear_map

variables [nondiscrete_normed_field 𝕜]
  [normed_group E] [normed_group E'] [normed_group E''] [normed_group F]
  [normed_space 𝕜 E] [normed_space 𝕜 E'] [normed_space 𝕜 E''] [normed_space 𝕜 F]

variables {f f' : G → E} {g g' : G → E'}
    {x x' : G} {y y' : E}

namespace continuous_linear_map

variables [normed_group G] [normed_space 𝕜 G]

lemma map_add₂' (f : E →L[𝕜] F →L[𝕜] G) (x x' : E) (y : F) : f (x + x') y = f x y + f x' y :=
by rw [f.map_add, add_apply]

lemma map_sub₂ (f : E →L[𝕜] F →L[𝕜] G) (x x' : E) (y : F) : f (x - x') y = f x y - f x' y :=
by rw [f.map_sub, sub_apply]

lemma map_smul₂ (f : E →L[𝕜] F →L[𝕜] G) (c : 𝕜) (x : E) (y : F) : f (c • x) y = c • f x y :=
by rw [f.map_smul, smul_apply]

lemma map_zero₂ (f : E →L[𝕜] F →L[𝕜] G) (y : F) : f 0 y = 0 :=
by rw [f.map_zero, zero_apply]

lemma continuous₂ (L : E →L[𝕜] E' →L[𝕜] F) : continuous (uncurry (λ x y, L x y)) :=
L.is_bounded_bilinear_map.continuous

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

variables [measurable_space X] {μ : measure X}

lemma ae_strongly_measurable_comp₂ (L : E →L[𝕜] E' →L[𝕜] F) {f : X → E} {g : X → E'}
  (hf : ae_strongly_measurable f μ) (hg : ae_strongly_measurable g μ) :
  ae_strongly_measurable (λ x, L (f x) (g x)) μ :=
L.continuous₂.comp_ae_strongly_measurable $ hf.prod_mk hg

end


variables (E'')

/--  Apply the bilinear map pointwise on the second argument -/
@[simps apply]
def precompR (L : E →L[𝕜] E' →L[𝕜] F) : E →L[𝕜] (E'' →L[𝕜] E') →L[𝕜] (E'' →L[𝕜] F) :=
(compL 𝕜 E'' E' F).comp L

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

variables [group G] [has_measurable_mul G] [has_measurable_inv G]

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

variables [normed_space ℝ F] [complete_space E]

-- section smul
-- variables [group G] [mul_action G X] [has_measurable_smul G X]

-- @[to_additive]
-- lemma integral_smul_eq_self {μ : measure X} [smul_invariant_measure G X μ] (f : X → E) {m : G} :
--   ∫ x, f (m • x) ∂μ = ∫ x, f x ∂μ :=
-- begin
--   have h : measurable_embedding (λ x : X, m • x) :=
--   (measurable_equiv.smul m).measurable_embedding,
--   rw [← h.integral_map, map_smul]
-- end

-- end smul


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
  (h2f : ∀ᵐ x ∂μ, quasi_measure_preserving (λ y, f (x, y)) ν τ) :
  quasi_measure_preserving f (μ.prod ν) τ :=
begin
  refine ⟨hf, _⟩,
  refine absolutely_continuous.mk (λ s hs h2s, _),
  simp_rw [map_apply hf hs, prod_apply (hf hs), preimage_preimage,
    lintegral_congr_ae (h2f.mono (λ x hx, hx.preimage_null h2s)), lintegral_zero],
end

lemma quasi_measure_preserving.prod_of_left {α β γ} [measurable_space α] [measurable_space β]
  [measurable_space γ] {f : α × β → γ} {μ : measure α} {ν : measure β} {τ : measure γ}
  (hf : measurable f) [sigma_finite μ] [sigma_finite ν]
  (h2f : ∀ᵐ y ∂ν, quasi_measure_preserving (λ x, f (x, y)) μ τ) :
  quasi_measure_preserving f (μ.prod ν) τ :=
begin
  refine ⟨hf, _⟩,
  refine absolutely_continuous.mk (λ s hs h2s, _),
  simp_rw [map_apply hf hs, prod_apply_symm (hf hs), preimage_preimage,
    lintegral_congr_ae (h2f.mono (λ x hx, hx.preimage_null h2s)), lintegral_zero],
end

@[to_additive]
lemma quasi_measure_preserving_div [is_mul_right_invariant μ] :
  quasi_measure_preserving (λ (p : G × G), p.1 / p.2) (μ.prod μ) μ :=
begin
  refine quasi_measure_preserving.prod_of_left measurable_div _,
  simp_rw [div_eq_mul_inv],
  refine eventually_of_forall
    (λ y, ⟨measurable_mul_const y⁻¹, (map_mul_right_eq_self μ y⁻¹).absolutely_continuous⟩)
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
  refine ((map_inv_absolutely_continuous μ).map $ measurable_const_mul g).trans _,
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
  exact (absolutely_continuous_map_inv μ).map (measurable_const_mul g)
end

end

end mul

end measure_theory

lemma measurable_equiv.map_ae {α β : Type*} [measurable_space α] [measurable_space β]
  (f : α ≃ᵐ β) {μ : measure α} : filter.map f μ.ae = (map f μ).ae :=
by { ext s, simp_rw [mem_map, mem_ae_iff, ← preimage_compl, f.map_apply] }


variables [group G] {x : G}

@[to_additive]
lemma measurable_div_const [has_measurable_mul G] (g : G) : measurable (λ h, h / g) :=
by simp_rw [div_eq_mul_inv, measurable_mul_const]

/-- `equiv.div_right` as a `measurable_equiv` -/
@[to_additive /-" `equiv.sub_right` as a `measurable_equiv` "-/]
def measurable_equiv.div_right [has_measurable_mul G] [has_measurable_inv G] (g : G) : G ≃ᵐ G :=
{ to_equiv := equiv.div_right g,
  measurable_to_fun := measurable_div_const g,
  measurable_inv_fun := measurable_mul_const g }

/-- `equiv.div_left` as a `measurable_equiv` -/
@[to_additive /-" `equiv.sub_left` as a `measurable_equiv` "-/]
def measurable_equiv.div_left [has_measurable_mul G] [has_measurable_inv G] (g : G) : G ≃ᵐ G :=
{ to_equiv := equiv.div_left g,
  measurable_to_fun := measurable_id.const_div g,
  measurable_inv_fun := measurable_inv.mul_const g }

@[to_additive]
lemma map_mul_left_ae [has_measurable_mul G] [is_mul_left_invariant μ] :
  filter.map (λ t, x * t) μ.ae = μ.ae :=
(measurable_equiv.mul_left x).map_ae.trans $ congr_arg ae $ map_mul_left_eq_self μ x

@[to_additive]
lemma map_div_left_ae [has_measurable_mul G] [has_measurable_inv G] [is_mul_left_invariant μ]
  [is_inv_invariant μ] :
  filter.map (λ t, x / t) μ.ae = μ.ae :=
(measurable_equiv.div_left x).map_ae.trans $ congr_arg ae $ map_div_left_eq_self μ x

end general_measure

open measure_theory

/- START ACTUAL WORK -/

section preparation

variables [nondiscrete_normed_field 𝕜]
variables [normed_group E] [normed_group E'] [normed_group E''] [normed_group F]
variables [normed_space 𝕜 E] [normed_space 𝕜 E'] [normed_space 𝕜 E''] [normed_space 𝕜 F]
variables {f f' : G → E} {g g' : G → E'}
variables {L : E →L[𝕜] E' →L[𝕜] F}

-- section
-- variables [add_group G] [topological_space G] [has_continuous_sub G]
-- lemma continuous.convolution_integrand_snd (hf : continuous f) (hg : continuous g) (x : G) :
--   continuous (λ t, L (f t) (g (x - t))) :=
-- L.continuous₂.comp₂ hf $ hg.comp $ continuous_const.sub continuous_id

-- lemma continuous.convolution_integrand_swap_snd (hf : continuous f) (hg : continuous g) (x : G) :
--   continuous (λ t, L (f (x - t)) (g t)) :=
-- L.continuous₂.comp₂ (hf.comp $ continuous_const.sub continuous_id) hg
-- end

section
variables [measurable_space G] {μ : measure G}

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

variables [normed_group E] [normed_group E'] [normed_group E''] [normed_group F]
variables {f f' : G → E} {g g' : G → E'} {x x' : G} {y y' : E}

section nondiscrete_normed_field

variables [nondiscrete_normed_field 𝕜]
variables [normed_space 𝕜 E] [normed_space 𝕜 E'] [normed_space 𝕜 E''] [normed_space 𝕜 F]
variables (L : E →L[𝕜] E' →L[𝕜] F)

section no_measurability

variables [add_group G] [topological_space G]

lemma has_compact_support.convolution_integrand_bound_right (hcg : has_compact_support g)
  (hg : continuous g) {x t : G} {s : set G} (hx : x ∈ s) :
  ∥L (f t) (g (x - t))∥ ≤ (- tsupport g + s).indicator (λ t, ∥L∥ * ∥f t∥ * (⨆ i, ∥g i∥)) t :=
begin
  refine le_indicator (λ t ht, _) (λ t ht, _) t,
  { refine (L.le_op_norm₂ _ _).trans _,
    exact mul_le_mul_of_nonneg_left
        (le_csupr (hg.norm.bdd_above_range_of_has_compact_support hcg.norm) $ x - t)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) },
  { have : x - t ∉ support g,
    { refine mt (λ hxt, _) ht, refine ⟨_, _, set.neg_mem_neg.mpr (subset_closure hxt), hx, _⟩,
      rw [neg_sub, sub_add_cancel] },
    rw [nmem_support.mp this, (L _).map_zero, norm_zero] }
end

lemma continuous.convolution_integrand_fst [has_continuous_sub G] (hg : continuous g) (t : G) :
  continuous (λ x, L (f t) (g (x - t))) :=
L.continuous₂.comp₂ continuous_const $ hg.comp $ continuous_id.sub continuous_const

lemma has_compact_support.convolution_integrand_bound_left (hcf : has_compact_support f)
  (hf : continuous f) {x t : G} {s : set G} (hx : x ∈ s) :
  ∥L (f (x - t)) (g t)∥ ≤ (- tsupport f + s).indicator (λ t, ∥L∥ * (⨆ i, ∥f i∥) * ∥g t∥) t :=
by { convert hcf.convolution_integrand_bound_right L.flip hf hx,
  simp_rw [L.op_norm_flip, mul_right_comm] }

end no_measurability

section measurability

variables [measurable_space G] [measurable_space G₀] [measurable_space X] {μ : measure G}

/-- The convolution of `f` and `g` exists at `x` when the function `t ↦ L (f t) (g (x - t))` is
  integrable. There are various conditions on `f` and `g` to prove this. -/
def convolution_exists_at [has_sub G] (f : G → E) (g : G → E') (x : G) (L : E →L[𝕜] E' →L[𝕜] F)
  (μ : measure G . volume_tac) : Prop :=
integrable (λ t, L (f t) (g (x - t))) μ

/-- The convolution of `f` and `g` exists when the function `t ↦ L (f t) (g (x - t))` is integrable
  for all `x : G`. There are various conditions on `f` and `g` to prove this. -/
def convolution_exists [has_sub G] (f : G → E) (g : G → E') (L : E →L[𝕜] E' →L[𝕜] F)
  (μ : measure G . volume_tac) : Prop :=
∀ x : G, convolution_exists_at f g x L μ

section convolution_exists

variables {L}
lemma convolution_exists_at.integrable [has_sub G] {x : G} (h : convolution_exists_at f g x L μ) :
  integrable (λ t, L (f t) (g (x - t))) μ :=
h

variables (L)

section group

variables [add_group G]
variables [has_measurable_add₂ G] [has_measurable_neg G]

lemma measure_theory.ae_strongly_measurable.convolution_integrand' [sigma_finite μ]
  (hf : ae_strongly_measurable f μ)
  (hg : ae_strongly_measurable g $ map (λ (p : G × G), p.1 - p.2) (μ.prod μ)) :
  ae_strongly_measurable (λ p : G × G, L (f p.2) (g (p.1 - p.2))) (μ.prod μ) :=
L.ae_strongly_measurable_comp₂ hf.snd $ hg.comp_measurable $ measurable_fst.sub measurable_snd

lemma measure_theory.ae_strongly_measurable.convolution_integrand_snd'
  (hf : ae_strongly_measurable f μ) {x : G}
  (hg : ae_strongly_measurable g $ map (λ t, x - t) μ) :
  ae_strongly_measurable (λ t, L (f t) (g (x - t))) μ :=
L.ae_strongly_measurable_comp₂ hf $ hg.comp_measurable $ measurable_id.const_sub x

lemma measure_theory.ae_strongly_measurable.convolution_integrand_swap_snd'
  {x : G} (hf : ae_strongly_measurable f $ map (λ t, x - t) μ)
  (hg : ae_strongly_measurable g μ) : ae_strongly_measurable (λ t, L (f (x - t)) (g t)) μ :=
L.ae_strongly_measurable_comp₂ (hf.comp_measurable $ measurable_id.const_sub x) hg

lemma bdd_above.convolution_exists_at' {x₀ : G}
  {s : set G} (hs : measurable_set s) (h2s : support (λ t, L (f t) (g (x₀ - t))) ⊆ s)
  (hf : integrable_on f s μ)
  (hmf : ae_strongly_measurable f μ)
  (hbg : bdd_above ((λ i, ∥g i∥) '' ((λ t, - t + x₀) ⁻¹' s)))
  (hmg : ae_strongly_measurable g $ map (λ t, x₀ - t) μ) :
    convolution_exists_at f g x₀ L μ :=
begin
  set s' := (λ t, - t + x₀) ⁻¹' s,
  have : ∀ᵐ (t : G) ∂μ,
    ∥L (f t) (g (x₀ - t))∥ ≤ s.indicator (λ t, ∥L∥ * ∥f t∥ * ⨆ i : s', ∥g i∥) t,
  { refine eventually_of_forall _,
    refine le_indicator (λ t ht, _) (λ t ht, _),
    { refine (L.le_op_norm₂ _ _).trans _,
      refine mul_le_mul_of_nonneg_left
        (le_csupr_set hbg $ mem_preimage.mpr _)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)),
      rwa [neg_sub, sub_add_cancel] },
    { have : t ∉ support (λ t, L (f t) (g (x₀ - t))) := mt (λ h, h2s h) ht,
      rw [nmem_support.mp this, norm_zero] } },
  refine integrable.mono' _ _ this,
  { rw [integrable_indicator_iff hs], exact (hf.norm.const_mul _).mul_const _ },
  { exact hmf.convolution_integrand_snd' L hmg }
end

section left
variables [sigma_finite μ] [is_add_left_invariant μ]

lemma measure_theory.ae_strongly_measurable.convolution_integrand_snd
  (hf : ae_strongly_measurable f μ) (hg : ae_strongly_measurable g μ)
  (x : G) : ae_strongly_measurable (λ t, L (f t) (g (x - t))) μ :=
hf.convolution_integrand_snd' L $ hg.mono' $ map_sub_left_absolutely_continuous μ x

lemma measure_theory.ae_strongly_measurable.convolution_integrand_swap_snd
  (hf : ae_strongly_measurable f μ) (hg : ae_strongly_measurable g μ)
  (x : G) : ae_strongly_measurable (λ t, L (f (x - t)) (g t)) μ :=
(hf.mono' (map_sub_left_absolutely_continuous μ x)).convolution_integrand_swap_snd' L hg

end left

section right

variables [sigma_finite μ] [is_add_right_invariant μ]

lemma measure_theory.ae_strongly_measurable.convolution_integrand
  (hf : ae_strongly_measurable f μ) (hg : ae_strongly_measurable g μ) :
  ae_strongly_measurable (λ p : G × G, L (f p.2) (g (p.1 - p.2))) (μ.prod μ) :=
hf.convolution_integrand' L $ hg.mono' (quasi_measure_preserving_sub μ).absolutely_continuous

lemma measure_theory.integrable.convolution_integrand (hf : integrable f μ) (hg : integrable g μ) :
  integrable (λ p : G × G, L (f p.2) (g (p.1 - p.2))) (μ.prod μ) :=
begin
  have h_meas : ae_strongly_measurable (λ (p : G × G), (L (f p.2)) (g (p.1 - p.2))) (μ.prod μ) :=
    hf.ae_strongly_measurable.convolution_integrand L hg.ae_strongly_measurable,
  have h2_meas : ae_strongly_measurable (λ (y : G), ∫ (x : G), ∥(L (f y)) (g (x - y))∥ ∂μ) μ :=
    h_meas.prod_swap.norm.integral_prod_right',
  simp_rw [integrable_prod_iff' h_meas],
  refine ⟨eventually_of_forall (λ t, (L (f t)).integrable_comp (hg.comp_sub_right t)), _⟩,
  refine integrable.mono' _ h2_meas (eventually_of_forall $
    λ t, integral_norm_bilinear_le_right (λ x, g (x - t)) (f t) (hg.comp_sub_right t)),
  simp_rw [integral_sub_right_eq_self (λ t, ∥ g t ∥) μ],
  exact (hf.norm.const_mul _).mul_const _,
end

lemma integrable.ae_convolution_exists (hf : integrable f μ) (hg : integrable g μ) :
  ∀ᵐ x ∂μ, convolution_exists_at f g x L μ :=
((integrable_prod_iff $ hf.ae_strongly_measurable.convolution_integrand L
  hg.ae_strongly_measurable).mp $ hf.convolution_integrand L hg).1

end right

variables [topological_space G] [topological_add_group G] [borel_space G]
  [second_countable_topology G] [sigma_compact_space G]

lemma has_compact_support.convolution_exists_at {x₀ : G}
  (h : has_compact_support (λ t, L (f t) (g (x₀ - t)))) (hf : locally_integrable f μ)
  (hg : continuous g) : convolution_exists_at f g x₀ L μ :=
((((homeomorph.neg G).trans $ homeomorph.add_right x₀).compact_preimage.mpr h).bdd_above_image
  hg.norm.continuous_on).convolution_exists_at' L is_closed_closure.measurable_set subset_closure
  (hf h) hf.ae_strongly_measurable hg.ae_strongly_measurable

lemma has_compact_support.convolution_exists_right
  (hf : locally_integrable f μ) (hcg : has_compact_support g) (hg : continuous g) :
  convolution_exists f g L μ :=
begin
  intro x₀,
  refine has_compact_support.convolution_exists_at L _ hf hg,
  refine (hcg.comp_homeomorph (homeomorph.sub_left x₀)).mono _,
  refine λ t, mt (λ ht : g (x₀ - t) = 0, _),
  simp_rw [ht, (L _).map_zero]
end

lemma has_compact_support.convolution_exists_left_of_continuous_right
  (hcf : has_compact_support f) (hf : locally_integrable f μ) (hg : continuous g) :
  convolution_exists f g L μ :=
begin
  intro x₀,
  refine has_compact_support.convolution_exists_at L _ hf hg,
  refine hcf.mono _,
  refine λ t, mt (λ ht : f t = 0, _),
  simp_rw [ht, L.map_zero₂]
end

end group

section comm_group

variables [add_comm_group G]

section measurable_group

variables [has_measurable_add₂ G] [has_measurable_neg G] [is_add_left_invariant μ]

lemma bdd_above.convolution_exists_at [sigma_finite μ] {x₀ : G}
  {s : set G} (hs : measurable_set s) (h2s : support (λ t, L (f t) (g (x₀ - t))) ⊆ s)
  (hf : integrable_on f s μ)
  (hmf : ae_strongly_measurable f μ)
  (hbg : bdd_above ((λ i, ∥g i∥) '' ((λ t, x₀ - t) ⁻¹' s)))
  (hmg : ae_strongly_measurable g μ) :
    convolution_exists_at f g x₀ L μ :=
begin
  refine bdd_above.convolution_exists_at' L hs h2s hf hmf _ _,
  { simp_rw [← sub_eq_neg_add, hbg] },
  { exact hmg.mono' (map_sub_left_absolutely_continuous μ x₀) }
end

variables {L} [is_neg_invariant μ]

lemma convolution_exists_at_flip :
  convolution_exists_at g f x L.flip μ ↔ convolution_exists_at f g x L μ :=
by simp_rw [convolution_exists_at, ← integrable_comp_sub_left μ (λ t, L (f t) (g (x - t))) x,
  sub_sub_cancel, flip_apply]

lemma convolution_exists_at.integrable_swap (h : convolution_exists_at f g x L μ) :
  integrable (λ t, L (f (x - t)) (g t)) μ :=
by { convert h.comp_sub_left x, simp_rw [sub_sub_self] }

lemma convolution_exists_at_iff_integrable_swap :
  convolution_exists_at f g x L μ ↔ integrable (λ t, L (f (x - t)) (g t)) μ :=
convolution_exists_at_flip.symm

end measurable_group

variables [topological_space G] [topological_add_group G] [borel_space G]
  [second_countable_topology G] [is_add_left_invariant μ] [is_neg_invariant μ]
  [sigma_compact_space G]

lemma has_compact_support.convolution_exists_left
  (hcf : has_compact_support f) (hf : continuous f) (hg : locally_integrable g μ) :
  convolution_exists f g L μ :=
λ x₀, convolution_exists_at_flip.mp $ hcf.convolution_exists_right L.flip hg hf x₀

lemma has_compact_support.convolution_exists_right_of_continuous_left
  (hcg : has_compact_support g) (hf : continuous f) (hg : locally_integrable g μ) :
  convolution_exists f g L μ :=
λ x₀, convolution_exists_at_flip.mp $
  hcg.convolution_exists_left_of_continuous_right L.flip hg hf x₀

end comm_group

end convolution_exists

variables [normed_space ℝ F] [complete_space F]

/-- The convolution of two functions `f` and `g`. -/
def convolution [has_sub G] (f : G → E) (g : G → E') (L : E →L[𝕜] E' →L[𝕜] F)
  (μ : measure G . volume_tac) : G → F :=
λ x, ∫ t, L (f t) (g (x - t)) ∂μ

localized "notation f ` ⋆[`:67 L:67 `, ` μ:67 `] `:0 g:66 := convolution f g L μ" in convolution
localized "notation f ` ⋆[`:67 L:67 `]`:0 g:66 := convolution f g L
  measure_theory.measure_space.volume" in convolution
localized "notation f ` ⋆ `:67 g:66 := convolution f g (continuous_linear_map.lsmul ℝ ℝ)
  measure_theory.measure_space.volume" in convolution

lemma convolution_def [has_sub G] : (f ⋆[L, μ] g) x = ∫ t, L (f t) (g (x - t)) ∂μ := rfl

/-- The definition of convolution where the bilinear operator is scalar multiplication.
Note: it often helps the elaborator to give the type of the convolution explicitly. -/
lemma convolution_lsmul [has_sub G] {f : G → 𝕜} {g : G → F}:
  (f ⋆[lsmul 𝕜 𝕜, μ] g : G → F) x = ∫ t, f t • g (x - t) ∂μ := rfl

/-- The definition of convolution where the bilinear operator is multiplication. -/
lemma convolution_lmul [has_sub G] [normed_space ℝ 𝕜] [complete_space 𝕜] {f : G → 𝕜} {g : G → 𝕜} :
  (f ⋆[lmul 𝕜 𝕜, μ] g) x = ∫ t, f t * g (x - t) ∂μ := rfl

section group

variables {L} [add_group G]

lemma smul_convolution [smul_comm_class ℝ 𝕜 F]
  {y : 𝕜} : (y • f) ⋆[L, μ] g = y • (f ⋆[L, μ] g) :=
by { ext, simp only [pi.smul_apply, convolution_def, ← integral_smul, L.map_smul₂] }

lemma convolution_smul [smul_comm_class ℝ 𝕜 F]
  {y : 𝕜} : f ⋆[L, μ] (y • g) = y • (f ⋆[L, μ] g) :=
by { ext, simp only [pi.smul_apply, convolution_def, ← integral_smul, (L _).map_smul] }

lemma zero_convolution : 0 ⋆[L, μ] g = 0 :=
by { ext, simp_rw [convolution_def, pi.zero_apply, L.map_zero₂, integral_zero] }

lemma convolution_zero : f ⋆[L, μ] 0 = 0 :=
by { ext, simp_rw [convolution_def, pi.zero_apply, (L _).map_zero, integral_zero] }

lemma convolution_exists_at.distrib_add {x : G} (hfg : convolution_exists_at f g x L μ)
  (hfg' : convolution_exists_at f g' x L μ) :
  (f ⋆[L, μ] (g + g')) x = (f ⋆[L, μ] g) x + (f ⋆[L, μ] g') x :=
by simp only [convolution_def, (L _).map_add, pi.add_apply, integral_add hfg hfg']

lemma convolution_exists.distrib_add (hfg : convolution_exists f g L μ)
  (hfg' : convolution_exists f g' L μ) : f ⋆[L, μ] (g + g') = f ⋆[L, μ] g + f ⋆[L, μ] g' :=
by { ext, exact (hfg x).distrib_add (hfg' x) }

lemma convolution_exists_at.add_distrib {x : G} (hfg : convolution_exists_at f g x L μ)
  (hfg' : convolution_exists_at f' g x L μ) :
  ((f + f') ⋆[L, μ] g) x = (f ⋆[L, μ] g) x + (f' ⋆[L, μ] g) x :=
by simp only [convolution_def, L.map_add₂', pi.add_apply, integral_add hfg hfg']

lemma convolution_exists.add_distrib (hfg : convolution_exists f g L μ)
  (hfg' : convolution_exists f' g L μ) : (f + f') ⋆[L, μ] g = f ⋆[L, μ] g + f' ⋆[L, μ] g :=
by { ext, exact (hfg x).add_distrib (hfg' x) }

variables (L)

lemma convolution_congr [has_measurable_add G] [has_measurable_neg G] [is_add_left_invariant μ]
  [is_neg_invariant μ] (h1 : f =ᵐ[μ] f') (h2 : g =ᵐ[μ] g') :
  f ⋆[L, μ] g = f' ⋆[L, μ] g' :=
begin
  ext,
  apply integral_congr_ae,
  exact (h1.prod_mk $ h2.comp_tendsto map_sub_left_ae.le).fun_comp ↿(λ x y, L x y)
end

lemma support_convolution_subset_swap : support (f ⋆[L, μ] g) ⊆ support g + support f :=
begin
  intros x h2x,
  by_contra hx,
  apply h2x,
  simp_rw [set.mem_add, not_exists, not_and_distrib, nmem_support] at hx,
  rw [convolution_def],
  convert integral_zero G F,
  ext t,
  rcases hx (x - t) t with h|h|h,
  { rw [h, (L _).map_zero] },
  { rw [h, L.map_zero₂] },
  { exact (h $ sub_add_cancel x t).elim }
end

variables [topological_space G]
variables [topological_add_group G]

lemma has_compact_support.convolution [t2_space G] (hcf : has_compact_support f)
  (hcg : has_compact_support g) : has_compact_support (f ⋆[L, μ] g) :=
compact_of_is_closed_subset (hcg.is_compact.add hcf) is_closed_closure $ closure_minimal
  ((support_convolution_subset_swap L).trans $ add_subset_add subset_closure subset_closure)
  (hcg.is_compact.add hcf).is_closed

variables [borel_space G] [second_countable_topology G] [sigma_finite μ]
variables [is_add_right_invariant μ]

lemma integrable.integrable_convolution (hf : integrable f μ) (hg : integrable g μ) :
  integrable (f ⋆[L, μ] g) μ :=
(hf.convolution_integrand L hg).integral_prod_left

/-- The convolution is continuous if one function is locally integrable and the other has compact
  support and is continuous. -/
lemma has_compact_support.continuous_convolution_right [locally_compact_space G] [t2_space G]
  (hf : locally_integrable f μ) (hcg : has_compact_support g)
  (hg : continuous g) : continuous (f ⋆[L, μ] g) :=
begin
  refine continuous_iff_continuous_at.mpr (λ x₀, _),
  obtain ⟨K, hK, h2K⟩ := exists_compact_mem_nhds x₀,
  let K' := - tsupport g + K,
  have hK' : is_compact K' := hcg.neg.add hK,
  have : ∀ᶠ x in 𝓝 x₀, ∀ᵐ (t : G) ∂μ,
    ∥L (f t) (g (x - t))∥ ≤ K'.indicator (λ t, ∥L∥ * ∥f t∥ * (⨆ i, ∥g i∥)) t :=
  eventually_of_mem h2K (λ x hx, eventually_of_forall $
    λ t, hcg.convolution_integrand_bound_right L hg hx),
  refine continuous_at_of_dominated _ this _ _,
  { exact eventually_of_forall
      (λ x, hf.ae_strongly_measurable.convolution_integrand_snd' L hg.ae_strongly_measurable) },
  { rw [integrable_indicator_iff hK'.measurable_set],
    exact ((hf hK').norm.const_mul _).mul_const _ },
  { exact eventually_of_forall (λ t, (L.continuous₂.comp₂ continuous_const $
      hg.comp $ continuous_id.sub $ by apply continuous_const).continuous_at) }
end

/-- The convolution is continuous if one function is integrable and the other is bounded and
  continuous. -/
lemma bdd_above.continuous_convolution_right_of_integrable
  (hf : integrable f μ) (hbg : bdd_above (range (λ x, ∥g x∥))) (hg : continuous g) :
    continuous (f ⋆[L, μ] g) :=
begin
  refine continuous_iff_continuous_at.mpr (λ x₀, _),
  have : ∀ᶠ x in 𝓝 x₀, ∀ᵐ (t : G) ∂μ,
    ∥L (f t) (g (x - t))∥ ≤ ∥L∥ * ∥f t∥ * (⨆ i, ∥g i∥),
  { refine eventually_of_forall (λ x, eventually_of_forall $ λ t, _),
    refine (L.le_op_norm₂ _ _).trans _,
    exact mul_le_mul_of_nonneg_left (le_csupr hbg $ x - t)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) },
  refine continuous_at_of_dominated _ this _ _,
  { exact eventually_of_forall
      (λ x, hf.ae_strongly_measurable.convolution_integrand_snd' L hg.ae_strongly_measurable) },
  { exact (hf.norm.const_mul _).mul_const _ },
  { exact eventually_of_forall (λ t, (L.continuous₂.comp₂ continuous_const $
      hg.comp $ continuous_id.sub $ by apply continuous_const).continuous_at) }
end

end group

section comm_group

variables [add_comm_group G]

lemma support_convolution_subset : support (f ⋆[L, μ] g) ⊆ support f + support g :=
(support_convolution_subset_swap L).trans (add_comm _ _).subset

variables [topological_space G]
variables [topological_add_group G]
variables [borel_space G]
variables [is_add_left_invariant μ]  [is_neg_invariant μ]

variable (L)
/-- Commutativity of convolution -/
lemma convolution_flip : g ⋆[L.flip, μ] f = f ⋆[L, μ] g :=
begin
  ext1 x,
  simp_rw [convolution_def],
  rw [← integral_sub_left_eq_self _ μ x],
  simp_rw [sub_sub_self, flip_apply]
end

/-- The symmetric definition of convolution. -/
lemma convolution_eq_swap : (f ⋆[L, μ] g) x = ∫ t, L (f (x - t)) (g t) ∂μ :=
by { rw [← convolution_flip], refl }

/-- The symmetric definition of convolution where the bilinear operator is scalar multiplication. -/
lemma convolution_lsmul_swap {f : G → 𝕜} {g : G → F}:
  (f ⋆[lsmul 𝕜 𝕜, μ] g : G → F) x = ∫ t, f (x - t) • g t ∂μ :=
convolution_eq_swap _

/-- The symmetric definition of convolution where the bilinear operator is multiplication. -/
lemma convolution_lmul_swap [normed_space ℝ 𝕜] [complete_space 𝕜] {f : G → 𝕜} {g : G → 𝕜} :
  (f ⋆[lmul 𝕜 𝕜, μ] g) x = ∫ t, f (x - t) * g t ∂μ :=
convolution_eq_swap _

variables [second_countable_topology G] [sigma_finite μ]

lemma has_compact_support.continuous_convolution_left [locally_compact_space G] [t2_space G]
  (hcf : has_compact_support f) (hf : continuous f) (hg : locally_integrable g μ) :
    continuous (f ⋆[L, μ] g) :=
by { rw [← convolution_flip], exact hcf.continuous_convolution_right L.flip hg hf }

lemma bdd_above.continuous_convolution_left_of_integrable
  (hbf : bdd_above (range (λ x, ∥f x∥))) (hf : continuous f) (hg : integrable g μ) :
    continuous (f ⋆[L, μ] g) :=
by { rw [← convolution_flip], exact hbf.continuous_convolution_right_of_integrable L.flip hg hf }

/-- A version of `has_compact_support.continuous_convolution_left` that works if `G` is
  not locally compact but requires that `g` is integrable. -/
lemma has_compact_support.continuous_convolution_left_of_integrable
  (hcf : has_compact_support f) (hf : continuous f) (hg : integrable g μ) :
    continuous (f ⋆[L, μ] g) :=
(hf.norm.bdd_above_range_of_has_compact_support hcf.norm).continuous_convolution_left_of_integrable
  L hf hg

end comm_group

section normed_group

variables [semi_normed_group G]

/-- We can simplify the RHS further if we assume `f` is integrable, but also if `L = (•)`.
  TODO: add a version that assumes `antilipschitz_with` on `L`. -/
lemma convolution_eq_right' {x₀ : G} {R : ℝ}
  (hf : support f ⊆ ball (0 : G) R)
  (hg : ∀ x ∈ ball x₀ R, g x = g x₀) : (f ⋆[L, μ] g) x₀ = ∫ (t : G), (L (f t)) (g x₀) ∂μ :=
begin
  have h2 : ∀ t, L (f t) (g (x₀ - t)) = L (f t) (g x₀),
  { intro t, by_cases ht : t ∈ support f,
    { have h2t := hf ht,
      rw [mem_ball_zero_iff] at h2t,
      specialize hg (x₀ - t),
      rw [sub_eq_add_neg, add_mem_ball_iff_norm, norm_neg, ← sub_eq_add_neg] at hg,
      rw [hg h2t] },
    { rw [nmem_support] at ht,
      simp_rw [ht, L.map_zero₂] } },
  simp_rw [convolution_def, h2],
end

variables [borel_space G] [second_countable_topology G]
variables [is_add_left_invariant μ] [sigma_finite μ]

--measurable_set_ball can be pseudo_metric_space

lemma dist_convolution_le' {x₀ : G} {R ε : ℝ}
  (hif : integrable f μ)
  (hR : 0 < R) -- todo: remove this assumption(?)
  (hf : support f ⊆ ball (0 : G) R)
  (hmg : ae_strongly_measurable g μ)
  (hg : ∀ x ∈ ball x₀ R, dist (g x) (g x₀) ≤ ε) :
  dist ((f ⋆[L, μ] g : G → F) x₀) (∫ (t : G), (L (f t)) (g x₀) ∂μ) ≤ ∥L∥ * ∫ x, ∥f x∥ ∂μ * ε :=
begin
  have hε : 0 ≤ ε, { convert hg x₀ (mem_ball_self hR), rw dist_self },
  have hfg : convolution_exists_at f g x₀ L μ,
  { refine bdd_above.convolution_exists_at L metric.is_open_ball.measurable_set (subset_trans _ hf)
      hif.integrable_on hif.ae_strongly_measurable _ hmg,
    { refine λ t, mt (λ ht : f t = 0, _), simp_rw [ht, L.map_zero₂] },
    rw [bdd_above_def],
    refine ⟨∥g x₀∥ + ε, _⟩,
    rintro _ ⟨x, hx, rfl⟩,
    refine norm_le_norm_add_const_of_dist_le (hg x _),
    rwa [mem_ball_iff_norm, norm_sub_rev, ← mem_ball_zero_iff] },
  have h2 : ∀ t, dist (L (f t) (g (x₀ - t))) (L (f t) (g x₀)) ≤ ∥L (f t)∥ * ε,
  { intro t, by_cases ht : t ∈ support f,
    { have h2t := hf ht,
      rw [mem_ball_zero_iff] at h2t,
      specialize hg (x₀ - t),
      rw [sub_eq_add_neg, add_mem_ball_iff_norm, norm_neg, ← sub_eq_add_neg] at hg,
      refine ((L (f t)).dist_le_op_norm _ _).trans _,
      exact mul_le_mul_of_nonneg_left (hg h2t) (norm_nonneg _) },
    { rw [nmem_support] at ht,
      simp_rw [ht, L.map_zero₂, L.map_zero, norm_zero, zero_mul, dist_self] } },
  simp_rw [convolution_def],
  simp_rw [dist_eq_norm] at h2 ⊢,
  rw [← integral_sub hfg.integrable], swap, { exact (L.flip (g x₀)).integrable_comp hif },
  refine (norm_integral_le_of_norm_le ((L.integrable_comp hif).norm.mul_const ε)
    (eventually_of_forall h2)).trans _,
  rw [integral_mul_right],
  refine mul_le_mul_of_nonneg_right _ hε,
  have h3 : ∀ t, ∥L (f t)∥ ≤ ∥L∥ * ∥f t∥ := λ t, L.le_op_norm (f t),
  refine (integral_mono (L.integrable_comp hif).norm (hif.norm.const_mul _) h3).trans_eq _,
  rw [integral_mul_left]
end

variables [normed_space ℝ E] [normed_space ℝ E'] [complete_space E']

lemma dist_convolution_le {f : G → ℝ} {x₀ : G} {R ε : ℝ}
  (hR : 0 < R) -- todo: remove this assumption(?)
  (hf : support f ⊆ ball (0 : G) R)
  (hnf : ∀ x, 0 ≤ f x)
  (hintf : ∫ x, f x ∂μ = 1)
  (hmg : ae_strongly_measurable g μ)
  (hg : ∀ x ∈ ball x₀ R, dist (g x) (g x₀) ≤ ε) :
  dist ((f ⋆[lsmul ℝ ℝ, μ] g : G → E') x₀) (g x₀) ≤ ε :=
begin
  have hε : 0 ≤ ε, { convert hg x₀ (mem_ball_self hR), rw dist_self },
  have hif : integrable f μ,
  { by_contra hif, exact zero_ne_one ((integral_undef hif).symm.trans hintf) },
  convert (dist_convolution_le' _ hif hR hf hmg hg).trans _,
  { simp_rw [lsmul_apply, integral_smul_const, hintf, one_smul] },
  { simp_rw [real.norm_of_nonneg (hnf _), hintf, mul_one],
    convert
      (mul_le_mul_of_nonneg_right continuous_linear_map.op_norm_lsmul_le hε).trans_eq (one_mul ε) }
end

lemma convolution_tendsto_right {ι} {l : filter ι} {φ : ι → G → ℝ}
  (hnφ : ∀ i x, 0 ≤ φ i x)
  (hiφ : ∀ i, ∫ s, φ i s ∂μ = 1)
  (hφ : tendsto (λ n, support (φ n)) l (𝓝 0).small_sets)
  (hmg : ae_strongly_measurable g μ) {x₀ : G} (hcg : continuous_at g x₀) :
  tendsto (λ i, (φ i ⋆[lsmul ℝ ℝ, μ] g : G → E') x₀) l (𝓝 (g x₀)) :=
begin
  simp_rw [tendsto_small_sets_iff] at hφ,
  rw [metric.continuous_at_iff] at hcg,
  rw [metric.tendsto_nhds],
  intros ε hε,
  rcases hcg (ε / 2) (half_pos hε) with ⟨δ, hδ, hgδ⟩,
  refine (hφ (ball (0 : G) δ) $ ball_mem_nhds _ hδ).mono (λ i hi, _),
  exact (dist_convolution_le hδ hi (hnφ i) (hiφ i) hmg (λ x hx, (hgδ hx.out).le)).trans_lt
    (half_lt_self hε)
end

end normed_group

namespace cont_diff_bump_of_inner

variables {n : with_top ℕ}
variables [normed_space ℝ E']
variables [inner_product_space ℝ G]
variables [complete_space E']
variables {a : G} {φ : cont_diff_bump_of_inner (0 : G)}

lemma convolution_eq_right {x₀ : G}
  (hg : ∀ x ∈ ball x₀ φ.R, g x = g x₀) : (φ ⋆[lsmul ℝ ℝ, μ] g : G → E') x₀ = integral μ φ • g x₀ :=
by simp_rw [convolution_eq_right' _ φ.support_eq.subset hg, lsmul_apply, integral_smul_const]

variables [borel_space G]
variables [is_locally_finite_measure μ] [is_open_pos_measure μ]
variables [finite_dimensional ℝ G]

lemma normed_convolution_eq_right {x₀ : G}
  (hg : ∀ x ∈ ball x₀ φ.R, g x = g x₀) : (φ.normed μ ⋆[lsmul ℝ ℝ, μ] g : G → E') x₀ = g x₀ :=
by { simp_rw [convolution_eq_right' _ φ.support_normed_eq.subset hg, lsmul_apply],
  exact integral_normed_smul φ μ (g x₀) }

variables [is_add_left_invariant μ]

lemma dist_normed_convolution_le {x₀ : G} {ε : ℝ}
  (hmg : ae_strongly_measurable g μ)
  (hg : ∀ x ∈ ball x₀ φ.R, dist (g x) (g x₀) ≤ ε) :
  dist ((φ.normed μ ⋆[lsmul ℝ ℝ, μ] g : G → E') x₀) (g x₀) ≤ ε :=
dist_convolution_le φ.R_pos φ.support_normed_eq.subset φ.nonneg_normed φ.integral_normed hmg hg

lemma convolution_tendsto_right' {ι} {φ : ι → cont_diff_bump_of_inner (0 : G)}
  {l : filter ι} (hφ : tendsto (λ i, (φ i).R) l (𝓝 0))
  (hmg : ae_strongly_measurable g μ) {x₀ : G} (hcg : continuous_at g x₀) :
  tendsto (λ i, ((λ x, (φ i).normed μ x) ⋆[lsmul ℝ ℝ, μ] g : G → E') x₀) l (𝓝 (g x₀)) :=
begin
  refine convolution_tendsto_right (λ i, (φ i).nonneg_normed) (λ i, (φ i).integral_normed)
    _ hmg hcg,
  rw [normed_group.tendsto_nhds_zero] at hφ,
  rw [tendsto_small_sets_iff],
  intros t ht,
  rcases metric.mem_nhds_iff.mp ht with ⟨ε, hε, ht⟩,
  refine (hφ ε hε).mono (λ i hi, subset_trans _ ht),
  simp_rw [(φ i).support_normed_eq],
  rw [real.norm_eq_abs, abs_eq_self.mpr (φ i).R_pos.le] at hi,
  exact ball_subset_ball hi.le
end

lemma convolution_tendsto_right {ι} {φ : ι → cont_diff_bump_of_inner (0 : G)}
  {l : filter ι} (hφ : tendsto (λ i, (φ i).R) l (𝓝 0))
  (hg : continuous g) (x₀ : G) :
  tendsto (λ i, ((λ x, (φ i).normed μ x) ⋆[lsmul ℝ ℝ, μ] g : G → E') x₀) l (𝓝 (g x₀)) :=
convolution_tendsto_right' hφ hg.ae_strongly_measurable hg.continuous_at

end cont_diff_bump_of_inner

end measurability

end nondiscrete_normed_field

open_locale convolution


section normed_space
-- (`𝕜` cannot be nondiscrete_normed_field, because of `continuous_linear_map.integral_apply`)
variables [is_R_or_C 𝕜]
variables [normed_space 𝕜 E]
variables [normed_space 𝕜 E']
variables [normed_space 𝕜 E'']
variables [normed_space ℝ F] [normed_space 𝕜 F]
variables [normed_group G]
variables {n : with_top ℕ}
variables [complete_space F]
variables [measurable_space G] [borel_space G] {μ : measure G} [second_countable_topology G]
variables (L : E →L[𝕜] E' →L[𝕜] F)
variables [sigma_finite μ] [sigma_compact_space G]
variables [is_add_left_invariant μ]

lemma convolution_precompR_apply {g : G → E'' →L[𝕜] E'}
  (hf : locally_integrable f μ) (hcg : has_compact_support g) (hg : continuous g)
  (x₀ : G) (x : E'') : (f ⋆[L.precompR E'', μ] g) x₀ x = (f ⋆[L, μ] (λ a, g a x)) x₀  :=
begin
  have := hcg.convolution_exists_right (L.precompR E'') hf hg x₀,
  simp_rw [convolution_def, continuous_linear_map.integral_apply this],
  refl,
end

variables [normed_space 𝕜 G] [proper_space G]

lemma has_compact_support.has_fderiv_at_convolution_right
  (hf : locally_integrable f μ) (hcg : has_compact_support g) (hg : cont_diff 𝕜 1 g) (x₀ : G) :
  has_fderiv_at (f ⋆[L, μ] g) ((f ⋆[L.precompR G, μ] fderiv 𝕜 g) x₀) x₀ :=
begin
  set L' := L.precompR G,
  have h1 : ∀ᶠ x in 𝓝 x₀, ae_strongly_measurable (λ t, L (f t) (g (x - t))) μ :=
  eventually_of_forall
    (hf.ae_strongly_measurable.convolution_integrand_snd L hg.continuous.ae_strongly_measurable),
  have h2 : ∀ x, ae_strongly_measurable (λ t, L' (f t) (fderiv 𝕜 g (x - t))) μ,
  { exact hf.ae_strongly_measurable.convolution_integrand_snd L'
      (hg.continuous_fderiv le_rfl).ae_strongly_measurable },
  have h3 : ∀ x t, has_fderiv_at (λ x, g (x - t)) (fderiv 𝕜 g (x - t)) x,
  { intros x t,
    simpa using (hg.differentiable le_rfl).differentiable_at.has_fderiv_at.comp x
      ((has_fderiv_at_id x).sub (has_fderiv_at_const t x)) },
  let K' := - tsupport (fderiv 𝕜 g) + closed_ball x₀ 1,
  have hK' : is_compact K' := (hcg.fderiv 𝕜).neg.add (is_compact_closed_ball x₀ 1),
  refine has_fderiv_at_integral_of_dominated_of_fderiv_le
    zero_lt_one h1 _ (h2 x₀) _ _ _,
  { exact K'.indicator (λ t, ∥L'∥ * ∥f t∥ * (⨆ x, ∥fderiv 𝕜 g x∥)) },
  { exact hcg.convolution_exists_right L hf hg.continuous x₀ },
  { refine eventually_of_forall (λ t x hx, _),
    exact (hcg.fderiv 𝕜).convolution_integrand_bound_right L'
      (hg.continuous_fderiv le_rfl) (ball_subset_closed_ball hx) },
  { rw [integrable_indicator_iff hK'.measurable_set],
    exact ((hf hK').norm.const_mul _).mul_const _ },
  { exact eventually_of_forall (λ t x hx, (L _).has_fderiv_at.comp x (h3 x t)) },
end

lemma has_compact_support.has_fderiv_at_convolution_left [is_neg_invariant μ]
  (hcf : has_compact_support f) (hf : cont_diff 𝕜 1 f) (hg : locally_integrable g μ) (x₀ : G) :
  has_fderiv_at (f ⋆[L, μ] g) ((fderiv 𝕜 f ⋆[L.precompL G, μ] g) x₀) x₀ :=
begin
  simp only [← convolution_flip] {single_pass := tt},
  exact hcf.has_fderiv_at_convolution_right L.flip hg hf x₀,
end

lemma has_compact_support.cont_diff_convolution_right [finite_dimensional 𝕜 G]
  (hf : locally_integrable f μ) (hcg : has_compact_support g) (hg : cont_diff 𝕜 n g) :
  cont_diff 𝕜 n (f ⋆[L, μ] g) :=
begin
  induction n using with_top.nat_induction with n ih ih generalizing g,
  { rw [cont_diff_zero] at hg ⊢,
    exact hcg.continuous_convolution_right L hf hg },
  { have h : ∀ x, has_fderiv_at (f ⋆[L, μ] g) ((f ⋆[L.precompR G, μ] fderiv 𝕜 g) x) x :=
      hcg.has_fderiv_at_convolution_right L hf hg.one_of_succ,
    rw cont_diff_succ_iff_fderiv_apply,
    split,
    { exact λ x₀, ⟨_, h x₀⟩ },
    { simp_rw [fderiv_eq h, convolution_precompR_apply L hf (hcg.fderiv 𝕜)
        (hg.one_of_succ.continuous_fderiv le_rfl)],
      intro x,
      refine ih _ _,
      { refine @has_compact_support.comp_left _ _ _ _ _ _ (λ (G : _ →L[𝕜] _), G x) _
          (hcg.fderiv 𝕜) (continuous_linear_map.zero_apply x) },
      { revert x, rw [← cont_diff_clm_apply],
        exact (cont_diff_succ_iff_fderiv.mp hg).2 } } },
  { rw [cont_diff_top] at hg ⊢, exact λ n, ih n hcg (hg n) }
end

lemma has_compact_support.cont_diff_convolution_left [finite_dimensional 𝕜 G] [is_neg_invariant μ]
  (hcf : has_compact_support f) (hf : cont_diff 𝕜 n f) (hg : locally_integrable g μ) :
  cont_diff 𝕜 n (f ⋆[L, μ] g) :=
begin
  rw [← convolution_flip],
  exact hcf.cont_diff_convolution_right L.flip hg hf,
end

variables {F' F'' : Type*}
variables [normed_group E''] [normed_space 𝕜 E'']
variables [normed_group F'] [normed_space ℝ F'] [normed_space 𝕜 F'] [complete_space F']
variables [normed_group F''] [normed_space ℝ F''] [normed_space 𝕜 F''] [complete_space F'']
variables {k : G → E''}
variables (L₂ : F →L[𝕜] E'' →L[𝕜] F')
variables (L₃ : E →L[𝕜] F'' →L[𝕜] F')
variables (L₄ : E' →L[𝕜] E'' →L[𝕜] F'')

-- lemma integrable_assoc_integrand'  {x₀ : G} (hf : integrable f μ) (hg : integrable g μ)
--   (hk : integrable k μ) :
--   integrable (uncurry (λ x y, (L₃ (f y)) ((L₄ (g (x - y))) (k (x₀ - x))))) (μ.prod μ) :=
-- begin
--   rw [measure_theory.integrable_prod_iff],
--   { split,
--     { refine eventually_of_forall (λ x, _), dsimp,
--       have h2 : integrable (λ y, (L₄ (g y)) (k (x₀ - x))) μ := sorry,
--       -- have := L₃.integrable_comp,
--       sorry
--       -- have h3 : map (λ y, (x, y)) μ ≤ μ.prod μ,
--       -- { intros s hs, rw [map_apply _ hs, ← prod_univ], },
--       -- exact ((measure_theory.integrable.convolution_integrand L₃ hf h2).mono_measure
--       --   h3).comp_measurable (measurable_const.prod_mk measurable_id)
--         },
--     { sorry } },
--   { refine L₃.ae_strongly_measurable_comp₂ hf.ae_strongly_measurable.snd _,
--     refine L₄.ae_strongly_measurable_comp₂
--       ((hg.ae_strongly_measurable.mono' _).comp_measurable $ measurable_fst.sub measurable_snd)
--       ((hk.ae_strongly_measurable.mono' _).comp_measurable $ measurable_const.sub measurable_fst),
--     exact (quasi_measure_preserving_sub μ).absolutely_continuous,
--     rw [← measure.map_map],
--     refine (prod_fst_absolutely_continuous.map $ measurable_id.const_sub x₀).trans
--       (map_sub_left_absolutely_continuous μ x₀),
--     exact measurable_id.const_sub x₀,
--     exact measurable_fst }
-- end

-- todo: prove that `hi` follows from simpler conditions.
lemma convolution_assoc (hL : ∀ (x : E) (y : E') (z : E''), L₂ (L x y) z = L₃ x (L₄ y z))
  {x₀ : G}
  (h₄ : convolution_exists g k L₄ μ)
  (h₁ : convolution_exists f g L μ)
  (hi : integrable (uncurry (λ x y, (L₃ (f y)) ((L₄ (g (x - y))) (k (x₀ - x))))) (μ.prod μ)) :
  ((f ⋆[L, μ] g) ⋆[L₂, μ] k) x₀ = (f ⋆[L₃, μ] (g ⋆[L₄, μ] k)) x₀ :=
begin
  have h1 := λ t, (L₂.flip (k (x₀ - t))).integral_comp_comm (h₁ t),
  dsimp only [flip_apply] at h1,
  simp_rw [convolution_def, ← (L₃ (f _)).integral_comp_comm (h₄ (x₀ - _)), ← h1, hL],
  rw [integral_integral_swap hi],
  congr', ext t,
  rw [eq_comm, ← integral_sub_right_eq_self _ μ t],
  simp_rw [sub_sub_sub_cancel_right],
end

end normed_space

section real
/-! The one-variable case -/

variables [is_R_or_C 𝕜] --[measurable_space 𝕜] [proper_space 𝕜]
variables [normed_space 𝕜 E]
variables [normed_space 𝕜 E']
variables [normed_space ℝ F] [normed_space 𝕜 F]
variables {f₀ : 𝕜 → E} {g₀ : 𝕜 → E'}
variables {n : with_top ℕ}
variables (L : E →L[𝕜] E' →L[𝕜] F)
variables [complete_space F]
variables {μ : measure 𝕜}
variables [is_add_left_invariant μ] [sigma_finite μ]

lemma has_compact_support.has_deriv_at_convolution_right
  (hf : locally_integrable f₀ μ) (hcg : has_compact_support g₀) (hg : cont_diff 𝕜 1 g₀)
  (x₀ : 𝕜) :
  has_deriv_at (f₀ ⋆[L, μ] g₀) ((f₀ ⋆[L, μ] deriv g₀) x₀) x₀ :=
begin
  convert (hcg.has_fderiv_at_convolution_right L hf hg x₀).has_deriv_at,
  rw [convolution_precompR_apply L hf (hcg.fderiv 𝕜) (hg.continuous_fderiv le_rfl)],
  refl,
end

lemma has_compact_support.has_deriv_at_convolution_left [is_neg_invariant μ]
  (hcf : has_compact_support f₀) (hf : cont_diff 𝕜 1 f₀)
  (hg : locally_integrable g₀ μ) (x₀ : 𝕜) :
  has_deriv_at (f₀ ⋆[L, μ] g₀) ((deriv f₀ ⋆[L, μ] g₀) x₀) x₀ :=
begin
  simp only [← convolution_flip] {single_pass := tt},
  exact hcf.has_deriv_at_convolution_right L.flip hg hf x₀,
end

end real
