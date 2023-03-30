/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import to_mathlib.linear_algebra.basic
import to_mathlib.analysis.cont_diff
import to_mathlib.analysis.inner_product_space.cross_product
import analysis.special_functions.trigonometric.deriv
import tactic.linear_combination

/-! # Rotation about an axis, considered as a function in that axis -/

noncomputable theory

open_locale real_inner_product_space
open finite_dimensional

local attribute [instance] fact_finite_dimensional_of_finrank_eq_succ

variables {E : Type*} [normed_add_comm_group E] [inner_product_space ℝ E] [fact (finrank ℝ E = 3)]
  (ω : orientation ℝ E (fin 3))

include ω

local infix `×₃`:100 := ω.cross_product

namespace orientation

/-- A family of endomorphisms of `E`, parametrized by `ℝ × E`. The idea is that for nonzero `v : E`
and `t : ℝ` this endomorphism will be the rotation by the angle `t` about the axis spanned by `v`.
-/
def rot (p : ℝ × E) : E →L[ℝ] E :=
(ℝ ∙ p.2).subtypeL ∘L (orthogonal_projection (ℝ ∙ p.2) : E →L[ℝ] (ℝ ∙ p.2))
  + real.cos (p.1 * real.pi) • (ℝ ∙ p.2)ᗮ.subtypeL ∘L (orthogonal_projection (ℝ ∙ p.2)ᗮ : E →L[ℝ] (ℝ ∙ p.2)ᗮ)
  + real.sin (p.1 * real.pi) • (ω.cross_product p.2).to_continuous_linear_map

/-- Alternative form of the construction `rot`, convenient for the smoothness calculation. -/
def rot_aux (p : ℝ × E) : E →L[ℝ] E :=
real.cos (p.1 * real.pi) • continuous_linear_map.id ℝ E +
  ((1 - real.cos (p.1 * real.pi)) • (ℝ ∙ p.2).subtypeL ∘L (orthogonal_projection (ℝ ∙ p.2) : E →L[ℝ] (ℝ ∙ p.2))
    + real.sin (p.1 * real.pi) • (ω.cross_product' p.2))

lemma rot_eq_aux : ω.rot = ω.rot_aux :=
begin
  ext1 p,
  dsimp [rot, rot_aux],
  rw id_eq_sum_orthogonal_projection_self_orthogonal_complement (ℝ ∙ p.2),
  simp only [smul_add, sub_smul, one_smul],
  abel,
end

/-- The map `rot` is smooth on `ℝ × (E \ {0})`. -/
lemma cont_diff_rot {p : ℝ × E} (hp : p.2 ≠ 0) : cont_diff_at ℝ ⊤ ω.rot p :=
begin
  simp only [rot_eq_aux],
  refine (cont_diff_at_fst.mul_const.cos.smul cont_diff_at_const).add _,
  refine ((cont_diff_at_const.sub cont_diff_at_fst.mul_const.cos).smul _).add
    (cont_diff_at_fst.mul_const.sin.smul _),
  { exact (cont_diff_at_orthogonal_projection_singleton hp).comp _ cont_diff_at_snd },
  { exact ω.cross_product'.cont_diff.cont_diff_at.comp _ cont_diff_at_snd },
end

/-- The map `rot` sends `{0} × E` to the identity. -/
lemma rot_zero (v : E) : ω.rot (0, v) = continuous_linear_map.id ℝ E :=
begin
  ext w,
  simpa [rot] using (eq_sum_orthogonal_projection_self_orthogonal_complement (ℝ ∙ v) w).symm,
end

/-- The map `rot` sends `(1, v)` to a transformation which on `(ℝ ∙ v)ᗮ` acts as the negation. -/
lemma rot_one (v : E) {w : E} (hw : w ∈ (ℝ ∙ v)ᗮ) : ω.rot (1, v) w = - w :=
by simp [rot, orthogonal_projection_eq_self_iff.mpr hw,
  orthogonal_projection_mem_subspace_orthogonal_complement_eq_zero hw]

/-- The map `rot` sends `(v, t)` to a transformation fixing `v`. -/
lemma rot_self (p : ℝ × E) : ω.rot p p.2 = p.2 :=
begin
  have H : ↑(orthogonal_projection (ℝ ∙ p.2) p.2) = p.2 :=
    orthogonal_projection_eq_self_iff.mpr (submodule.mem_span_singleton_self p.2),
  simp [rot, cross_product_apply_self, orthogonal_projection_orthogonal_complement_singleton_eq_zero, H],
end

/-- The map `rot` sends `(t, v)` to a transformation preserving `span v`. -/
lemma rot_eq_of_mem_span (p : ℝ × E) {x : E} (hx : x ∈ ℝ ∙ p.2): ω.rot p x = x :=
by { obtain ⟨a, rfl⟩ := submodule.mem_span_singleton.mp hx, simp_rw [map_smul, rot_self] }

/-- The map `rot` sends `(v, t)` to a transformation preserving the subspace `(ℝ ∙ v)ᗮ`. -/
lemma inner_rot_apply_self (p : ℝ × E) (w : E) (hw : w ∈ (ℝ ∙ p.2)ᗮ) : ⟪ω.rot p w, p.2⟫ = 0 :=
begin
  have H₁ : orthogonal_projection (ℝ ∙ p.2) w = 0 :=
    orthogonal_projection_mem_subspace_orthogonal_complement_eq_zero hw,
  have H₂ : (orthogonal_projection (ℝ ∙ p.2)ᗮ w : E) = w :=
    congr_arg (coe : (ℝ ∙ p.2)ᗮ → E) (orthogonal_projection_mem_subspace_eq_self ⟨w, hw⟩),
  have H₃ : ⟪w, p.2⟫ = 0 :=
    by simpa only [real_inner_comm] using hw p.2 (submodule.mem_span_singleton_self _),
  have H₄ : ⟪p.2 ×₃ w, p.2⟫ = 0 := ω.inner_cross_product_apply_self p.2 ⟨w, hw⟩,
  simp [rot, H₁, H₂, H₃, H₄, inner_smul_left, inner_add_left],
end

lemma isometry_on_rot (t : ℝ) (v : metric.sphere (0:E) 1) (w : (ℝ ∙ (v:E))ᗮ) :
  ‖ω.rot (t, v) w‖ = ‖(w:E)‖ :=
begin
  have h1 : ⟪v ×₃ w, v ×₃ w⟫ = ⟪w, w⟫,
  { simp only [inner_self_eq_norm_sq_to_K, ω.isometry_on_cross_product v w] },
  have h2 : ⟪v ×₃ w, w⟫ = 0 := ω.inner_cross_product_apply_apply_self v w,
  have h3 : ⟪(w:E), v ×₃ w⟫ = 0 := by rwa real_inner_comm,
  have : ‖real.cos (t * real.pi) • (w:E) + real.sin (t * real.pi) • v ×₃ w‖ = ‖(w:E)‖,
  { simp only [@norm_eq_sqrt_inner ℝ],
    congr' 2,
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, h1, h2, h3,
      is_R_or_C.conj_to_real, submodule.coe_inner],
    linear_combination ⟪(w:E), w⟫ * real.cos_sq_add_sin_sq (t * real.pi) },
  simp [rot, orthogonal_projection_mem_subspace_orthogonal_complement_eq_zero w.prop, this],
end

lemma isometry_rot (t : ℝ) (v : metric.sphere (0:E) 1) :
  isometry (ω.rot (t, v)) :=
begin
  rw add_monoid_hom_class.isometry_iff_norm,
  intros w,
  obtain ⟨a, ha, w, hw, rfl⟩ := (ℝ ∙ (v:E)).exists_sum_mem_mem_orthogonal w,
  rw submodule.mem_span_singleton at ha,
  obtain ⟨s, rfl⟩ := ha,
  rw [← sq_eq_sq (norm_nonneg _) (norm_nonneg _), sq, sq, map_add,
    @norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero ℝ,
    @norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero ℝ],
  { have hvw : ‖ω.rot (t, v) w‖ = ‖w‖ := by simpa only using ω.isometry_on_rot t v ⟨w, hw⟩,
    simp [hvw, rot_self] },
  { simp [inner_smul_left, hw v (submodule.mem_span_singleton_self _)] },
  rw real_inner_comm,
  simp [rot_self, inner_smul_right, ω.inner_rot_apply_self (t, v) w hw],
end

open real submodule
open_locale real

lemma inj_on_rot_of_ne (t : ℝ) {x : E} (hx : x ≠ 0) :
  set.inj_on (ω.rot (t, x)) (ℝ ∙ x)ᗮ :=
begin
  change set.inj_on (ω.rot (t, x)).to_linear_map (ℝ ∙ x)ᗮ,
  simp_rw [← linear_map.ker_inf_eq_bot, submodule.eq_bot_iff, submodule.mem_inf],
  rintros y ⟨hy, hy'⟩,
  rw linear_map.mem_ker at hy,
  change ↑((orthogonal_projection (span ℝ {x})) y) +
      cos (t * real.pi) • ↑((orthogonal_projection (span ℝ {x})ᗮ) y) +
      real.sin (t * real.pi) • x ×₃ y = 0 at hy,
  rw [orthogonal_projection_mem_subspace_orthogonal_complement_eq_zero hy',
      orthogonal_projection_eq_self_iff.mpr hy', coe_zero, zero_add] at hy,
  apply_fun (λ x, ‖x‖^2) at hy,
  rw [pow_two, @norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero ℝ] at hy,
  simp_rw [← pow_two, norm_smul, mul_pow] at hy,
  change _ + _ * ‖ x ×₃ (⟨y, hy'⟩ : (span ℝ {x})ᗮ)‖ ^ 2 = ‖(0 : E)‖ ^ 2 at hy,
  rw [norm_cross_product] at hy,
  simp only [norm_eq_abs, pow_bit0_abs, coe_mk, norm_zero, zero_pow', ne.def, bit0_eq_zero,
             nat.one_ne_zero, not_false_iff] at hy,
  change _ + _ * (_ * ‖y‖) ^ 2 = 0 at hy,
  rw [mul_pow, ← mul_assoc, ← add_mul, mul_eq_zero, or_iff_not_imp_left] at hy,
  have : 0 < cos (t * π) ^ 2 + sin (t * π) ^ 2 * ‖x‖ ^ 2,
  { have : 0 < ‖x‖^2,
    exact pow_pos (norm_pos_iff.mpr hx) 2,
    rw cos_sq',
    rw show 1 - sin (t * π) ^ 2 + sin (t * π) ^ 2 * ‖x‖ ^ 2 = 1 + sin (t * π) ^ 2*(‖x‖^2 - 1), by ring,
    have I₁ : ‖x‖ ^ 2 - 1 > -1, by linarith,
    have I₂ : sin (t * π) ^ 2 ≤ 1, from sin_sq_le_one (t * π),
    have I₃ : 0 ≤ sin (t * π) ^ 2, from sq_nonneg _,
    rcases I₃.eq_or_lt with H | H,
    { rw ← H,
      norm_num },
    { nlinarith } },
  replace hy := hy this.ne',
  exact norm_eq_zero.mp (pow_eq_zero hy),
  rw [inner_smul_left, inner_smul_right],
  have := inner_cross_product_apply_apply_self ω x ⟨y, hy'⟩,
  change ⟪x ×₃ y, y⟫ = 0 at this,
  rw [real_inner_comm, this],
  simp,
end

lemma inj_on_rot (t : ℝ) (x : metric.sphere (0:E) 1) :
  set.inj_on (ω.rot (t, x)) (ℝ ∙ (x:E))ᗮ :=
begin
  intros v hv w hw h,
  simpa [sub_eq_zero, h] using (ω.isometry_on_rot t x (⟨v, hv⟩ - ⟨w, hw⟩)).symm
end

end orientation
