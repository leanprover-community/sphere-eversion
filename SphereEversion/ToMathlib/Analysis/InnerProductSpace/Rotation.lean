/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth

! This file was ported from Lean 3 source module to_mathlib.analysis.inner_product_space.rotation
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import SphereEversion.ToMathlib.Analysis.ContDiff
import SphereEversion.ToMathlib.LinearAlgebra.Basic
import SphereEversion.ToMathlib.Analysis.InnerProductSpace.CrossProduct

/-! # Rotation about an axis, considered as a function in that axis -/

noncomputable section

open scoped RealInnerProductSpace

open Module Submodule

set_option synthInstance.checkSynthOrder false
attribute [local instance] FiniteDimensional.of_fact_finrank_eq_succ
set_option synthInstance.checkSynthOrder true

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fact (finrank ℝ E = 3)]
  (ω : Orientation ℝ E (Fin 3))

local infixl:100 "×₃" => ω.crossProduct

namespace Orientation

/-- A family of endomorphisms of `E`, parametrized by `ℝ × E`. The idea is that for nonzero `v : E`
and `t : ℝ` this endomorphism will be the rotation by the angle `t` about the axis spanned by `v`.
-/
def rot (p : ℝ × E) : E →L[ℝ] E :=
  (ℝ ∙ p.2).subtypeL ∘L (orthogonalProjection (ℝ ∙ p.2) : E →L[ℝ] ℝ ∙ p.2) +
      Real.cos (p.1 * Real.pi) •
        (ℝ ∙ p.2)ᗮ.subtypeL ∘L (orthogonalProjection (ℝ ∙ p.2)ᗮ : E →L[ℝ] (ℝ ∙ p.2)ᗮ) +
    Real.sin (p.1 * Real.pi) • LinearMap.toContinuousLinearMap (ω.crossProduct p.2)

/-- Alternative form of the construction `rot`, convenient for the smoothness calculation. -/
def rotAux (p : ℝ × E) : E →L[ℝ] E :=
  Real.cos (p.1 * Real.pi) • ContinuousLinearMap.id ℝ E +
    ((1 - Real.cos (p.1 * Real.pi)) •
        (ℝ ∙ p.2).subtypeL ∘L (orthogonalProjection (ℝ ∙ p.2) : E →L[ℝ] ℝ ∙ p.2) +
      Real.sin (p.1 * Real.pi) • ω.crossProduct' p.2)

theorem rot_eq_aux : ω.rot = ω.rotAux := by
  ext1 p
  dsimp [rot, rotAux]
  rw [id_eq_sum_orthogonalProjection_self_orthogonalComplement (ℝ ∙ p.2)]
  simp only [smul_add, sub_smul, one_smul]
  abel

/-- The map `rot` is smooth on `ℝ × (E \ {0})`. -/
theorem contDiff_rot {p : ℝ × E} (hp : p.2 ≠ 0) : ContDiffAt ℝ ⊤ ω.rot p := by
  simp only [rot_eq_aux]
  refine (contDiffAt_fst.mul_const.cos.smul contDiffAt_const).add ?_
  refine ((contDiffAt_const.sub contDiffAt_fst.mul_const.cos).smul ?_).add
    (contDiffAt_fst.mul_const.sin.smul ?_)
  · exact (contDiffAt_orthogonalProjection_singleton hp).comp _ contDiffAt_snd
  · exact ω.crossProduct'.contDiff.contDiffAt.comp _ contDiffAt_snd

/-- The map `rot` sends `{0} × E` to the identity. -/
theorem rot_zero (v : E) : ω.rot (0, v) = ContinuousLinearMap.id ℝ E := by
  ext w
  simp [rot]

/-- The map `rot` sends `(1, v)` to a transformation which on `(ℝ ∙ v)ᗮ` acts as the negation. -/
theorem rot_one (v : E) {w : E} (hw : w ∈ (ℝ ∙ v)ᗮ) : ω.rot (1, v) w = -w := by
  suffices (orthogonalProjection (Submodule.span ℝ {v}) w : E) +
    -(orthogonalProjection (Submodule.span ℝ {v})ᗮ w) = -w by simpa [rot]
  simp [orthogonalProjection_eq_self_iff.mpr hw,
        orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero hw]

/-- The map `rot` sends `(v, t)` to a transformation fixing `v`. -/
@[simp]
theorem rot_self (p : ℝ × E) : ω.rot p (no_index p.2) = p.2 := by
  have H : orthogonalProjection (ℝ ∙ p.2) p.2 = p.2 :=
    orthogonalProjection_eq_self_iff.mpr (Submodule.mem_span_singleton_self p.2)
  simp [rot, crossProduct_apply_self, orthogonalProjection_orthogonalComplement_singleton_eq_zero,H]

/-- The map `rot` sends `(t, v)` to a transformation preserving `span v`. -/
theorem rot_eq_of_mem_span (p : ℝ × E) {x : E} (hx : x ∈ ℝ ∙ p.2) : ω.rot p x = x := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx; simp_rw [map_smul, rot_self]

/-- The map `rot` sends `(v, t)` to a transformation preserving the subspace `(ℝ ∙ v)ᗮ`. -/
theorem inner_rot_apply_self (p : ℝ × E) (w : E) (hw : w ∈ (ℝ ∙ p.2)ᗮ) :
    ⟪ω.rot p w, no_index p.2⟫ = 0 := by
  have H₁ : orthogonalProjection (ℝ ∙ p.2) w = 0 :=
    orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero hw
  have H₂ : (orthogonalProjection (ℝ ∙ p.2)ᗮ w : E) = w :=
    congr_arg (_ : (ℝ ∙ p.2)ᗮ → E) (orthogonalProjection_mem_subspace_eq_self ⟨w, hw⟩)
  have H₃ : ⟪w, p.2⟫ = 0 := by
    simpa only [real_inner_comm] using hw p.2 (Submodule.mem_span_singleton_self _)
  have H₄ : ⟪p.2×₃w, p.2⟫ = 0 := ω.inner_crossProduct_apply_self p.2 ⟨w, hw⟩
  simp [rot, H₁, H₂, H₃, H₄, inner_smul_left, inner_add_left]

theorem isometry_on_rot (t : ℝ) (v : Metric.sphere (0 : E) 1) (w : (ℝ ∙ (v : E))ᗮ) :
    ‖ω.rot (t, v) w‖ = ‖(w : E)‖ := by
  have h1 : ⟪v×₃w, v×₃w⟫ = ⟪w, w⟫ := by
    simp only [inner_self_eq_norm_sq_to_K, ω.isometry_on_crossProduct v w]
  have h2 : ⟪v×₃w, w⟫ = 0 := ω.inner_crossProduct_apply_apply_self v w
  have h3 : ⟪(w : E), v×₃w⟫ = 0 := by rwa [real_inner_comm]
  have : ‖Real.cos (t * Real.pi) • (w : E) + Real.sin (t * Real.pi) • v×₃w‖ = ‖(w : E)‖ := by
    simp only [@norm_eq_sqrt_re_inner ℝ]
    congr 2
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, h1, h2, h3,
      RCLike.conj_to_real, Submodule.coe_inner]
    linear_combination ⟪(w : E), w⟫ * Real.cos_sq_add_sin_sq (t * Real.pi)
  dsimp [rot]
  simp [orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero w.prop, this]

theorem isometry_rot (t : ℝ) (v : Metric.sphere (0 : E) 1) : Isometry (ω.rot (t, v)) := by
  rw [AddMonoidHomClass.isometry_iff_norm]
  intro w
  obtain ⟨a, ha, w, hw, rfl⟩ := (ℝ ∙ (v : E)).exists_add_mem_mem_orthogonal w
  rw [Submodule.mem_span_singleton] at ha
  obtain ⟨s, rfl⟩ := ha
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), sq, sq, map_add,
    @norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero ℝ,
    @norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero ℝ]
  · have hvw : ‖ω.rot (t, v) w‖ = ‖w‖ :=  ω.isometry_on_rot t v ⟨w, hw⟩
    simp [hvw]
  · simp [inner_smul_left, hw v (Submodule.mem_span_singleton_self _)]
  rw [real_inner_comm]
  simp [inner_smul_right, ω.inner_rot_apply_self (t, v) w hw]

open Real Submodule

open scoped Real

set_option linter.style.multiGoal false in
theorem injOn_rot_of_ne (t : ℝ) {x : E} (hx : x ≠ 0) : Set.InjOn (ω.rot (t, x)) (ℝ ∙ x)ᗮ := by
  change Set.InjOn (ω.rot (t, x)).toLinearMap (ℝ ∙ x)ᗮ
  simp_rw [← LinearMap.ker_inf_eq_bot, Submodule.eq_bot_iff, Submodule.mem_inf]
  rintro y ⟨hy, hy'⟩
  rw [LinearMap.mem_ker] at hy
  change
    ↑((orthogonalProjection (span ℝ {x})) y) +
          cos (t * Real.pi) • ↑((orthogonalProjection (span ℝ {x})ᗮ) y) +
        Real.sin (t * Real.pi) • x×₃y =
      0 at hy
  rw [orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero hy',
    orthogonalProjection_eq_self_iff.mpr hy', coe_zero, zero_add] at hy
  apply_fun fun x ↦ ‖x‖ ^ 2 at hy
  rw [pow_two, @norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero ℝ] at hy
  simp_rw [← pow_two, norm_smul, mul_pow] at hy
  change _ + _ * ‖x×₃(⟨y, hy'⟩ : (span ℝ {x})ᗮ)‖ ^ 2 = ‖(0 : E)‖ ^ 2 at hy
  rw [norm_crossProduct] at hy
  simp +decide only [norm_eq_abs, Even.pow_abs, norm_zero, zero_pow, Ne, not_false_iff] at hy
  change _ + _ * (_ * ‖y‖) ^ 2 = 0 at hy
  rw [mul_pow, ← mul_assoc, ← add_mul, mul_eq_zero, or_iff_not_imp_left] at hy
  have : (0 : ℝ) < cos (t * π) ^ 2 + sin (t * π) ^ 2 * ‖x‖ ^ 2 := by
    have : (0 : ℝ) < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hx) 2
    rw [cos_sq']
    rw [show (1 : ℝ) - sin (t * π) ^ 2 + sin (t * π) ^ 2 * ‖x‖ ^ 2 =
      (1 : ℝ) + sin (t * π) ^ 2 * (‖x‖ ^ 2 - 1) by ring]
    have I₂ : sin (t * π) ^ 2 ≤ 1 := sin_sq_le_one (t * π)
    have I₃ : (0 : ℝ) ≤ sin (t * π) ^ 2 := sq_nonneg _
    rcases I₃.eq_or_lt with (H | H)
    · rw [← H]
      norm_num
    · nlinarith
  · replace hy := hy this.ne'
    exact norm_eq_zero.mp (pow_eq_zero hy)
  · rw [inner_smul_left, inner_smul_right]
    have := inner_crossProduct_apply_apply_self ω x ⟨y, hy'⟩
    change ⟪x×₃y, y⟫ = 0 at this
    rw [real_inner_comm, this]
    simp

theorem injOn_rot (t : ℝ) (x : Metric.sphere (0 : E) 1) :
    Set.InjOn (ω.rot (t, x)) (ℝ ∙ (x : E))ᗮ := by
  intro v hv w hw h
  simpa [sub_eq_zero, h] using (ω.isometry_on_rot t x (⟨v, hv⟩ - ⟨w, hw⟩)).symm

end Orientation
