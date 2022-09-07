/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import to_mathlib.analysis.cont_diff
import to_mathlib.analysis.inner_product_space
import to_mathlib.linear_algebra.finrank
import analysis.inner_product_space.orientation
import analysis.special_functions.trigonometric.deriv

/-! # Rotation about an axis, considered as a function in that axis -/

noncomputable theory

open_locale real_inner_product_space
open finite_dimensional

variables (E : Type*) [inner_product_space ℝ E]

section
variables [finite_dimensional ℝ E]

/-- The identification of a finite-dimensional inner product space with its algebraic dual. -/
def to_dual : E ≃ₗ[ℝ] (E →ₗ[ℝ] ℝ) :=
(inner_product_space.to_dual ℝ E).to_linear_equiv ≪≫ₗ linear_map.to_continuous_linear_map.symm

variables {E} (Ω : alternating_map ℝ E ℝ (fin 3))
include E Ω

/-- Linear map from `E` to `E →ₗ[ℝ] E` constructed from a 3-form `Ω` on `E` and an identification of
`E` with its dual.  Effectively, the Hodge star operation.  (Under appropriate hypotheses it turns
out that the image of this map is in `𝔰𝔬(E)`, the skew-symmetric operators, which can be identified
with `Λ²E`.) -/
def A : E →ₗ[ℝ] (E →ₗ[ℝ] E) :=
begin
  let z : alternating_map ℝ E ℝ (fin 0) ≃ₗ[ℝ] ℝ :=
    alternating_map.const_linear_equiv_of_is_empty.symm,
  let y : alternating_map ℝ E ℝ (fin 1) →ₗ[ℝ] E →ₗ[ℝ] ℝ :=
    (linear_map.llcomp ℝ E (alternating_map ℝ E ℝ (fin 0)) ℝ z) ∘ₗ
      alternating_map.curry_left_linear_map,
  let y' : alternating_map ℝ E ℝ (fin 1) →ₗ[ℝ] E :=
    (linear_map.llcomp ℝ (alternating_map ℝ E ℝ (fin 1)) (E →ₗ[ℝ] ℝ) E (to_dual E).symm) y,
  let x : alternating_map ℝ E ℝ (fin 2) →ₗ[ℝ] E →ₗ[ℝ] E :=
    (linear_map.llcomp ℝ E (alternating_map ℝ E ℝ (fin 1)) _ y') ∘ₗ
      alternating_map.curry_left_linear_map,
  exact x ∘ₗ Ω.curry_left_linear_map,
end

lemma A_apply_self (v : E) : A Ω v v = 0 := by simp [A]

lemma inner_A_apply (u v w : E) : ⟪A Ω u v, w⟫ = Ω ![u, v, w] :=
by simp only [A, to_dual, linear_equiv.trans_symm, linear_equiv.symm_symm,
  linear_isometry_equiv.to_linear_equiv_symm, alternating_map.curry_left_linear_map_apply,
  linear_map.coe_comp, function.comp_app, linear_map.llcomp_apply,
  linear_equiv.coe_coe, linear_equiv.trans_apply, linear_isometry_equiv.coe_to_linear_equiv,
  linear_isometry_equiv.norm_map, submodule.coe_norm,
  inner_product_space.to_dual_symm_apply, alternating_map.curry_left_apply_apply,
  alternating_map.const_linear_equiv_of_is_empty_symm_apply,
  eq_self_iff_true, linear_map.coe_to_continuous_linear_map', matrix.zero_empty]

lemma inner_A_apply_self (x : E) (v : (ℝ ∙ x)ᗮ) : ⟪A Ω x v, x⟫ = 0 :=
begin
  rw inner_A_apply Ω x v x,
  refine Ω.map_eq_zero_of_eq ![x, v, x] _ (_ : (0 : fin 3) ≠ 2),
  { simp },
  { norm_num }
end

lemma inner_A_apply_apply_self (x : E) (v : (ℝ ∙ x)ᗮ) : ⟪A Ω x v, v⟫ = 0 :=
begin
  rw inner_A_apply Ω x v v,
  refine Ω.map_eq_zero_of_eq ![x, v, v] _ (_ : (1 : fin 3) ≠ 2),
  { simp },
  { norm_num }
end

attribute [irreducible] A

/-- The map `A`, upgraded from linear to continuous-linear; useful for calculus. -/
def A' : E →L[ℝ] (E →L[ℝ] E) :=
(↑(linear_map.to_continuous_linear_map : (E →ₗ[ℝ] E) ≃ₗ[ℝ] (E →L[ℝ] E))
  ∘ₗ (A Ω)).to_continuous_linear_map

@[simp] lemma A'_apply (v : E) : A' Ω v = (A Ω v).to_continuous_linear_map := rfl

/-- A family of endomorphisms of `E`, parametrized by `ℝ × E`. The idea is that for nonzero `v : E`
and `t : ℝ` this endomorphism should be the rotation by the angle `t` about the axis spanned by `v`,
although this definition does not itself impose enough conditions to ensure that meaning. -/
def rot (p : ℝ × E) : E →L[ℝ] E :=
(ℝ ∙ p.2).subtypeL ∘L (orthogonal_projection (ℝ ∙ p.2) : E →L[ℝ] (ℝ ∙ p.2))
  + real.cos (p.1 * real.pi) • (ℝ ∙ p.2)ᗮ.subtypeL ∘L (orthogonal_projection (ℝ ∙ p.2)ᗮ : E →L[ℝ] (ℝ ∙ p.2)ᗮ)
  + real.sin (p.1 * real.pi) • (A Ω p.2).to_continuous_linear_map

/-- Alternative form of the construction `rot`, convenient for the smoothness calculation. -/
def rot_aux (p : ℝ × E) : E →L[ℝ] E :=
real.cos (p.1 * real.pi) • continuous_linear_map.id ℝ E +
  ((1 - real.cos (p.1 * real.pi)) • (ℝ ∙ p.2).subtypeL ∘L (orthogonal_projection (ℝ ∙ p.2) : E →L[ℝ] (ℝ ∙ p.2))
    + real.sin (p.1 * real.pi) • (A' Ω p.2))

lemma rot_eq_aux : rot Ω = rot_aux Ω :=
begin
  ext1 p,
  dsimp [rot, rot_aux],
  rw id_eq_sum_orthogonal_projection_self_orthogonal_complement (ℝ ∙ p.2),
  simp only [smul_add, sub_smul, one_smul],
  abel,
end

/-- The map `rot` is smooth on `ℝ × (E \ {0})`. -/
lemma cont_diff_rot {p : ℝ × E} (hp : p.2 ≠ 0) : cont_diff_at ℝ ⊤ (rot Ω) p :=
begin
  simp only [rot_eq_aux],
  refine (cont_diff_at_fst.mul_const.cos.smul cont_diff_at_const).add _,
  refine ((cont_diff_at_const.sub cont_diff_at_fst.mul_const.cos).smul _).add
    (cont_diff_at_fst.mul_const.sin.smul _),
  { exact (cont_diff_at_orthogonal_projection_singleton hp).comp _ cont_diff_at_snd },
  { exact (A' Ω).cont_diff.cont_diff_at.comp _ cont_diff_at_snd },
end

/-- The map `rot` sends `{0} × E` to the identity. -/
lemma rot_zero (v : E) : rot Ω (0, v) = continuous_linear_map.id ℝ E :=
begin
  ext w,
  simpa [rot] using (eq_sum_orthogonal_projection_self_orthogonal_complement (ℝ ∙ v) w).symm,
end

/-- The map `rot` sends `(1, v)` to a transformation which on `(ℝ ∙ v)ᗮ` acts as the negation. -/
lemma rot_one (v : E) {w : E} (hw : w ∈ (ℝ ∙ v)ᗮ) : rot Ω (1, v) w = - w :=
by simp [rot, orthogonal_projection_eq_self_iff.mpr hw,
  orthogonal_projection_mem_subspace_orthogonal_complement_eq_zero hw]

/-- The map `rot` sends `(v, t)` to a transformation fixing `v`. -/
lemma rot_self (p : ℝ × E) : rot Ω p p.2 = p.2 :=
begin
  have H : ↑(orthogonal_projection (ℝ ∙ p.2) p.2) = p.2 :=
    orthogonal_projection_eq_self_iff.mpr (submodule.mem_span_singleton_self p.2),
  simp [rot, A_apply_self, orthogonal_projection_orthogonal_complement_singleton_eq_zero, H],
end

/-- The map `rot` sends `(v, t)` to a transformation preserving the subspace `(ℝ ∙ v)ᗮ`. -/
lemma inner_rot_apply_self (p : ℝ × E) (w : E) (hw : w ∈ (ℝ ∙ p.2)ᗮ) : ⟪rot Ω p w, p.2⟫ = 0 :=
begin
  have H₁ : orthogonal_projection (ℝ ∙ p.2) w = 0 :=
    orthogonal_projection_mem_subspace_orthogonal_complement_eq_zero hw,
  have H₂ : (orthogonal_projection (ℝ ∙ p.2)ᗮ w : E) = w :=
    congr_arg (coe : (ℝ ∙ p.2)ᗮ → E) (orthogonal_projection_mem_subspace_eq_self ⟨w, hw⟩),
  have H₃ : ⟪w, p.2⟫ = 0 :=
    by simpa only [real_inner_comm] using hw p.2 (submodule.mem_span_singleton_self _),
  have H₄ : ⟪A Ω p.2 w, p.2⟫ = 0 := inner_A_apply_self Ω p.2 ⟨w, hw⟩,
  simp [rot, H₁, H₂, H₃, H₄, inner_smul_left, inner_add_left],
end

end

namespace orientation
variables {E} [fact (finrank ℝ E = 3)] (ω : orientation ℝ E (fin 3))

local attribute [instance] fact_finite_dimensional_of_finrank_eq_succ

lemma norm_A (x : E) (v : (ℝ ∙ x)ᗮ) : ∥A ω.volume_form x v∥ = ∥x∥ * ∥v∥ :=
begin
  classical,
  refine le_antisymm _ _,
  { cases eq_or_lt_of_le (norm_nonneg (A ω.volume_form x v)) with h h,
    { rw ← h,
      positivity },
    refine le_of_mul_le_mul_right' _ h,
    rw ← real_inner_self_eq_norm_mul_norm,
    simpa only [inner_A_apply, fin.mk_zero, fin.prod_univ_succ, finset.card_singleton,
      finset.prod_const, fintype.univ_of_subsingleton, matrix.cons_val_fin_one, matrix.cons_val_succ,
      matrix.cons_val_zero, mul_assoc, nat.nat_zero_eq_zero, pow_one, submodule.coe_norm]
      using ω.volume_form_apply_le ![x, ↑v, A ω.volume_form x v] },
  let K : submodule ℝ E := submodule.span ℝ ({x, v} : set E),
  haveI : nontrivial Kᗮ,
  { apply @finite_dimensional.nontrivial_of_finrank_pos ℝ,
    have : finrank ℝ K ≤ _ := finrank_span_insert_le {(v:E)} x,
    have : finrank ℝ _ ≤ 1 := finrank_span_singleton_le (v:E),
    have : finrank ℝ K + finrank ℝ Kᗮ = finrank ℝ E := K.finrank_add_finrank_orthogonal,
    have : finrank ℝ E = 3 := fact.out _,
    linarith },
  obtain ⟨w, hw⟩ : ∃ w : Kᗮ, w ≠ 0 := exists_ne 0,
  have hw' : (w:E) ≠ 0 := λ h, hw (submodule.coe_eq_zero.mp h),
  have H : pairwise (λ i j, ⟪![x, v, ↑w] i, ![x, v, ↑w] j⟫ = 0),
  { intros i j hij,
    have h1 : ⟪x, v⟫ = 0 := v.2 _ (submodule.mem_span_singleton_self _),
    have h2 : ⟪(v:E), w⟫ = 0 := w.2 _ (submodule.subset_span (by simp)),
    have h3 : ⟪x, w⟫ = 0 := w.2 _ (submodule.subset_span (by simp)),
    fin_cases i; fin_cases j; norm_num at hij; simp [h1, h2, h3]; rw real_inner_comm; assumption },
  refine le_of_mul_le_mul_right' _ (by rwa norm_pos_iff : 0 < ∥w∥),
  -- Cauchy-Schwarz inequality for `A ω.volume_form x v` and `w`
  simpa only [inner_A_apply, ω.abs_volume_form_apply_of_pairwise_orthogonal H, inner_A_apply,
    fin.mk_zero, fin.prod_univ_succ, finset.card_singleton, finset.prod_const,
    fintype.univ_of_subsingleton, matrix.cons_val_fin_one, matrix.cons_val_succ, matrix.cons_val_zero,
    nat.nat_zero_eq_zero, pow_one, mul_assoc]
    using abs_real_inner_le_norm (A ω.volume_form x v) w,
end

lemma isometry_on_A (x : metric.sphere (0:E) 1) (v : (ℝ ∙ (x:E))ᗮ) : ∥A ω.volume_form x v∥ = ∥v∥ :=
by simp [norm_A]

lemma isometry_on_rot (t : ℝ) (x : metric.sphere (0:E) 1) (v : (ℝ ∙ (x:E))ᗮ) :
  ∥rot ω.volume_form (t, x) v∥ = ∥(v:E)∥ :=
begin
  have h1 : ⟪A ω.volume_form x v, A ω.volume_form x v⟫ = ⟪v, v⟫,
  { simp only [inner_self_eq_norm_sq_to_K, ω.isometry_on_A x v] },
  have h2 : ⟪A ω.volume_form x v, v⟫ = 0 := inner_A_apply_apply_self ω.volume_form x v,
  have h3 : ⟪(v:E), A ω.volume_form x v⟫ = 0 := by rwa real_inner_comm,
  have : ∥real.cos (t * real.pi) • (v:E) + real.sin (t * real.pi) • A ω.volume_form x v∥ = ∥(v:E)∥,
  { simp only [norm_eq_sqrt_inner],
    congr' 2,
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, h1, h2, h3,
      is_R_or_C.conj_to_real, submodule.coe_inner],
    linear_combination ⟪(v:E), v⟫ * real.cos_sq_add_sin_sq (t * real.pi) },
  simp [rot, orthogonal_projection_mem_subspace_orthogonal_complement_eq_zero v.prop, this],
end

lemma isometry_rot (t : ℝ) (x : metric.sphere (0:E) 1) :
  isometry (rot ω.volume_form (t, x)) :=
begin
  rw add_monoid_hom_class.isometry_iff_norm,
  intros v,
  obtain ⟨a, ha, w, hw, rfl⟩ := (ℝ ∙ (x:E)).exists_sum_mem_mem_orthogonal v,
  rw submodule.mem_span_singleton at ha,
  obtain ⟨s, rfl⟩ := ha,
  rw [← sq_eq_sq (norm_nonneg _) (norm_nonneg _), sq, sq, map_add,
    norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero,
    norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero],
  { have hxw : ∥rot ω.volume_form (t, x) w∥ = ∥w∥ := by simpa only using ω.isometry_on_rot t x ⟨w, hw⟩,
    simp [hxw, rot_self] },
  { simp [inner_smul_left, hw x (submodule.mem_span_singleton_self _)] },
  rw real_inner_comm,
  simp [rot_self, inner_smul_right, inner_rot_apply_self ω.volume_form (t, x) w hw],
end

end orientation
