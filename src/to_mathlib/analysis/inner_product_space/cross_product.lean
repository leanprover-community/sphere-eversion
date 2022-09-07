/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import to_mathlib.analysis.inner_product_space
import to_mathlib.linear_algebra.finrank
import analysis.inner_product_space.dual
import analysis.inner_product_space.orientation

/-! # The cross-product on an oriented real inner product space of dimension three -/

noncomputable theory

open_locale real_inner_product_space
open finite_dimensional

local attribute [instance] fact_finite_dimensional_of_finrank_eq_succ

variables (E : Type*) [inner_product_space ℝ E]

/-- The identification of a finite-dimensional inner product space with its algebraic dual. -/
private def to_dual [finite_dimensional ℝ E] : E ≃ₗ[ℝ] (E →ₗ[ℝ] ℝ) :=
(inner_product_space.to_dual ℝ E).to_linear_equiv ≪≫ₗ linear_map.to_continuous_linear_map.symm

namespace orientation
variables {E} [fact (finrank ℝ E = 3)] (ω : orientation ℝ E (fin 3))

include ω

/-- Linear map from `E` to `E →ₗ[ℝ] E` constructed from a 3-form `Ω` on `E` and an identification of
`E` with its dual.  Effectively, the Hodge star operation.  (Under appropriate hypotheses it turns
out that the image of this map is in `𝔰𝔬(E)`, the skew-symmetric operators, which can be identified
with `Λ²E`.) -/
def cross_product : E →ₗ[ℝ] (E →ₗ[ℝ] E) :=
begin
  let z : alternating_map ℝ E ℝ (fin 0) ≃ₗ[ℝ] ℝ :=
    alternating_map.const_linear_equiv_of_is_empty.symm,
  let y : alternating_map ℝ E ℝ (fin 1) →ₗ[ℝ] E →ₗ[ℝ] ℝ :=
    (linear_map.llcomp ℝ E (alternating_map ℝ E ℝ (fin 0)) ℝ z) ∘ₗ
      alternating_map.curry_left_linear_map,
  let y' : alternating_map ℝ E ℝ (fin 1) →ₗ[ℝ] E :=
    (linear_map.llcomp ℝ (alternating_map ℝ E ℝ (fin 1)) (E →ₗ[ℝ] ℝ) E (to_dual E).symm) y,
  let u : alternating_map ℝ E ℝ (fin 2) →ₗ[ℝ] E →ₗ[ℝ] E :=
    (linear_map.llcomp ℝ E (alternating_map ℝ E ℝ (fin 1)) _ y') ∘ₗ
      alternating_map.curry_left_linear_map,
  exact u ∘ₗ (alternating_map.curry_left_linear_map ω.volume_form),
end

local infix `×₃`:100 := ω.cross_product

lemma cross_product_apply_self (v : E) : v ×₃ v = 0 := by simp [cross_product]

lemma inner_cross_product_apply (u v w : E) : ⟪u ×₃ v, w⟫ = ω.volume_form ![u, v, w] :=
by simp only [cross_product, to_dual, linear_equiv.trans_symm, linear_equiv.symm_symm,
  linear_isometry_equiv.to_linear_equiv_symm, alternating_map.curry_left_linear_map_apply,
  linear_map.coe_comp, function.comp_app, linear_map.llcomp_apply,
  linear_equiv.coe_coe, linear_equiv.trans_apply, linear_isometry_equiv.coe_to_linear_equiv,
  linear_isometry_equiv.norm_map, submodule.coe_norm,
  inner_product_space.to_dual_symm_apply, alternating_map.curry_left_apply_apply,
  alternating_map.const_linear_equiv_of_is_empty_symm_apply,
  eq_self_iff_true, linear_map.coe_to_continuous_linear_map', matrix.zero_empty]

lemma inner_cross_product_apply_self (u : E) (v : (ℝ ∙ u)ᗮ) : ⟪u ×₃ v, u⟫ = 0 :=
begin
  rw ω.inner_cross_product_apply u v u,
  refine ω.volume_form.map_eq_zero_of_eq ![u, v, u] _ (_ : (0 : fin 3) ≠ 2),
  { simp },
  { norm_num }
end

lemma inner_cross_product_apply_apply_self (u : E) (v : (ℝ ∙ u)ᗮ) : ⟪u ×₃ v, v⟫ = 0 :=
begin
  rw ω.inner_cross_product_apply u v v,
  refine ω.volume_form.map_eq_zero_of_eq ![u, v, v] _ (_ : (1 : fin 3) ≠ 2),
  { simp },
  { norm_num }
end

attribute [irreducible] cross_product

/-- The map `cross_product`, upgraded from linear to continuous-linear; useful for calculus. -/
def cross_product' : E →L[ℝ] (E →L[ℝ] E) :=
(↑(linear_map.to_continuous_linear_map : (E →ₗ[ℝ] E) ≃ₗ[ℝ] (E →L[ℝ] E))
  ∘ₗ (ω.cross_product)).to_continuous_linear_map

@[simp] lemma cross_product'_apply (v : E) : ω.cross_product' v = (ω.cross_product v).to_continuous_linear_map := rfl

lemma norm_cross_product (u : E) (v : (ℝ ∙ u)ᗮ) : ∥u ×₃ v∥ = ∥u∥ * ∥v∥ :=
begin
  classical,
  refine le_antisymm _ _,
  { cases eq_or_lt_of_le (norm_nonneg (u ×₃ v)) with h h,
    { rw ← h,
      positivity },
    refine le_of_mul_le_mul_right' _ h,
    rw ← real_inner_self_eq_norm_mul_norm,
    simpa only [inner_cross_product_apply, fin.mk_zero, fin.prod_univ_succ, finset.card_singleton,
      finset.prod_const, fintype.univ_of_subsingleton, matrix.cons_val_fin_one, matrix.cons_val_succ,
      matrix.cons_val_zero, mul_assoc, nat.nat_zero_eq_zero, pow_one, submodule.coe_norm]
      using ω.volume_form_apply_le ![u, v, u ×₃ v] },
  let K : submodule ℝ E := submodule.span ℝ ({u, v} : set E),
  haveI : nontrivial Kᗮ,
  { apply @finite_dimensional.nontrivial_of_finrank_pos ℝ,
    have : finrank ℝ K ≤ _ := finrank_span_insert_le {(v:E)} u,
    have : finrank ℝ _ ≤ 1 := finrank_span_singleton_le (v:E),
    have : finrank ℝ K + finrank ℝ Kᗮ = finrank ℝ E := K.finrank_add_finrank_orthogonal,
    have : finrank ℝ E = 3 := fact.out _,
    linarith },
  obtain ⟨w, hw⟩ : ∃ w : Kᗮ, w ≠ 0 := exists_ne 0,
  have hw' : (w:E) ≠ 0 := λ h, hw (submodule.coe_eq_zero.mp h),
  have H : pairwise (λ i j, ⟪![u, v, w] i, ![u, v, w] j⟫ = 0),
  { intros i j hij,
    have h1 : ⟪u, v⟫ = 0 := v.2 _ (submodule.mem_span_singleton_self _),
    have h2 : ⟪(v:E), w⟫ = 0 := w.2 _ (submodule.subset_span (by simp)),
    have h3 : ⟪u, w⟫ = 0 := w.2 _ (submodule.subset_span (by simp)),
    fin_cases i; fin_cases j; norm_num at hij; simp [h1, h2, h3]; rw real_inner_comm; assumption },
  refine le_of_mul_le_mul_right' _ (by rwa norm_pos_iff : 0 < ∥w∥),
  -- Cauchy-Schwarz inequality for `u ×₃ v` and `w`
  simpa only [inner_cross_product_apply, ω.abs_volume_form_apply_of_pairwise_orthogonal H,
    inner_cross_product_apply, fin.mk_zero, fin.prod_univ_succ, finset.card_singleton,
    finset.prod_const, fintype.univ_of_subsingleton, matrix.cons_val_fin_one, matrix.cons_val_succ,
    matrix.cons_val_zero, nat.nat_zero_eq_zero, pow_one, mul_assoc]
    using abs_real_inner_le_norm (u ×₃ v) w,
end

lemma isometry_on_cross_product (u : metric.sphere (0:E) 1) (v : (ℝ ∙ (u:E))ᗮ) : ∥u ×₃ v∥ = ∥v∥ :=
by simp [norm_cross_product]

end orientation
