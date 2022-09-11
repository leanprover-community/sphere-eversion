/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import to_mathlib.analysis.cont_diff
import to_mathlib.analysis.inner_product_space
import analysis.inner_product_space.orientation
import analysis.special_functions.trigonometric.deriv

/-! # Rotation about an axis, considered as a function in that axis -/

noncomputable theory

lemma linear_map.ker_inf_eq_bot {R : Type*} {R₂ : Type*} {M : Type*} {M₂ : Type*} [ring R] [ring R₂]
  [add_comm_group M] [add_comm_group M₂] [module R M] [module R₂ M₂]
  {τ₁₂ : R →+* R₂} {f : M →ₛₗ[τ₁₂] M₂} {S : submodule R M} :
  linear_map.ker f ⊓ S = ⊥ ↔ set.inj_on f S :=
begin
  rw [set.inj_on_iff_injective, inf_comm, ← disjoint_iff, linear_map.disjoint_ker'],
  split,
  { intros h x y hxy,
    exact subtype.coe_injective (h x x.prop y y.prop hxy) },
  { intros h x hx y hy hxy,
    have : (S : set M).restrict f ⟨x, hx⟩ = (S : set M).restrict f ⟨y, hy⟩, from hxy,
    cases h this,
    refl }
end

open_locale real_inner_product_space
open finite_dimensional

variables (E : Type*) [inner_product_space ℝ E] [finite_dimensional ℝ E]

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

/-- The map `rot` sends `(t, v)` to a transformation preserving `v`. -/
lemma rot_self (p : ℝ × E) : rot Ω p p.2 = p.2 :=
begin
  have H : ↑(orthogonal_projection (ℝ ∙ p.2) p.2) = p.2 :=
    orthogonal_projection_eq_self_iff.mpr (submodule.mem_span_singleton_self p.2),
  simp [rot, A_apply_self, orthogonal_projection_orthogonal_complement_singleton_eq_zero, H],
end

/-- The map `rot` sends `(t, v)` to a transformation preserving `span v`. -/
lemma rot_eq_of_mem_span (p : ℝ × E) {x : E} (hx : x ∈ ℝ ∙ p.2): rot Ω p x = x :=
by { obtain ⟨a, rfl⟩ := submodule.mem_span_singleton.mp hx, simp_rw [map_smul, rot_self] }

omit Ω

namespace orientation

variables [fact (finrank ℝ E = 3)] (ω : orientation ℝ E (fin 3))

lemma norm_A (x : E) (v : (ℝ ∙ x)ᗮ) : ∥A ω.volume_form x v∥ = ∥x∥ * ∥v∥ :=
begin
  classical,
  simp only [A, to_dual, linear_equiv.trans_symm, linear_equiv.symm_symm,
    linear_isometry_equiv.to_linear_equiv_symm, alternating_map.curry_left_linear_map_apply,
    linear_map.coe_comp, function.comp_app, linear_map.llcomp_apply,
    linear_equiv.coe_coe, linear_equiv.trans_apply, linear_isometry_equiv.coe_to_linear_equiv,
    linear_isometry_equiv.norm_map, submodule.coe_norm],
  refine le_antisymm _ _,
  { apply continuous_linear_map.op_norm_le_bound' _ (by positivity : 0 ≤ ∥x∥ * ∥v∥),
    intros w hw,
    simpa only [linear_map.coe_to_continuous_linear_map', linear_map.llcomp_apply,
      linear_equiv.coe_coe, alternating_map.const_linear_equiv_of_is_empty_symm_apply,
      matrix.zero_empty, alternating_map.curry_left_apply_apply, real.norm_eq_abs,
      submodule.coe_norm, fin.prod_univ_succ, ←mul_assoc, matrix.cons_val_zero, matrix.cons_val_succ,
      fintype.univ_of_subsingleton, matrix.cons_val_fin_one, finset.prod_const, finset.card_singleton,
      pow_one]
      using ω.abs_volume_form_apply_le ![x, v, w] },
  let K : submodule ℝ E := submodule.span ℝ ({x, v} : set E),
  haveI : nontrivial Kᗮ,
  { apply @finite_dimensional.nontrivial_of_finrank_pos ℝ,
    have : finrank ℝ K ≤ finset.card {x, (v:E)},
    { simpa [set.to_finset_singleton] using finrank_span_le_card ({x, v} : set E) },
    have : finset.card {x, (v:E)} ≤ finset.card {(v:E)} + 1 := finset.card_insert_le x {v},
    have : finset.card {(v:E)} = 1 := finset.card_singleton (v:E),
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
  refine continuous_linear_map.le_op_norm_of_le' _ hw' _,
  simp only [linear_map.coe_to_continuous_linear_map', linear_map.llcomp_apply,
    linear_equiv.coe_coe, alternating_map.const_linear_equiv_of_is_empty_symm_apply,
    matrix.zero_empty, alternating_map.curry_left_apply_apply, real.norm_eq_abs,
    ω.abs_volume_form_apply_of_pairwise_orthogonal H,
    fin.prod_univ_succ, matrix.cons_val_zero, matrix.cons_val_succ,
    fintype.univ_of_subsingleton, matrix.cons_val_fin_one, finset.prod_const, finset.card_singleton,
    pow_one, ← mul_assoc],
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
    simp_rw [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, h1, h2, h3,
      is_R_or_C.conj_to_real, submodule.coe_inner],
    linear_combination ⟪(v:E), v⟫ * real.cos_sq_add_sin_sq (t * real.pi) },
  simp [rot, orthogonal_projection_mem_subspace_orthogonal_complement_eq_zero v.prop, this],
end

def foo (S : submodule ℝ E) : E →L[ℝ] E :=
S.subtypeL ∘L orthogonal_projection S

lemma rot_eq_foo (p : ℝ × E) :
  rot Ω p = foo (ℝ ∙ p.2) + real.cos (p.1 * real.pi) • foo (ℝ ∙ p.2)ᗮ
    + real.sin (p.1 * real.pi) • (A Ω p.2).to_continuous_linear_map :=
rfl

open real submodule
open_locale real

lemma aux {x : E} (hx : x ≠ 0) (t : ℝ) : 0 < cos (t * π) ^ 2 + sin (t * π) ^ 2 * ∥x∥ ^ 2 :=
begin
  have : 0 < ∥x∥^2,
  exact pow_pos (norm_pos_iff.mpr hx) 2,
  rw cos_sq',
  rw show 1 - sin (t * π) ^ 2 + sin (t * π) ^ 2 * ∥x∥ ^ 2 = 1 + sin (t * π) ^ 2*(∥x∥^2 - 1), by ring,
  have I₁ : ∥x∥ ^ 2 - 1 > -1, by linarith,
  have I₂ : sin (t * π) ^ 2 ≤ 1, from sin_sq_le_one (t * π),
  have I₃ : 0 ≤ sin (t * π) ^ 2, from sq_nonneg _,
  rcases I₃.eq_or_lt with H | H,
  { rw ← H,
    norm_num },
  { nlinarith }
end

lemma inj_on_rot_of_ne (t : ℝ) {x : E} (hx : x ≠ 0) :
  set.inj_on (rot ω.volume_form (t, x)) (ℝ ∙ x)ᗮ :=
begin
  change set.inj_on (rot ω.volume_form (t, x)).to_linear_map (ℝ ∙ x)ᗮ,
  simp_rw [← linear_map.ker_inf_eq_bot, submodule.eq_bot_iff, submodule.mem_inf],
  rintros y ⟨hy, hy'⟩,
  rw linear_map.mem_ker at hy,
  change ↑((orthogonal_projection (span ℝ {x})) y) +
      cos (t * real.pi) • ↑((orthogonal_projection (span ℝ {x})ᗮ) y) +
      real.sin (t * real.pi) • (A ω.volume_form x) y = 0 at hy,
  rw [orthogonal_projection_mem_subspace_orthogonal_complement_eq_zero hy',
      orthogonal_projection_eq_self_iff.mpr hy', coe_zero, zero_add] at hy,
  apply_fun (λ x, ∥x∥^2) at hy,
  rw [pow_two, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero] at hy,
  simp_rw [← pow_two, norm_smul, mul_pow] at hy,
  change _ + _ * ∥((A ω.volume_form) x) (⟨y, hy'⟩ : (span ℝ {x})ᗮ)∥ ^ 2 = ∥(0 : E)∥ ^ 2 at hy,
  rw [norm_A] at hy,
  simp only [norm_eq_abs, pow_bit0_abs, coe_mk, norm_zero, zero_pow', ne.def, bit0_eq_zero,
             nat.one_ne_zero, not_false_iff] at hy,
  change _ + _ * (_ * ∥y∥) ^ 2 = 0 at hy,
  rw [mul_pow, ← mul_assoc, ← add_mul, mul_eq_zero, or_iff_not_imp_left] at hy,
  have : 0 < cos (t * π) ^ 2 + sin (t * π) ^ 2 * ∥x∥ ^ 2,
  { apply aux hx },
  replace hy := hy this.ne',
  exact norm_eq_zero.mp (pow_eq_zero hy),
  rw [inner_smul_left, inner_smul_right],
  have := inner_A_apply_apply_self ω.volume_form x ⟨y, hy'⟩,
  change ⟪A ω.volume_form x y, y⟫ = 0 at this,
  rw [real_inner_comm, this],
  simp,
end

lemma inj_on_rot (t : ℝ) (x : metric.sphere (0:E) 1) :
  set.inj_on (rot ω.volume_form (t, x)) (ℝ ∙ (x:E))ᗮ :=
begin
  intros v hv w hw h,
  simpa [sub_eq_zero, h] using (ω.isometry_on_rot t x (⟨v, hv⟩ - ⟨w, hw⟩)).symm
end

end orientation
