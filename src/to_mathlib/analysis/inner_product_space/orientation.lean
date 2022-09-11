/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import analysis.inner_product_space.orientation
import to_mathlib.analysis.inner_product_space.gram_schmidt
import to_mathlib.analysis.inner_product_space.unitary_group
import to_mathlib.linear_algebra.orientation

noncomputable theory

open_locale real_inner_product_space big_operators
open finite_dimensional

variables {E : Type*} [inner_product_space ℝ E] [finite_dimensional ℝ E]

section adjust_to_orientation
variables {ι : Type*} [fintype ι] [decidable_eq ι] [nonempty ι] (e : orthonormal_basis ι ℝ E)
  (x : orientation ℝ E ι)

/-! These lemmas should replace some of the current `basis.adjust_to_orientation`
construction for orthonormal sets. -/

/-- `basis.adjust_to_orientation`, applied to an orthonormal basis, produces an orthonormal
basis. -/
lemma orthonormal_basis.orthonormal_adjust_to_orientation :
  orthonormal ℝ (e.to_basis.adjust_to_orientation x) :=
begin
  apply e.orthonormal.orthonormal_of_forall_eq_or_eq_neg,
  simpa using e.to_basis.adjust_to_orientation_apply_eq_or_eq_neg x
end

def orthonormal_basis.adjust_to_orientation : orthonormal_basis ι ℝ E :=
(e.to_basis.adjust_to_orientation x).to_orthonormal_basis (e.orthonormal_adjust_to_orientation x)

lemma orthonormal_basis.to_basis_adjust_to_orientation :
  (e.adjust_to_orientation x).to_basis = e.to_basis.adjust_to_orientation x :=
(e.to_basis.adjust_to_orientation x).to_basis_to_orthonormal_basis _

/-- `adjust_to_orientation` gives an orthonormal basis with the required orientation. -/
@[simp] lemma orthonormal_basis.orientation_adjust_to_orientation :
  (e.adjust_to_orientation x).to_basis.orientation = x :=
begin
  rw e.to_basis_adjust_to_orientation,
  exact e.to_basis.orientation_adjust_to_orientation x,
end

/-- Every basis vector from `adjust_to_orientation` is either that from the original basis or its
negation. -/
lemma orthonormal_basis.adjust_to_orientation_apply_eq_or_eq_neg (i : ι) :
  e.adjust_to_orientation x i = e i ∨ e.adjust_to_orientation x i = -(e i) :=
by simpa [← e.to_basis_adjust_to_orientation] using e.to_basis.adjust_to_orientation_apply_eq_or_eq_neg x i

lemma orthonormal_basis.det_adjust_to_orientation :
  (e.adjust_to_orientation x).to_basis.det = e.to_basis.det
  ∨ (e.adjust_to_orientation x).to_basis.det = -e.to_basis.det :=
by simpa using e.to_basis.det_adjust_to_orientation x

lemma orthonormal_basis.abs_det_adjust_to_orientation (v : ι → E) :
  |(e.adjust_to_orientation x).to_basis.det v| = |e.to_basis.det v| :=
by simpa using e.to_basis.abs_det_adjust_to_orientation x v

end adjust_to_orientation

section
variables {ι : Type*} [fintype ι] [decidable_eq ι] (a b : orthonormal_basis ι ℝ E)

lemma orthonormal_basis.det_to_matrix_orthonormal_basis_of_same_orientation
  (h : a.to_basis.orientation = b.to_basis.orientation) :
  a.to_basis.det b = 1 :=
begin
  apply (a.det_to_matrix_orthonormal_basis_real b).resolve_right,
  have : 0 < a.to_basis.det b,
  { rw a.to_basis.orientation_eq_iff_det_pos at h,
    simpa using h },
  linarith,
end

lemma orthonormal_basis.det_eq_det_of_same_orientation
  (h : a.to_basis.orientation = b.to_basis.orientation) :
  a.to_basis.det = b.to_basis.det :=
begin
  rw a.to_basis.det.eq_smul_basis_det b.to_basis,
  simp [a.det_to_matrix_orthonormal_basis_of_same_orientation b h],
end

end

namespace orientation

variables {n : ℕ} [fact (finrank ℝ E = n + 1)] (ω : orientation ℝ E (fin n.succ))

def volume_form : alternating_map ℝ E ℝ (fin n.succ) :=
(ω.fin_orthonormal_basis n.succ_pos (fact.out (finrank ℝ E = n + 1))).det

lemma volume_form_robust (b : orthonormal_basis (fin n.succ) ℝ E) (hb : b.to_basis.orientation = ω) :
  ω.volume_form = b.to_basis.det :=
begin
  let e : orthonormal_basis (fin n.succ) ℝ E :=
    (ω.fin_orthonormal_basis n.succ_pos (fact.out _)).to_orthonormal_basis
    (ω.fin_orthonormal_basis_orthonormal _ _),
  apply e.det_eq_det_of_same_orientation b,
  rw [hb, ← ω.fin_orthonormal_basis_orientation n.succ_pos (fact.out _)],
  refl,
end

attribute [irreducible] orientation.volume_form

lemma volume_form_robust' (b : orthonormal_basis (fin n.succ) ℝ E) (v : fin n.succ → E) :
  |ω.volume_form v| = |b.to_basis.det v| :=
by rw [ω.volume_form_robust (b.adjust_to_orientation ω) (b.orientation_adjust_to_orientation ω),
  b.abs_det_adjust_to_orientation]

lemma abs_volume_form_apply_le (v : fin n.succ → E) :
  |ω.volume_form v| ≤ ∏ i : fin n.succ, ∥v i∥ :=
begin
  have : finrank ℝ E = fintype.card (fin n.succ) := by simpa using fact.out _,
  let b : orthonormal_basis (fin n.succ) ℝ E := gram_schmidt_orthonormal_basis' this v,
  have hb : b.to_basis.det v = ∏ i, ⟪b i, v i⟫ := gram_schmidt_orthonormal_basis'_det this v,
  rw [ω.volume_form_robust' b, hb, finset.abs_prod],
  apply finset.prod_le_prod,
  { intros i hi,
    positivity },
  intros i hi,
  convert abs_real_inner_le_norm (b i) (v i),
  simp [b.orthonormal.1 i],
end

lemma volume_form_apply_le (v : fin n.succ → E) :
  ω.volume_form v ≤ ∏ i : fin n.succ, ∥v i∥ :=
(le_abs_self _).trans (ω.abs_volume_form_apply_le v)

lemma abs_volume_form_apply_of_pairwise_orthogonal
  {v : fin n.succ → E} (hv : pairwise (λ i j, ⟪v i, v j⟫ = 0)) :
  |ω.volume_form v| = ∏ i : fin n.succ, ∥v i∥ :=
begin
  have hdim : finrank ℝ E = fintype.card (fin n.succ) := by simpa using fact.out _,
  let b : orthonormal_basis (fin n.succ) ℝ E := gram_schmidt_orthonormal_basis' hdim v,
  have hb : b.to_basis.det v = ∏ i, ⟪b i, v i⟫ := gram_schmidt_orthonormal_basis'_det hdim v,
  rw [ω.volume_form_robust' b, hb, finset.abs_prod],
  by_cases h : ∃ i, v i = 0,
  obtain ⟨i, hi⟩ := h,
  { rw [finset.prod_eq_zero (finset.mem_univ i), finset.prod_eq_zero (finset.mem_univ i)];
    simp [hi] },
  push_neg at h,
  congr,
  ext i,
  have hb : b i = ∥v i∥⁻¹ • v i := gram_schmidt_orthonormal_basis'_apply_of_orthogonal hdim hv (h i),
  simp only [hb, inner_smul_left, real_inner_self_eq_norm_mul_norm, is_R_or_C.conj_to_real],
  rw abs_of_nonneg,
  { have : ∥v i∥ ≠ 0 := by simpa using h i,
    field_simp },
  { positivity },
end

lemma abs_volume_form_apply_of_orthonormal {v : fin n.succ → E} (hv : orthonormal ℝ v) :
  |ω.volume_form v| = 1 :=
by simp [ω.abs_volume_form_apply_of_pairwise_orthogonal (λ i j, hv.2), hv.1]

end orientation
