import analysis.inner_product_space.orientation
import to_mathlib.analysis.inner_product_space.unitary_group

noncomputable theory

open_locale real_inner_product_space big_operators
open finite_dimensional

variables {E : Type*} [inner_product_space ℝ E] [finite_dimensional ℝ E]

section
variables {ι : Type*} [fintype ι] [decidable_eq ι] (a b : orthonormal_basis ι ℝ E)

lemma orthonormal_basis.det_to_matrix_orthonormal_basis_of_same_orientation
  (h : a.to_basis.orientation = b.to_basis.orientation) :
  a.to_basis.det b = 1 :=
begin
  have : a.to_basis.det b = -1 ∨ a.to_basis.det b = 1,
  { simpa using a.det_to_matrix_orthonormal_basis_real b },
  apply this.resolve_left,
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
  b.to_basis.det = ω.volume_form :=
begin
  let e : orthonormal_basis (fin n.succ) ℝ E :=
    (ω.fin_orthonormal_basis n.succ_pos (fact.out _)).to_orthonormal_basis
    (ω.fin_orthonormal_basis_orthonormal _ _),
  apply b.det_eq_det_of_same_orientation e,
  rw [hb, ← ω.fin_orthonormal_basis_orientation n.succ_pos (fact.out _)],
  refl,
end

attribute [irreducible] orientation.volume_form

lemma abs_volume_form_apply_le (v : fin n.succ → E) :
  |ω.volume_form v| ≤ ∏ i : fin n.succ, ∥v i∥ :=
sorry

lemma volume_form_apply_le (v : fin n.succ → E) :
  ω.volume_form v ≤ ∏ i : fin n.succ, ∥v i∥ :=
(le_abs_self _).trans (ω.abs_volume_form_apply_le v)

lemma abs_volume_form_apply_of_pairwise_orthogonal
  {v : fin n.succ → E} (hv : pairwise (λ i j, ⟪v i, v j⟫ = 0)) :
  |ω.volume_form v| = ∏ i : fin n.succ, ∥v i∥ :=
sorry

lemma abs_volume_form_apply_of_orthonormal {v : fin n.succ → E} (hv : orthonormal ℝ v) :
  |ω.volume_form v| = 1 :=
by simp [ω.abs_volume_form_apply_of_pairwise_orthogonal (λ i j, hv.2), hv.1]

end orientation
