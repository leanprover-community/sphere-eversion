import to_mathlib.analysis.normed_space.add_torsor_bases
import to_mathlib.analysis.calculus

noncomputable theory
open set function
open_locale affine matrix big_operators

section barycentric_det

variables (ι R k P : Type*) {M : Type*} [ring R] [add_comm_group M] [module R M] [affine_space M P]
include M

-- On reflection, it might be better to drop this definition and just write
-- `affine_independent R v ∧ affine_span R (range v) = ⊤` everywhere instead of
-- `v ∈ affine_bases ι R P`.
def affine_bases : set (ι → P) :=
{ v | affine_independent R v ∧ affine_span R (range v) = ⊤ }

variables [fintype ι] [decidable_eq ι]

lemma affine_bases_findim [field k] [module k M] [finite_dimensional k M]
  (h : fintype.card ι = finite_dimensional.finrank k M + 1) :
  affine_bases ι k P = { v | affine_independent k v } :=
begin
  ext v,
  simp only [affine_bases, mem_set_of_eq, and_iff_left_iff_imp],
  exact λ h_ind, h_ind.affine_span_eq_top_iff_card_eq_finrank_add_one.mpr h,
end

lemma mem_affine_bases_iff [nontrivial R] (b : affine_basis ι R P) (v : ι → P) :
  v ∈ affine_bases ι R P ↔ is_unit (b.to_matrix v) :=
(b.is_unit_to_matrix_iff v).symm

def eval_barycentric_coords [decidable_pred (∈ affine_bases ι R P)] (p : P) (v : ι → P) : ι → R :=
if h : v ∈ affine_bases ι R P then ((affine_basis.mk v h.1 h.2).coords p : ι → R) else 0

@[simp] lemma eval_barycentric_coords_apply_of_mem_bases [decidable_pred (∈ affine_bases ι R P)]
  (p : P) {v : ι → P} (h : v ∈ affine_bases ι R P) :
  eval_barycentric_coords ι R P p v = (affine_basis.mk v h.1 h.2).coords p :=
dif_pos h

@[simp] lemma eval_barycentric_coords_apply_of_not_mem_bases [decidable_pred (∈ affine_bases ι R P)]
  (p : P) {v : ι → P} (h : v ∉ affine_bases ι R P) :
  eval_barycentric_coords ι R P p v = 0 :=
dif_neg h


variables {ι R P}

-- This could be stated and proved without having to assume a choice of affine basis if we
-- had a sufficiently-developed theory of exterior algebras. Two key results which are missing
-- are that the top exterior power is one-dimensional (and thus its non-zero elements are a
-- multiplicative torsor for the scalar units) and that linear independence corresponds to
-- exterior product being non-zero.
lemma eval_barycentric_coords_eq_det
  (S : Type*) [field S] [module S M] [∀ v, decidable (v ∈ affine_bases ι S P)]
  (b : affine_basis ι S P) (p : P) (v : ι → P) :
  eval_barycentric_coords ι S P p v = (b.to_matrix v).det⁻¹ • (b.to_matrix v)ᵀ.cramer (b.coords p) :=
begin
  ext i,
  by_cases h : v ∈ affine_bases ι S P,
  { simp only [eval_barycentric_coords, h, dif_pos, algebra.id.smul_eq_mul, pi.smul_apply,
      affine_basis.coords_apply, ← b.det_smul_coords_eq_cramer_coords ⟨v, h.1, h.2⟩, smul_smul],
    convert (one_mul _).symm,
    have hu := b.is_unit_to_matrix ⟨v, h.1, h.2⟩,
    rw matrix.is_unit_iff_is_unit_det at hu,
    rw ← ring.inverse_eq_inv,
    exact ring.inverse_mul_cancel _ hu, },
  { -- Both sides are "junk values". It's only slightly evil to take advantage of this.
    simp only [eval_barycentric_coords, h, algebra.id.smul_eq_mul, pi.zero_apply, inv_eq_zero,
      dif_neg, not_false_iff, zero_eq_mul, pi.smul_apply],
    left,
    rwa [mem_affine_bases_iff ι S P b v, matrix.is_unit_iff_is_unit_det,
      is_unit_iff_ne_zero, not_not] at h, },
end

end barycentric_det

namespace matrix

variables (ι k : Type*) [fintype ι] [decidable_eq ι] [nondiscrete_normed_field k]

attribute [instance] matrix.normed_group matrix.normed_space

-- This should really be deduced from general results about continuous multilinear maps.
lemma smooth_det (m : with_top ℕ) :
  cont_diff k m (det : matrix ι ι k → k) :=
begin
  suffices : ∀ (n : ℕ), cont_diff k m (det : matrix (fin n) (fin n) k → k),
  { have h : (det : matrix ι ι k → k) = det ∘ reindex (fintype.equiv_fin ι) (fintype.equiv_fin ι),
    { ext, simp, },
    rw h,
    apply (this (fintype.card ι)).comp,
    exact cont_diff_pi.mpr (λ i, cont_diff_pi.mpr (λ j, cont_diff_apply_apply _ _)), },
  intros n,
  induction n with n ih,
  { rw coe_det_is_empty,
    exact cont_diff_const, },
  change cont_diff k m (λ (A : matrix (fin n.succ) (fin n.succ) k), A.det),
  simp_rw det_succ_column_zero,
  apply cont_diff.sum (λ l _, _),
  apply cont_diff.mul,
  { refine cont_diff_const.mul _,
    apply cont_diff_apply_apply, },
  { apply ih.comp,
    refine cont_diff_pi.mpr (λ i, cont_diff_pi.mpr (λ j, _)),
    simp only [minor_apply],
    apply cont_diff_apply_apply, },
end

end matrix

section smooth_barycentric

variables (ι 𝕜 F : Type*)
variables [fintype ι] [decidable_eq ι] [nondiscrete_normed_field 𝕜] [complete_space 𝕜]
variables [normed_group F] [normed_space 𝕜 F]

-- An alternative approach would be to prove the affine version of `cont_diff_at_map_inverse`
-- and prove that barycentric coordinates give a continuous affine equivalence to
-- `{ f : ι →₀ 𝕜 | f.sum = 1 }`. This should obviate the need for the finite-dimensionality assumption.
lemma smooth_barycentric [decidable_pred (∈ affine_bases ι 𝕜 F)] [finite_dimensional 𝕜 F]
  (h : fintype.card ι = finite_dimensional.finrank 𝕜 F + 1) :
  cont_diff_on 𝕜 ⊤ (uncurry (eval_barycentric_coords ι 𝕜 F)) (@univ F ×ˢ (affine_bases ι 𝕜 F)) :=
begin
  obtain ⟨b : affine_basis ι 𝕜 F⟩ := affine_basis.exists_affine_basis_of_finite_dimensional h,
  simp_rw [uncurry_def, cont_diff_on_pi, eval_barycentric_coords_eq_det 𝕜 b],
  intros i,
  simp only [algebra.id.smul_eq_mul, pi.smul_apply, matrix.cramer_transpose_apply],
  have h_snd : cont_diff 𝕜 ⊤ (λ (x : F × (ι → F)), b.to_matrix x.snd),
  { refine cont_diff.comp _ cont_diff_snd,
    refine cont_diff_pi.mpr (λ j, cont_diff_pi.mpr (λ j', _)),
    exact (smooth_barycentric_coord b j').comp (cont_diff_apply j), },
  apply cont_diff_on.mul,
  { apply ((matrix.smooth_det ι 𝕜 ⊤).comp h_snd).cont_diff_on.inv,
    rintros ⟨p, v⟩ hpv,
    have hv : is_unit (b.to_matrix v), { simpa [mem_affine_bases_iff ι 𝕜 F b v] using hpv, },
    rw [← is_unit_iff_ne_zero, ← matrix.is_unit_iff_is_unit_det],
    exact hv, },
  { refine ((matrix.smooth_det ι 𝕜 ⊤).comp _).cont_diff_on,
    refine cont_diff_pi.mpr (λ j, cont_diff_pi.mpr (λ j', _)),
    simp only [matrix.update_row_apply, affine_basis.to_matrix_apply, affine_basis.coords_apply],
    by_cases hij : j = i,
    { simp only [hij, if_true, eq_self_iff_true],
      exact (smooth_barycentric_coord b j').fst', },
    { simp only [hij, if_false],
      exact (smooth_barycentric_coord b j').comp (cont_diff_pi.mp cont_diff_snd j), }, },
end

end smooth_barycentric
