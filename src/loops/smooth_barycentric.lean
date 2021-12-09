import analysis.calculus.affine_map
import analysis.normed_space.add_torsor_bases

-- TODO Sort out this file: total mess.

noncomputable theory

section barycentric_det

open set function
open_locale affine matrix

variables (ι R P : Type*) {M : Type*} [ring R] [add_comm_group M] [module R M] [affine_space M P]
include M

def affine_bases : set (ι → P) :=
{ v | affine_independent R v ∧ affine_span R (range v) = ⊤ }

variables [fintype ι] [decidable_eq ι]

lemma mem_affine_bases_iff [nontrivial R] (b : affine_basis ι R P) (v : ι → P) :
  v ∈ affine_bases ι R P ↔ is_unit (b.to_matrix v) :=
(b.is_unit_to_matrix_iff v).symm

def eval_barycentric_coords [∀ v, decidable (v ∈ affine_bases ι R P)] (p : P) (v : ι → P) : ι → R :=
if h : v ∈ affine_bases ι R P then ((affine_basis.mk v h.1 h.2).coords p : ι → R) else 0

variables {ι R P}

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
    simp at hu,
    rw ← ring.inverse_eq_inv,
    exact ring.inverse_mul_cancel _ hu, },
  { simp only [eval_barycentric_coords, h, algebra.id.smul_eq_mul, pi.zero_apply, inv_eq_zero,
      dif_neg, not_false_iff, zero_eq_mul, pi.smul_apply],
    left,
    rwa [mem_affine_bases_iff ι S P b v, matrix.is_unit_iff_is_unit_det,
      is_unit_iff_ne_zero, not_not] at h, },
end

end barycentric_det

section smooth_det

variables (ι k : Type*) [fintype ι] [decidable_eq ι]
variables [nondiscrete_normed_field k] {Z : Type*} [normed_group Z] [normed_space k Z]

lemma times_cont_diff_apply {ι : Type*} [fintype ι] {m : with_top ℕ} (i : ι) :
  times_cont_diff k m (λ (f : ι → Z), f i) :=
(continuous_linear_map.proj i : (ι → Z) →L[k] Z).times_cont_diff

lemma times_cont_diff_apply_apply {ι : Type*} [fintype ι] {m : with_top ℕ} (i j : ι) :
  times_cont_diff k m (λ (f : ι → ι → Z), f j i) :=
(@times_cont_diff_apply k _ Z _ _ ι _ m i).comp (@times_cont_diff_apply k _ (ι → Z) _ _ ι _ m j)

namespace matrix

-- Exists in Mathlib but needs bump (looks like #10398 was breakage).
@[simp] lemma coe_det_is_empty {n R : Type*} [comm_ring R] [is_empty n] [decidable_eq n] :
  (det : matrix n n R → R) = function.const _ 1 :=
by { ext, exact det_is_empty, }

attribute [instance] normed_group normed_space

lemma smooth_det (m : with_top ℕ) :
  times_cont_diff k m (det : matrix ι ι k → k) :=
begin
  suffices : ∀ (n : ℕ), times_cont_diff k m (det : matrix (fin n) (fin n) k → k),
  { have h : (det : matrix ι ι k → k) = det ∘ reindex (fintype.equiv_fin ι) (fintype.equiv_fin ι),
    { ext, simp, },
    rw h,
    apply (this (fintype.card ι)).comp,
    exact times_cont_diff_pi.mpr (λ i, times_cont_diff_pi.mpr (λ j, times_cont_diff_apply_apply _ _ _)), },
  intros n,
  induction n with n ih,
  { rw coe_det_is_empty,
    exact times_cont_diff_const, },
  change times_cont_diff k m (λ (A : matrix (fin n.succ) (fin n.succ) k), A.det),
  simp_rw det_succ_column_zero,
  apply times_cont_diff.sum (λ l _, _),
  apply times_cont_diff.mul,
  { refine times_cont_diff_const.mul _,
    apply times_cont_diff_apply_apply, },
  { apply ih.comp,
    refine times_cont_diff_pi.mpr (λ i, times_cont_diff_pi.mpr (λ j, _)),
    simp only [minor_apply],
    apply times_cont_diff_apply_apply, },
end

end matrix

end smooth_det

section smooth_barycentric

open set function

variables (ι 𝕜 F : Type*)
variables [fintype ι] [decidable_eq ι] [nondiscrete_normed_field 𝕜] [complete_space 𝕜]
variables [normed_group F] [normed_space 𝕜 F]

lemma smooth_barycentric' [finite_dimensional 𝕜 F] (b : affine_basis ι 𝕜 F) (i : ι) :
  times_cont_diff 𝕜 ⊤ (b.coord i) :=
(⟨b.coord i, continuous_barycentric_coord b i⟩ : F →A[𝕜] 𝕜).times_cont_diff

-- Particularly horrendous proof
lemma smooth_barycentric [∀ v, decidable (v ∈ affine_bases ι 𝕜 F)] [finite_dimensional 𝕜 F]
  (h : fintype.card ι = finite_dimensional.finrank 𝕜 F + 1) :
  times_cont_diff_on 𝕜 ⊤ (uncurry (eval_barycentric_coords ι 𝕜 F)) (set.prod univ (affine_bases ι 𝕜 F)) :=
begin
  obtain ⟨b : affine_basis ι 𝕜 F⟩ := affine_basis.exists_affine_basis_of_finite_dimensional h,
  simp_rw [uncurry_def, times_cont_diff_on_pi, eval_barycentric_coords_eq_det 𝕜 b],
  intros i,
  simp only [algebra.id.smul_eq_mul, pi.smul_apply, matrix.cramer_transpose_apply],
  have h_snd : times_cont_diff 𝕜 ⊤ (λ (x : F × (ι → F)), b.to_matrix x.snd),
  { refine times_cont_diff.comp _ times_cont_diff_snd,
    refine times_cont_diff_pi.mpr (λ j, times_cont_diff_pi.mpr (λ j', _)),
    exact (smooth_barycentric' ι 𝕜 F b j').comp (times_cont_diff_apply 𝕜 j), },
  apply times_cont_diff_on.mul,
  { apply ((matrix.smooth_det ι 𝕜 ⊤).comp h_snd).times_cont_diff_on.inv,
    rintros ⟨p, v⟩ h,
    have hv : is_unit (b.to_matrix v), { simpa [mem_affine_bases_iff ι 𝕜 F b v] using h, },
    rw [← is_unit_iff_ne_zero, ← matrix.is_unit_iff_is_unit_det],
    exact hv, },
  { refine ((matrix.smooth_det ι 𝕜 ⊤).comp _).times_cont_diff_on,
    refine times_cont_diff_pi.mpr (λ j, times_cont_diff_pi.mpr (λ j', _)),
    simp only [matrix.update_row_apply, affine_basis.to_matrix_apply, affine_basis.coords_apply],
    by_cases hij : j = i,
    { simp only [hij, if_true, eq_self_iff_true],
      exact (smooth_barycentric' ι 𝕜 F b j').comp times_cont_diff_fst, },
    { simp only [hij, if_false],
      exact (smooth_barycentric' ι 𝕜 F b j').comp (times_cont_diff_pi.mp times_cont_diff_snd j), }, },
end

end smooth_barycentric
