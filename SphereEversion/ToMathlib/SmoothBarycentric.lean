import Mathlib.Analysis.Calculus.AddTorsor.Coord
import Mathlib.Analysis.Matrix
import Mathlib.LinearAlgebra.AffineSpace.Matrix

noncomputable section

open Set Function

open scoped Affine Matrix ContDiff

section BarycentricDet

variable (ι R k P : Type*) {M : Type*} [Ring R] [AddCommGroup M] [Module R M] [AffineSpace M P]

/-- The set of affine bases for an affine space. -/
def affineBases : Set (ι → P) :=
  {v | AffineIndependent R v ∧ affineSpan R (range v) = ⊤}

theorem affineBases_findim [Fintype ι] [Field k] [Module k M] [FiniteDimensional k M]
    (h : Fintype.card ι = Module.finrank k M + 1) :
    affineBases ι k P = {v | AffineIndependent k v} := by
  ext v
  simp only [affineBases, mem_setOf_eq, and_iff_left_iff_imp]
  exact fun h_ind ↦ h_ind.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr h

theorem mem_affineBases_iff [Fintype ι] [DecidableEq ι] [Nontrivial R] (b : AffineBasis ι R P)
    (v : ι → P) : v ∈ affineBases ι R P ↔ IsUnit (b.toMatrix v) :=
  (b.isUnit_toMatrix_iff v).symm

/-- If `P` is an affine space over the ring `R`, `v : ι → P` is an affine basis (for some indexing
set `ι`) and `p : P` is a point, then `eval_barycentric_coords ι R P p v` are the barycentric
coordinates of `p` with respect to the affine basis `v`.

Actually for convenience `eval_barycentric_coords` is defined even when `v` is not an affine basis.
In this case its value should be regarded as "junk". -/
def evalBarycentricCoords [DecidablePred (· ∈ affineBases ι R P)] (p : P) (v : ι → P) : ι → R :=
  if h : v ∈ affineBases ι R P then ((AffineBasis.mk v h.1 h.2).coords p : ι → R) else 0

@[simp]
theorem evalBarycentricCoords_apply_of_mem_bases [DecidablePred (· ∈ affineBases ι R P)] (p : P)
    {v : ι → P} (h : v ∈ affineBases ι R P) :
    evalBarycentricCoords ι R P p v = (AffineBasis.mk v h.1 h.2).coords p :=
  dif_pos h

@[simp]
theorem evalBarycentricCoords_apply_of_not_mem_bases [DecidablePred (· ∈ affineBases ι R P)] (p : P)
    {v : ι → P} (h : v ∉ affineBases ι R P) : evalBarycentricCoords ι R P p v = 0 :=
  dif_neg h

variable {ι R P}

theorem evalBarycentricCoords_eq_det [Fintype ι] [DecidableEq ι] (S : Type*) [Field S] [Module S M]
    [∀ v, Decidable (v ∈ affineBases ι S P)] (b : AffineBasis ι S P) (p : P) (v : ι → P) :
    evalBarycentricCoords ι S P p v =
      (b.toMatrix v).det⁻¹ • (b.toMatrix v)ᵀ.cramer (b.coords p) := by
  ext i
  by_cases h : v ∈ affineBases ι S P
  · simp only [evalBarycentricCoords, h, dif_pos, Algebra.id.smul_eq_mul, Pi.smul_apply,
      AffineBasis.coords_apply]
    erw [← b.det_smul_coords_eq_cramer_coords ⟨v, h.1, h.2⟩ p]
    simp only [Pi.smul_apply, AffineBasis.coords_apply, Algebra.id.smul_eq_mul]
    have hu := b.isUnit_toMatrix ⟨v, h.1, h.2⟩
    rw [Matrix.isUnit_iff_isUnit_det] at hu
    erw [← mul_assoc, ← Ring.inverse_eq_inv, Ring.inverse_mul_cancel _ hu, one_mul]
  · simp only [evalBarycentricCoords, h, Algebra.id.smul_eq_mul, Pi.zero_apply, inv_eq_zero,
      dif_neg, not_false_iff, zero_eq_mul, Pi.smul_apply]
    left
    rwa [mem_affineBases_iff ι S P b v, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero,
      Classical.not_not] at h

end BarycentricDet

namespace Matrix

variable (ι k : Type*) [Fintype ι] [DecidableEq ι] [NontriviallyNormedField k]

attribute [instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem smooth_det (m : WithTop ℕ∞) : ContDiff k m (det : Matrix ι ι k → k) := by
  suffices ∀ n : ℕ, ContDiff k m (det : Matrix (Fin n) (Fin n) k → k) by
    have h : (det : Matrix ι ι k → k) = det ∘ reindex (Fintype.equivFin ι) (Fintype.equivFin ι) :=
  by ext; simp
    rw [h]
    apply (this (Fintype.card ι)).comp
    exact contDiff_pi.mpr fun i ↦ contDiff_pi.mpr fun j ↦ contDiff_apply_apply _ _ _ _
  intro n
  induction' n with n ih
  · rw [coe_det_isEmpty]
    exact contDiff_const
  change ContDiff k m fun A : Matrix (Fin n.succ) (Fin n.succ) k ↦ A.det
  simp_rw [det_succ_column_zero]
  apply ContDiff.sum fun l _ ↦ ?_
  apply ContDiff.mul
  · refine contDiff_const.mul ?_
    apply contDiff_apply_apply
  · apply ih.comp
    refine contDiff_pi.mpr fun i ↦ contDiff_pi.mpr fun j ↦ ?_
    simp only [submatrix_apply]
    apply contDiff_apply_apply

end Matrix

section smooth_barycentric

variable (ι 𝕜 F : Type*)

variable [Fintype ι] [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]

variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]

-- An alternative approach would be to prove the affine version of `contDiffAt_map_inverse`
-- and prove that barycentric coordinates give a continuous affine equivalence to
-- `{ f : ι →₀ 𝕜 | f.sum = 1 }`.
-- This should obviate the need for the finite-dimensionality assumption.
theorem smooth_barycentric [DecidablePred (· ∈ affineBases ι 𝕜 F)] [FiniteDimensional 𝕜 F]
    (h : Fintype.card ι = Module.finrank 𝕜 F + 1) {n : WithTop ℕ∞} :
    ContDiffOn 𝕜 n (uncurry (evalBarycentricCoords ι 𝕜 F)) (@univ F ×ˢ affineBases ι 𝕜 F) := by
  classical
  obtain ⟨b⟩ : Nonempty (AffineBasis ι 𝕜 F) := AffineBasis.exists_affineBasis_of_finiteDimensional h
  simp_rw [uncurry_def, contDiffOn_pi, evalBarycentricCoords_eq_det 𝕜 b]
  intro i
  change ContDiffOn 𝕜 n
    (fun x : F × (ι → F)  ↦
      (Matrix.det (AffineBasis.toMatrix b x.snd))⁻¹ •
        (Matrix.cramer (AffineBasis.toMatrix b x.snd)ᵀ : (ι → 𝕜) → ι → 𝕜)
          ((AffineBasis.coords b : F → ι → 𝕜) x.1) i)
    (univ ×ˢ affineBases ι 𝕜 F)
  simp only [Matrix.cramer_transpose_apply]
  have hcont : ContDiff 𝕜 n fun x : ι → F ↦ b.toMatrix x :=
    contDiff_pi.mpr fun j ↦ contDiff_pi.mpr fun j' ↦
      ((smooth_barycentric_coord b j').of_le le_top).comp (contDiff_apply 𝕜 F j)
  have h_snd : ContDiff 𝕜 n fun x : F × (ι → F) ↦ b.toMatrix x.snd := hcont.comp contDiff_snd
  apply ContDiffOn.mul
  · apply ((Matrix.smooth_det ι 𝕜 n).comp h_snd).contDiffOn.inv
    rintro ⟨p, v⟩ hpv
    have hv : IsUnit (b.toMatrix v) := by simpa [mem_affineBases_iff ι 𝕜 F b v] using hpv
    rw [← isUnit_iff_ne_zero, comp_apply, ← Matrix.isUnit_iff_isUnit_det]
    exact hv
  · refine ((Matrix.smooth_det ι 𝕜 n).comp ?_).contDiffOn
    refine contDiff_pi.mpr fun j ↦ contDiff_pi.mpr fun j' ↦ ?_
    simp only [Matrix.updateRow_apply]
    simp only [AffineBasis.toMatrix_apply, AffineBasis.coords_apply]
    by_cases hij : j = i
    · simp only [hij, if_true]
      exact (smooth_barycentric_coord b j').fst'.of_le le_top
    · simp only [hij, if_false]
      exact ((smooth_barycentric_coord b j').of_le le_top).comp (contDiff_pi.mp contDiff_snd j)

end smooth_barycentric
