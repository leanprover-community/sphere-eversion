import Mathlib.LinearAlgebra.Basis.Flag
import Mathlib.LinearAlgebra.Dual

noncomputable section

open Set Submodule

section

variable {R : Type*} [Semiring R] {M : Type*} [AddCommMonoid M] [Module R M]

-- not directly used
theorem Fin.coe_succ_le_iff_le {n : ℕ} {j k : Fin n} : (j : Fin <| n + 1) ≤ k ↔ j ≤ k := by
  simp only [Fin.coe_eq_castSucc]; rfl

-- PRed in #11265
theorem Fin.coe_succ_lt_iff_lt {n : ℕ} {j k : Fin n} : (j : Fin <| n + 1) < k ↔ j < k := by
  simp only [Fin.coe_eq_castSucc]; rfl

-- not directly used
theorem Fin.coe_lt_succ {n : ℕ} (k : Fin n) : (k : Fin <| n + 1) < k.succ := by
  rw [Fin.coe_eq_castSucc]
  exact Nat.lt_succ_self _

-- PRed to mathlib in #11264
theorem Basis.flag_span_succ {n : ℕ} (b : Basis (Fin n) R M) (k : Fin n) :
    b.flag k.succ = span R {b k} ⊔ b.flag k := by
  symm
  rw [Basis.flag, ← span_union, ← image_singleton, ← image_union, flag]
  refine congr_arg (span R <| b '' ·) <| Set.ext fun j ↦ ?_
  have : j = k ∨ j < k ↔ ↑j < k.succ := by
    rw [← le_iff_eq_or_lt, Fin.coe_eq_castSucc, Fin.lt_iff_val_lt_val]
    exact Nat.lt_succ_iff.symm
  simp [this]

end

section

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

variable {n : ℕ}

-- PRed in #11265
theorem Basis.flag_le_ker_dual (b : Basis (Fin n) R M) (k : Fin n) :
    b.flag k ≤ LinearMap.ker (b.dualBasis k) := by
  erw [span_le]
  rintro _ ⟨j, hj : j.castSucc < k, rfl⟩
  have : j < k := by rw [← Fin.coe_eq_castSucc, Fin.coe_succ_lt_iff_lt] at hj; exact hj
  simp only [coe_dualBasis, SetLike.mem_coe, LinearMap.mem_ker, coord_apply, repr_self]
  rw [Finsupp.single_apply_eq_zero]
  exact fun h ↦ False.elim (by omega)

end
