import Mathlib.LinearAlgebra.Basis
import Mathlib.LinearAlgebra.Dual
import Mathlib.Tactic.Monotonicity

noncomputable section

universe u

open Function Set Submodule

open scoped Classical BigOperators

section

variable {R : Type _} [Semiring R] {M : Type _} [AddCommMonoid M] [Module R M]

/-- The span of the first `n` elements of an ordered basis. -/
def Basis.flag {n : ℕ} (b : Basis (Fin n) R M) : Fin (n + 1) → Submodule R M := fun k =>
  span R (b '' {j | (j : Fin (n + 1)) < k})

@[simp]
theorem Basis.flag_zero {n : ℕ} (b : Basis (Fin n) R M) : b.flag 0 = ⊥ := by
  simp only [Basis.flag, Fin.coe_eq_castSucc]
  suffices {j : Fin n | Fin.castSuccEmb j < 0} = ∅ by simp [this]
  ext l
  simp [l.castSucc.zero_le]

@[simp]
theorem Basis.flag_last {n : ℕ} (b : Basis (Fin n) R M) : b.flag (Fin.last n) = ⊤ := by
  have : {j : Fin n | (j : Fin <| n + 1) < Fin.last n} = univ
  · ext l
    simp [Fin.castSucc_lt_last l]
  simp_rw [Basis.flag, this]
  simp [b.span_eq]

attribute [mono] Submodule.span_mono

@[simp]
theorem Basis.flag_mono {n : ℕ} (b : Basis (Fin n) R M) : Monotone b.flag := fun j k h ↦ by
  dsimp [Basis.flag]
  mono*
  rintro l (hl : ↑↑l < j)
  exact hl.trans_le h

theorem Fin.coe_succ_le_iff_le {n : ℕ} {j k : Fin n} : (j : Fin <| n + 1) ≤ k ↔ j ≤ k := by
  simp only [Fin.coe_eq_castSucc]; rfl

theorem Fin.coe_succ_lt_iff_lt {n : ℕ} {j k : Fin n} : (j : Fin <| n + 1) < k ↔ j < k := by
  simp only [Fin.coe_eq_castSucc]; rfl

theorem Fin.coe_lt_succ {n : ℕ} (k : Fin n) : (k : Fin <| n + 1) < k.succ := by
  rw [Fin.coe_eq_castSucc]
  exact Nat.lt_succ_self _

theorem Basis.flag_span_succ {n : ℕ} (b : Basis (Fin n) R M) (k : Fin n) :
    b.flag k ⊔ span R {b k} = b.flag k.succ := by
  rw [Basis.flag, ← span_union, ← image_singleton, ← image_union, flag]
  refine congr_arg (span R <| b '' ·) <| Set.ext fun j ↦ ?_
  have : j = k ∨ j < k ↔ ↑j < k.succ := by
    rw [← le_iff_eq_or_lt, Fin.coe_eq_castSucc, Fin.lt_iff_val_lt_val]
    exact Nat.lt_succ_iff.symm
  simp [this]

end

section

variable {R : Type _} [CommRing R] {M : Type _} [AddCommGroup M] [Module R M]

variable {n : ℕ} (b : Basis (Fin n) R M)

theorem Basis.flag_le_ker_dual (k : Fin n) : b.flag k ≤ LinearMap.ker (b.dualBasis k) := by
  erw [span_le]
  rintro _ ⟨j, hj : (j : Fin <| n + 1) < k, rfl⟩
  simp [(Fin.coe_succ_lt_iff_lt.mp hj).ne]

end

