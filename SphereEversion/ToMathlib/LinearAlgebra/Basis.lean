import Mathlib.LinearAlgebra.Basis.Flag
import Mathlib.LinearAlgebra.Dual

noncomputable section

open Set Submodule

section

variable {R : Type*} [Semiring R] {M : Type*} [AddCommMonoid M] [Module R M]

-- not directly used
theorem Fin.coe_succ_le_iff_le {n : ℕ} {j k : Fin n} : (j : Fin <| n + 1) ≤ k ↔ j ≤ k := by
  simp only [Fin.coe_eq_castSucc]; rfl

-- not directly used
theorem Fin.coe_lt_succ {n : ℕ} (k : Fin n) : (k : Fin <| n + 1) < k.succ := by
  rw [Fin.coe_eq_castSucc]
  exact Nat.lt_succ_self _

-- not used any more: now identical to Basis.flag_succ
theorem Basis.flag_span_succ {n : ℕ} (b : Basis (Fin n) R M) (k : Fin n) :
    b.flag k.succ = span R {b k} ⊔ b.flag k.castSucc := by
  symm
  rw [Basis.flag, ← span_union, ← image_singleton, ← image_union, flag]
  refine congr_arg (span R <| b '' ·) <| Set.ext fun j ↦ ?_
  have : j = k ∨ j < k ↔ ↑j < k.succ := by
    rw [← le_iff_eq_or_lt, Fin.coe_eq_castSucc, Fin.lt_iff_val_lt_val]
    exact Nat.lt_succ_iff.symm
  simp [this]

end
