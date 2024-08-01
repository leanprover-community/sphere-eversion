import Mathlib.Data.Fin.Basic

-- not directly used
theorem Fin.coe_succ_le_iff_le {n : ℕ} {j k : Fin n} : (j : Fin <| n + 1) ≤ k ↔ j ≤ k := by
  simp only [Fin.coe_eq_castSucc]; rfl

-- not directly used
theorem Fin.coe_lt_succ {n : ℕ} (k : Fin n) : (k : Fin <| n + 1) < k.succ := by
  rw [Fin.coe_eq_castSucc]
  exact Nat.lt_succ_self _
