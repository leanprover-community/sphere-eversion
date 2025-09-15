import Mathlib.Data.Fin.SuccPred

-- not directly used
theorem Fin.coe_succ_le_iff_le {n : ℕ} {j k : Fin n} : j.castSucc ≤ k.castSucc ↔ j ≤ k :=
  castSucc_le_castSucc_iff

-- not directly used
theorem Fin.coe_lt_succ {n : ℕ} (k : Fin n) : k.castSucc < k.succ := by
  rw [castSucc_lt_succ_iff]
  exact Fin.ge_of_eq rfl
