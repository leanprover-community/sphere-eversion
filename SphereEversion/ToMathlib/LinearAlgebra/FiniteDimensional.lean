import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

open Module Submodule

variable {𝕜 : Type*} [Field 𝕜] {E : Type*} [AddCommGroup E] [Module 𝕜 E] {E' : Type*}
  [AddCommGroup E'] [Module 𝕜 E']

theorem one_lt_rank_of_rank_lt_rank [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 E'] {π : E →ₗ[𝕜] 𝕜}
    (hπ : LinearMap.ker π ≠ ⊤) (h : finrank 𝕜 E < finrank 𝕜 E') (φ : E →ₗ[𝕜] E') :
    1 < Module.rank 𝕜 (E' ⧸ Submodule.map φ (LinearMap.ker π)) := by
  suffices 2 ≤ finrank 𝕜 (E' ⧸ (LinearMap.ker π).map φ) by
    rw [← finrank_eq_rank]
    exact_mod_cast this
  apply le_of_add_le_add_right
  rw [Submodule.finrank_quotient_add_finrank ((LinearMap.ker π).map φ)]
  have := calc finrank 𝕜 ((LinearMap.ker π).map φ)
      _ ≤ finrank 𝕜 (LinearMap.ker π) := finrank_map_le φ (LinearMap.ker π)
      _ < finrank 𝕜 E := Submodule.finrank_lt hπ
  linarith
