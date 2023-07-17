import Mathbin.LinearAlgebra.FiniteDimensional

open FiniteDimensional Submodule

variable {𝕜 : Type _} [Field 𝕜] {E : Type _} [AddCommGroup E] [Module 𝕜 E] {E' : Type _}
  [AddCommGroup E'] [Module 𝕜 E']

theorem two_le_rank_of_rank_lt_rank [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 E'] {π : E →ₗ[𝕜] 𝕜}
    (hπ : π.ker ≠ ⊤) (h : finrank 𝕜 E < finrank 𝕜 E') (φ : E →ₗ[𝕜] E') :
    2 ≤ Module.rank 𝕜 (E' ⧸ Submodule.map φ π.ker) :=
  by
  suffices 2 ≤ finrank 𝕜 (E' ⧸ π.ker.map φ)
    by
    rw [← finrank_eq_rank]
    exact_mod_cast this
  apply le_of_add_le_add_right
  rw [Submodule.finrank_quotient_add_finrank (π.ker.map φ)]
  have :=
    calc
      finrank 𝕜 (π.ker.map φ) ≤ finrank 𝕜 π.ker := finrank_map_le φ π.ker
      _ < finrank 𝕜 E := Submodule.finrank_lt (le_top.lt_of_ne hπ)
  linarith

