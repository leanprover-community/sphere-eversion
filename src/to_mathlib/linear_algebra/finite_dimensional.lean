import linear_algebra.finite_dimensional

open finite_dimensional

variables {𝕜 : Type*} [field 𝕜]
          {E : Type*} [add_comm_group E] [module 𝕜 E]
          {E' : Type*} [add_comm_group E'] [module 𝕜 E']

lemma two_le_rank_of_rank_lt_rank [finite_dimensional 𝕜 E] [finite_dimensional 𝕜 E']
  {π : E →ₗ[𝕜] 𝕜} (hπ : π.ker ≠ ⊤) (h : finrank 𝕜 E < finrank 𝕜 E') (φ : E →ₗ[𝕜] E') :
  2 ≤ module.rank 𝕜 (E' ⧸ submodule.map φ π.ker) :=
begin
  suffices : 2 ≤ finrank 𝕜 (E' ⧸ π.ker.map φ),
  { rw ← finrank_eq_dim,
    exact_mod_cast this },
  apply le_of_add_le_add_right,
  rw submodule.finrank_quotient_add_finrank (π.ker.map φ),
  have := calc finrank 𝕜 (π.ker.map φ)
        ≤ finrank 𝕜 π.ker : finrank_map_le 𝕜 φ π.ker
    ...  < finrank 𝕜 E : submodule.finrank_lt (le_top.lt_of_ne hπ),
  linarith,
end
