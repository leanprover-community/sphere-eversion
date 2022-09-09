import analysis.inner_product_space.pi_L2

variables {𝕜 : Type*} [is_R_or_C 𝕜] {E : Type*} [inner_product_space 𝕜 E]

open finite_dimensional

lemma orthonormal.exists_orthonormal_basis_extension_of_card_eq
  {ι : Type*} [fintype ι] (h : finrank 𝕜 E = fintype.card ι) {v : ι → E} {s : set ι}
  (hv : orthonormal 𝕜 (λ i : s, v i)) :
  ∃ b : orthonormal_basis ι 𝕜 E, ∀ i ∈ s, b i = v i :=
sorry
