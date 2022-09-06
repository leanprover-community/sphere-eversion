import analysis.inner_product_space.orientation

noncomputable theory

open_locale real_inner_product_space big_operators
open finite_dimensional

variables {E : Type*} [inner_product_space ℝ E] [finite_dimensional ℝ E]
  {n : ℕ} [fact (finrank ℝ E = n + 1)] (ω : orientation ℝ E (fin n.succ))

namespace orientation

def volume_form : alternating_map ℝ E ℝ (fin n.succ) :=
(ω.fin_orthonormal_basis n.succ_pos (fact.out _)).det

lemma abs_volume_form_apply_le (v : fin n.succ → E) :
  |ω.volume_form v| ≤ ∏ i : fin n.succ, ∥v i∥ :=
sorry

lemma abs_volume_form_apply_of_pairwise_orthogonal
  {v : fin n.succ → E} (hv : pairwise (λ i j, ⟪v i, v j⟫ = 0)) :
  |ω.volume_form v| = ∏ i : fin n.succ, ∥v i∥ :=
sorry

lemma abs_volume_form_apply_of_orthonormal {v : fin n.succ → E} (hv : orthonormal ℝ v) :
  |ω.volume_form n v| = 1 :=
by simp [ω.abs_volume_form_apply_of_pairwise_orthogonal hn h (λ i j, hv.2), hv.1]

end orientation

attribute [irreducible] orientation.volume_form
