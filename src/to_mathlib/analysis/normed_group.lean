import analysis.normed.group.basic

lemma norm_sub_le_add {G : Type*} [normed_group G] (a b c : G) : ∥a - b∥ ≤ ∥a - c∥ + ∥c - b∥ :=
by simp [← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm, dist_triangle]

lemma norm_sub_le_add_of_le {G : Type*} [normed_group G] {a b c : G} {d d' : ℝ}
  (h : ∥a - c∥ ≤ d) (h' : ∥c - b∥ ≤ d') : ∥a - b∥ ≤ d + d' :=
(norm_sub_le_add a b c).trans $ add_le_add h h'

namespace filter

open_locale topological_space

lemma tendsto.of_norm_le {α G : Type*} {l : filter α} [normed_group G]
  {f : α → G} {g : α → ℝ} (h₀ : tendsto g l (𝓝 0)) (h₁ : ∀ x, ∥f x∥ ≤ g x) :
  tendsto f l (𝓝 0) :=
begin
  rw normed_group.tendsto_nhds_zero at h₀ ⊢,
  exact λ ε hε, (h₀ ε hε).mono (λ x hx, (h₁ x).trans_lt $ (le_abs_self _).trans_lt hx),
end

end filter
