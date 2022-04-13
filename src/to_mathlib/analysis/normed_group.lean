import analysis.normed.group.basic
import analysis.normed.normed_field

lemma norm_sub_le_add {G : Type*} [normed_group G] (a b c : G) : ∥a - b∥ ≤ ∥a - c∥ + ∥c - b∥ :=
by simp [← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm, dist_triangle]

lemma norm_sub_le_add_of_le {G : Type*} [normed_group G] {a b c : G} {d d' : ℝ}
  (h : ∥a - c∥ ≤ d) (h' : ∥c - b∥ ≤ d') : ∥a - b∥ ≤ d + d' :=
(norm_sub_le_add a b c).trans $ add_le_add h h'

-- note: duplicates of `dist_self_add_right` which are currently PR'd to mathlib
@[simp]
lemma dist_add {G : Type*} [semi_normed_group G] (a b : G) : dist a (a+b) = ∥b∥ :=
by simp [dist_eq_norm]

@[simp]
lemma dist_add' {G : Type*} [semi_normed_group G] (a b : G) : dist (a+b) a = ∥b∥ :=
by simp [dist_eq_norm]

namespace filter

open_locale topological_space

lemma tendsto.of_norm_le {E F : Type*} {l : filter E} [normed_group F]
  {f : E → F} {g : E → ℝ} (h₀ : tendsto g l (𝓝 0)) (h₁ : ∀ x, ∥f x∥ ≤ g x) :
  tendsto f l (𝓝 0) :=
begin
  rw normed_group.tendsto_nhds_zero at h₀ ⊢,
  refine λ ε hε, (h₀ ε hε).mono (λ x hx, (h₁ x).trans_lt $ _),
  rw [real.norm_eq_abs] at hx,
  refine (le_abs_self _).trans_lt hx,
end

end filter
