import analysis.normed.group.basic
import analysis.normed.normed_field
import topology.metric_space.basic

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

lemma tendsto.of_norm_le {E F : Type*} [metric_space E] [normed_group F]
  {f : E → F} {g : E → ℝ} {x : E}
  (h₀ : tendsto g (𝓝 x) (𝓝 0)) (h₁ : ∀ x, ∥f x∥ ≤ g x) :
  tendsto f (𝓝 x) (𝓝 0) :=
begin
  -- TODO Please golf me!
  rw metric.tendsto_nhds_nhds at h₀ ⊢,
  intros ε hε,
  obtain ⟨δ, hδ₁, hδ₂⟩ := h₀ ε hε,
  refine ⟨δ, hδ₁, λ y hy, _⟩,
  simp * at *,
  specialize h₁ y,
  have hgy : 0 ≤ g y := (norm_nonneg (f y)).trans h₁,
  rw ← real.norm_of_nonneg hgy at h₁,
  exact lt_of_le_of_lt h₁ (hδ₂ hy),
end

end filter
