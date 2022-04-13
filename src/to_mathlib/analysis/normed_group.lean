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
  -- TODO Please golf me!
  rw tendsto_def at h₀ ⊢,
  intros s hs,
  obtain ⟨ε, hε, hs⟩ := metric.mem_nhds_iff.mp hs,
  filter_upwards [h₀ (metric.ball 0 ε) (metric.ball_mem_nhds 0 hε)],
  intros x hx,
  rw [set.mem_preimage, mem_ball_zero_iff, real.norm_of_nonneg
    ((norm_nonneg (f x)).trans (h₁ x))] at hx,
  exact hs (mem_ball_zero_iff.mpr (lt_of_le_of_lt (h₁ x) hx)),
end

end filter
