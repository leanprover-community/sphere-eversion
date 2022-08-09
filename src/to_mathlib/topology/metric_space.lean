import topology.metric_space.basic
import topology.metric_space.lipschitz

open metric set
open_locale nnreal

section
variables {α β : Type*} [pseudo_metric_space α] [pseudo_metric_space β]

lemma mem_ball_prod {x x₀ : α × β} {r : ℝ} :
  x ∈ ball x₀ r ↔ x.1 ∈ ball x₀.1 r ∧ x.2 ∈ ball x₀.2 r :=
by simp only [mem_ball, prod.dist_eq, max_lt_iff]

end

section lipschitz

variables {α β γ : Type*} [pseudo_emetric_space α] [pseudo_emetric_space β] [pseudo_emetric_space γ]

-- TODO Drop
protected lemma lipschitz_on_with.comp' {Kf Kg : ℝ≥0} {f : β → γ} {g : α → β} {s : set α} {t : set β}
  (hf : lipschitz_on_with Kf f t) (hg : lipschitz_on_with Kg g s) (hst : g '' s ⊆ t) :
  lipschitz_on_with (Kf * Kg) (f ∘ g) s :=
hf.comp hg $ maps_to'.mpr hst

lemma lipschitz_with_prod_mk_left (a : α) : lipschitz_with 1 (prod.mk a : β → α × β) :=
λ x y, show max _ _ ≤ _, by simp

lemma lipschitz_with_prod_mk_right (b : β) : lipschitz_with 1 (λ a : α, (a, b)) :=
λ x y, show max _ _ ≤ _, by simp

end lipschitz

namespace metric

open_locale topological_space

variables {α : Type*} [pseudo_metric_space α] {x : α} {s : set α}

theorem mem_nhds_iff' : s ∈ 𝓝 x ↔ ∃ε>0, closed_ball x ε ⊆ s :=
nhds_basis_closed_ball.mem_iff

end metric
