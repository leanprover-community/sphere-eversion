import topology.metric_space.basic
import topology.metric_space.lipschitz

open metric set
open_locale nnreal

section
variables {α β : Type*} [pseudo_metric_space α] [pseudo_metric_space β]

lemma mem_ball_prod {x x₀ : α × β} {r : ℝ} :
  x ∈ ball x₀ r ↔ x.1 ∈ ball x₀.1 r ∧ x.2 ∈ ball x₀.2 r :=
by { cases x₀, simp [← ball_prod_same] }
end

section lipschitz

variables {α β γ : Type*} [pseudo_emetric_space α] [pseudo_emetric_space β] [pseudo_emetric_space γ]

protected lemma lipschitz_on_with.comp {Kf Kg : ℝ≥0} {f : β → γ} {g : α → β} {s : set α} {t : set β}
  (hf : lipschitz_on_with Kf f t) (hg : lipschitz_on_with Kg g s) (hst : g '' s ⊆ t) :
  lipschitz_on_with (Kf * Kg) (f ∘ g) s :=
assume x x_in y y_in,
calc edist (f (g x)) (f (g y))
    ≤ Kf * edist (g x) (g y) : hf (hst $ mem_image_of_mem g x_in) (hst $ mem_image_of_mem g y_in)
... ≤ Kf * (Kg * edist x y) : ennreal.mul_left_mono (hg x_in y_in)
... = (Kf * Kg : ℝ≥0) * edist x y : by rw [← mul_assoc, ennreal.coe_mul]

lemma lipschitz_with_prod_mk_left (a : α) : lipschitz_with 1 (prod.mk a : β → α × β) :=
λ x y, show max _ _ ≤ _, by simp

lemma lipschitz_with_prod_mk_right (b : β) : lipschitz_with 1 (λ a : α, (a, b)) :=
λ x y, show max _ _ ≤ _, by simp

end lipschitz