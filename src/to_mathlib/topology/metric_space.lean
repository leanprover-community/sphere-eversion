import topology.metric_space.basic
import topology.metric_space.lipschitz

open metric set
open_locale nnreal

section lipschitz

variables {α β γ : Type*} [pseudo_emetric_space α] [pseudo_emetric_space β] [pseudo_emetric_space γ]

lemma lipschitz_with_prod_mk_left (a : α) : lipschitz_with 1 (prod.mk a : β → α × β) :=
λ x y, show max _ _ ≤ _, by simp

-- todo: remove and replace with lipschitz_with.prod_mk_right after a typo has been fixed
lemma lipschitz_with_prod_mk_right (b : β) : lipschitz_with 1 (λ a : α, (a, b)) :=
λ x y, show max _ _ ≤ _, by simp

end lipschitz
