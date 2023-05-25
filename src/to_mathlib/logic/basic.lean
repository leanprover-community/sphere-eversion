import logic.basic

-- `by simp [forall_and]` works in Lean 4
lemma forall₂_and_distrib {α β : Sort*} {p q : α → β → Prop} :
  (∀ x y, p x y ∧ q x y) ↔ (∀ x y, p x y) ∧ ∀ x y, q x y :=
(forall_congr $ λ x : α, @forall_and_distrib _ (p x) (q x)).trans
  forall_and_distrib
