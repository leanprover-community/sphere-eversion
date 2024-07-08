import Mathlib.Tactic.TypeStar

-- `by simp [forall_and]` works in Lean 4
theorem forall₂_and_distrib {α β : Sort*} {p q : α → β → Prop} :
    (∀ x y, p x y ∧ q x y) ↔ (∀ x y, p x y) ∧ ∀ x y, q x y :=
  (forall_congr' fun x : α ↦ @forall_and _ (p x) (q x)).trans forall_and
