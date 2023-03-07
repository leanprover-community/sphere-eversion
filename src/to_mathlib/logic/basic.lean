import logic.basic

lemma forall₂_and_distrib {α β : Sort*} {p q : α → β → Prop} :
  (∀ x y, p x y ∧ q x y) ↔ (∀ x y, p x y) ∧ ∀ x y, q x y :=
begin
  split ; intros h,
  split ; intros,
  exact (h x y).1,
  exact (h x y).2,
  intros x y,
   exact ⟨h.1 x y, h.2 x y⟩
end
