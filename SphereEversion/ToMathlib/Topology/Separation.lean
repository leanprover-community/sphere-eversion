import Mathlib.Topology.Separation

open Set Function

/-
TODO? State a specialized version for quotient maps? Note the open map assumption is still
a separate assumption there.
-/
theorem t2Space_iff_of_continuous_surjective_open {α β : Type _} [TopologicalSpace α]
    [TopologicalSpace β] {π : α → β} (hcont : Continuous π) (hsurj : Surjective π)
    (hop : IsOpenMap π) : T2Space β ↔ IsClosed {q : α × α | π q.1 = π q.2} :=
  by
  set rel := {q : α × α | π q.1 = π q.2}
  rw [t2_iff_isClosed_diagonal]
  constructor <;> intro H
  · exact H.preimage (hcont.prod_map hcont)
  · simp_rw [← isOpen_compl_iff] at H ⊢
    have key : Prod.map π π '' Relᶜ = diagonal βᶜ :=
      by
      ext ⟨x, y⟩
      suffices (∃ a b : α, ¬π a = π b ∧ π a = x ∧ π b = y) ↔ (x, y) ∉ diagonal β by simpa
      constructor
      · rintro ⟨a, b, hab, rfl, rfl⟩
        exact hab
      · intro h
        rcases hsurj x with ⟨e, rfl⟩
        rcases hsurj y with ⟨f, rfl⟩
        use e, f, h, rfl, rfl
    simp_rw [← key]
    exact (hop.prod hop) _ H

