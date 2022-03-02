import topology.separation

open set function

/-
TODO? State a specialized version for quotient maps? Note the open map assumption is still
a separate assumption there.
-/

lemma t2_space_iff_of_continuous_surjective_open
  {α β : Type*} [topological_space α] [topological_space β] {π : α → β}
  (hcont : continuous π) (hsurj : surjective π) (hop : is_open_map π) :
  t2_space β ↔ is_closed {q : α × α | π q.1 = π q.2} :=
begin
  set rel := {q : α × α | π q.1 = π q.2},
  rw t2_iff_is_closed_diagonal,
  split ; intro H,
  { exact H.preimage (hcont.prod_map hcont) },
  { simp_rw ← is_open_compl_iff at H ⊢,
    have key : prod.map π π '' relᶜ = (diagonal β)ᶜ,
    { ext ⟨x, y⟩,
      suffices : (∃ (a b : α), ¬π a = π b ∧ π a = x ∧ π b = y) ↔ (x, y) ∉ diagonal β, by simpa,
      split,
      { rintro ⟨a, b, hab, rfl, rfl⟩,
        exact hab },
      { intro h,
        rcases hsurj x with ⟨e, rfl⟩,
        rcases hsurj y with ⟨f, rfl⟩,
        use [e, f, h, rfl, rfl] } },
    simp_rw ← key,
    exact (hop.prod hop) _ H },
end
