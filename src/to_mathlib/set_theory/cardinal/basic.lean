import set_theory.cardinal.basic

open cardinal
open_locale cardinal

lemma set.countable_infinite_iff_nonempty_denumerable {α : Type*} {s : set α} :
  s.countable ∧ s.infinite ↔ nonempty (denumerable s) :=
begin
  rw [denumerable_iff, ← set.infinite_coe_iff, infinite_iff, ← mk_set_le_aleph_0],
  exact ⟨λ h, le_antisymm h.1 h.2, λ h, ⟨by rw h, by rw h⟩⟩,
end
