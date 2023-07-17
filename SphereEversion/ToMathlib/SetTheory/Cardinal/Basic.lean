import Mathbin.SetTheory.Cardinal.Basic

open Cardinal

open scoped Cardinal

theorem Set.countable_infinite_iff_nonempty_denumerable {α : Type _} {s : Set α} :
    s.Countable ∧ s.Infinite ↔ Nonempty (Denumerable s) :=
  by
  rw [denumerable_iff, ← Set.infinite_coe_iff, infinite_iff, ← le_aleph_0_iff_set_countable]
  exact ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨by rw [h], by rw [h]⟩⟩

