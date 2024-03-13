import Mathlib.Data.Set.Lattice

namespace Set

variable {α β : Type*} {ι : Sort*}

-- Put next to Union_prod_const...
theorem const_prod_iUnion {s : ι → Set α} {t : Set β} : (t ×ˢ ⋃ i, s i) = ⋃ i, t ×ˢ s i := by
  ext; simp

-- Put next to Union₂_prod_const...
theorem const_prod_iUnion₂ {κ : ι → Sort _} {s : ∀ i, κ i → Set α} {t : Set β} :
    (t ×ˢ ⋃ (i) (j), s i j) = ⋃ (i) (j), t ×ˢ s i j := by simp_rw [const_prod_iUnion]

-- the next 2 lemmas should be generalized from `Set α` to a `CompleteLattice`
-- before moving to Mathlib.
theorem bUnion_le {α ι : Type*} [PartialOrder ι] (s : ι → Set α) (i : ι) :
    (⋃ j ≤ i, s j) = (⋃ j < i, s j) ∪ s i := by
  simp only [le_iff_lt_or_eq]
  erw [biUnion_union, biUnion_singleton]
  rfl

theorem bUnion_ge {α ι : Type*} [PartialOrder ι] (s : ι → Set α) (i : ι) :
    (⋃ j ≥ i, s j) = s i ∪ ⋃ j > i, s j := by
  erw [@bUnion_le α (OrderDual ι) _ s i, union_comm]
  rfl

end Set
