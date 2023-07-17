import Mathlib.Data.Set.Lattice

namespace Set

variable {α β : Type _} {ι : Sort _}

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
-- Put next to Union_prod_const...
theorem const_prod_iUnion {s : ι → Set α} {t : Set β} : (t ×ˢ ⋃ i, s i) = ⋃ i, t ×ˢ s i := by ext;
  simp

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
-- Put next to Union₂_prod_const...
theorem const_prod_Union₂ {κ : ι → Sort _} {s : ∀ i, κ i → Set α} {t : Set β} :
    (t ×ˢ ⋃ (i) (j), s i j) = ⋃ (i) (j), t ×ˢ s i j := by simp_rw [const_prod_Union]

theorem bUnion_le {α ι : Type _} [PartialOrder ι] (s : ι → Set α) (i : ι) :
    (⋃ j ≤ i, s j) = (⋃ j < i, s j) ∪ s i :=
  by
  simp only [(fun j => le_iff_lt_or_eq : ∀ j, j ≤ i ↔ j < i ∨ j = i)]
  erw [bUnion_union, bUnion_singleton]
  rfl

theorem bUnion_ge {α ι : Type _} [PartialOrder ι] (s : ι → Set α) (i : ι) :
    (⋃ j ≥ i, s j) = s i ∪ ⋃ j > i, s j :=
  by
  erw [@bUnion_le α (OrderDual ι) _ s i, union_comm]
  rfl

end Set

