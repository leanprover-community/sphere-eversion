import Mathlib.Data.Set.Prod

open Set

namespace Set

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem univ_prod_inter_univ_prod {α β : Type _} {s t : Set β} :
    (univ : Set α) ×ˢ s ∩ (univ : Set α) ×ˢ t = (univ : Set α) ×ˢ (s ∩ t) :=
  by
  ext ⟨a, b⟩
  simp

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem univ_prod_nonempty_iff {α β : Type _} [Nonempty α] {s : Set β} :
    ((univ : Set α) ×ˢ s).Nonempty ↔ s.Nonempty := by simp [prod_nonempty_iff]

end Set

