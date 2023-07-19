import Mathlib.Data.Set.Prod

open Set

namespace Set

@[simp]
theorem univ_prod_nonempty_iff {α β : Type _} [Nonempty α] {s : Set β} :
    ((univ : Set α) ×ˢ s).Nonempty ↔ s.Nonempty := by simp [prod_nonempty_iff]

end Set

