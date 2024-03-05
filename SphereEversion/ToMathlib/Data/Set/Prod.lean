import Mathlib.Data.Set.Prod

open Set

namespace Set

theorem univ_prod_nonempty_iff {α β : Type _} [Nonempty α] {s : Set β} :
    ((univ : Set α) ×ˢ s).Nonempty ↔ s.Nonempty := by simp

end Set
