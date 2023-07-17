import Mathlib.Data.Set.Basic

namespace Set

theorem sep_eq_inter_setOf {α : Type _} (s : Set α) (P : α → Prop) :
    {x ∈ s | P x} = s ∩ {x | P x} :=
  rfl

end Set

