import data.set.basic

namespace set

lemma sep_eq_inter_set_of {α : Type*} (s : set α) (P : α → Prop) :
  {x ∈ s | P x} = s ∩ {x | P x} :=
rfl

end set
