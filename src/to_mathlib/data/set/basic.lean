import data.set.basic

namespace set

-- Should this be some sort of `set.comap` result?
-- This is just `equiv.set.sep.symm`
def subsubset_equiv_inter {α : Type*} (s : set α) (P : α → Prop) :
  {x : s | P ↑x} ≃ ↥(s ∩ {x : α | P x}) :=
{ to_fun := λ x, ⟨x, mem_inter x.1.2 x.2⟩,
  inv_fun := λ x, ⟨⟨x.1, ((mem_inter_iff x _ _).mp x.2).1⟩, ((mem_inter_iff x _ _).mp x.2).2⟩,
  left_inv := by { rintros ⟨⟨x, hx₁⟩, hx₂⟩, refl, },
  right_inv := by { rintros ⟨x, hx₁, hx₂⟩, refl, }, }

end set
