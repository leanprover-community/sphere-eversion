import order.hom.basic

namespace strict_mono

variables {α β : Type*} [linear_order α] [preorder β]
variables (f : α → β) (hf₁ : strict_mono f) (hf₂ : function.surjective f)

@[simp] lemma coe_order_iso_of_surjective :
  (order_iso_of_surjective f hf₁ hf₂ : α → β) = f :=
rfl

@[simp] lemma order_iso_of_surjective_symm_apply_self (a : α) :
  (order_iso_of_surjective f hf₁ hf₂).symm (f a) = a :=
by rw [← (strict_mono.order_iso_of_surjective f hf₁ hf₂).to_equiv.apply_eq_iff_eq,
  rel_iso.coe_fn_to_equiv, order_iso.apply_symm_apply, coe_order_iso_of_surjective]

@[simp] lemma order_iso_of_surjective_self_symm_apply (b : β) :
  f ((order_iso_of_surjective f hf₁ hf₂).symm b) = b :=
begin
  obtain ⟨a, rfl⟩ := hf₂ b,
  simp,
end

end strict_mono
