import topology.support

noncomputable theory


open set function

section

lemma tsupport_smul_left
  {α : Type*} [topological_space α] {M : Type*} {R : Type*} [semiring R] [add_comm_monoid M]
  [module R M] [no_zero_smul_divisors R M] (f : α → R) (g : α → M) :
  tsupport (f • g) ⊆ tsupport f :=
begin
  apply closure_mono,
  erw support_smul,
  exact inter_subset_left _ _
end

lemma tsupport_smul_right
   {α : Type*} [topological_space α] {M : Type*} {R : Type*} [semiring R] [add_comm_monoid M]
  [module R M] [no_zero_smul_divisors R M] (f : α → R) (g : α → M) :
    tsupport (f • g) ⊆ tsupport g :=
begin
  apply closure_mono,
  erw support_smul,
  exact inter_subset_right _ _
end

end

section
variables {ι X : Type*} [topological_space X]

@[to_additive]
lemma locally_finite_mul_support_iff {M : Type*} [comm_monoid M] {f : ι → X → M} :
locally_finite (λi, mul_support $ f i) ↔ locally_finite (λ i, mul_tsupport $ f i) :=
⟨locally_finite.closure, λ H, H.subset $ λ i, subset_closure⟩
end
