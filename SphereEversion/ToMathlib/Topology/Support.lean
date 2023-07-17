import Mathlib.Topology.Support

noncomputable section

open Set Function

section

theorem tsupport_smul_left {α : Type _} [TopologicalSpace α] {M : Type _} {R : Type _} [Semiring R]
    [AddCommMonoid M] [Module R M] [NoZeroSMulDivisors R M] (f : α → R) (g : α → M) :
    tsupport (f • g) ⊆ tsupport f := by
  apply closure_mono
  erw [support_smul]
  exact inter_subset_left _ _

theorem tsupport_smul_right {α : Type _} [TopologicalSpace α] {M : Type _} {R : Type _} [Semiring R]
    [AddCommMonoid M] [Module R M] [NoZeroSMulDivisors R M] (f : α → R) (g : α → M) :
    tsupport (f • g) ⊆ tsupport g := by
  apply closure_mono
  erw [support_smul]
  exact inter_subset_right _ _

end

section

variable {ι X : Type _} [TopologicalSpace X]

@[to_additive]
theorem locallyFinite_mulSupport_iff {M : Type _} [CommMonoid M] {f : ι → X → M} :
    (LocallyFinite fun i => mulSupport <| f i) ↔ LocallyFinite fun i => mulTSupport <| f i :=
  ⟨LocallyFinite.closure, fun H => H.Subset fun i => subset_closure⟩

end

