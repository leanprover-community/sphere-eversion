import Mathbin.Topology.LocallyFinite

open Function Set

theorem LocallyFinite.smul_left {ι : Type _} {α : Type _} [TopologicalSpace α] {M : Type _}
    {R : Type _} [Semiring R] [AddCommMonoid M] [Module R M] [NoZeroSMulDivisors R M]
    {s : ι → α → R} (h : LocallyFinite fun i => support <| s i) (f : ι → α → M) :
    LocallyFinite fun i => support <| s i • f i :=
  by
  apply h.subset fun i => _
  rw [support_smul]
  exact inter_subset_left _ _

theorem LocallyFinite.smul_right {ι : Type _} {α : Type _} [TopologicalSpace α] {M : Type _}
    {R : Type _} [Semiring R] [AddCommMonoid M] [Module R M] [NoZeroSMulDivisors R M]
    {f : ι → α → M} (h : LocallyFinite fun i => support <| f i) (s : ι → α → R) :
    LocallyFinite fun i => support <| s i • f i :=
  by
  apply h.subset fun i => _
  rw [support_smul]
  exact inter_subset_right _ _

section

variable {ι X : Type _} [TopologicalSpace X]

@[to_additive]
theorem LocallyFinite.exists_finset_mulSupport_eq {M : Type _} [CommMonoid M] {ρ : ι → X → M}
    (hρ : LocallyFinite fun i => mulSupport <| ρ i) (x₀ : X) :
    ∃ I : Finset ι, (mulSupport fun i => ρ i x₀) = I :=
  by
  use (hρ.point_finite x₀).toFinset
  rw [finite.coe_to_finset]
  rfl

end

open scoped Topology

open Filter

theorem LocallyFinite.eventually_subset {ι X : Type _} [TopologicalSpace X] {s : ι → Set X}
    (hs : LocallyFinite s) (hs' : ∀ i, IsClosed (s i)) (x : X) :
    ∀ᶠ y in 𝓝 x, {i | y ∈ s i} ⊆ {i | x ∈ s i} :=
  by
  apply mem_of_superset (hs.Inter_compl_mem_nhds hs' x)
  intro y hy i hi
  simp only [mem_Inter, mem_compl_iff] at hy 
  exact not_imp_not.mp (hy i) hi

