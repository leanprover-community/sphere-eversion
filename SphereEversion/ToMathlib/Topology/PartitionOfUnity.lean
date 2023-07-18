import Mathlib.Topology.PartitionOfUnity

noncomputable section

open scoped Topology Filter BigOperators

open Set Function Filter

section

variable {ι X : Type _} [TopologicalSpace X]

theorem PartitionOfUnity.exists_finset_nhd' {s : Set X} (ρ : PartitionOfUnity ι X s) (x₀ : X) :
    ∃ I : Finset ι, (∀ᶠ x in 𝓝[s] x₀, ∑ i in I, ρ i x = 1) ∧
      ∀ᶠ x in 𝓝 x₀, support (ρ · x) ⊆ I := by
  rcases ρ.locallyFinite.exists_finset_support x₀ with ⟨I, hI⟩
  refine' ⟨I, _, hI⟩
  refine' eventually_nhdsWithin_iff.mpr (hI.mono fun x hx x_in => _)
  have : ∑ᶠ i : ι, ρ i x = ∑ i : ι in I, ρ i x := finsum_eq_sum_of_support_subset _ hx
  rwa [eq_comm, ρ.sum_eq_one x_in] at this

theorem PartitionOfUnity.exists_finset_nhd (ρ : PartitionOfUnity ι X univ) (x₀ : X) :
    ∃ I : Finset ι, ∀ᶠ x in 𝓝 x₀, ∑ i in I, ρ i x = 1 ∧ support (ρ · x) ⊆ I := by
  rcases ρ.exists_finset_nhd' x₀ with ⟨I, H⟩
  use I
  rwa [nhdsWithin_univ, ← eventually_and] at H

/-- The support of a partition of unity at a point as a `finset`. -/
def PartitionOfUnity.finsupport {s : Set X} (ρ : PartitionOfUnity ι X s) (x₀ : X) : Finset ι :=
  (ρ.locallyFinite.point_finite x₀).toFinset

@[simp]
theorem PartitionOfUnity.coe_finsupport {s : Set X} (ρ : PartitionOfUnity ι X s) (x₀ : X) :
    (ρ.finsupport x₀ : Set ι) = support fun i => ρ i x₀ := by
  dsimp only [PartitionOfUnity.finsupport]
  rw [Finite.coe_toFinset]
  rfl

@[simp]
theorem PartitionOfUnity.mem_finsupport {s : Set X} (ρ : PartitionOfUnity ι X s) (x₀ : X) {i} :
    i ∈ ρ.finsupport x₀ ↔ i ∈ support fun i => ρ i x₀ := by
  simp only [PartitionOfUnity.finsupport, mem_support, Finite.mem_toFinset, mem_setOf_eq]

theorem PartitionOfUnity.sum_finsupport {s : Set X} (ρ : PartitionOfUnity ι X s) {x₀ : X}
    (hx₀ : x₀ ∈ s := by trivial) :
    ∑ i in ρ.finsupport x₀, ρ i x₀ = 1 := by
  have := ρ.sum_eq_one hx₀
  rwa [finsum_eq_sum_of_support_subset] at this
  rw [ρ.coe_finsupport]

theorem PartitionOfUnity.sum_finsupport' {s : Set X} (ρ : PartitionOfUnity ι X s) {x₀ : X}
    (hx₀ : x₀ ∈ s := by trivial) {I : Finset ι} (hI : ρ.finsupport x₀ ⊆ I) :
    ∑ i in I, ρ i x₀ = 1 := by
  classical
  rw [← Finset.sum_sdiff hI, ρ.sum_finsupport hx₀]
  suffices ∑ i in I \ ρ.finsupport x₀, ρ i x₀ = 0 by rw [this, zero_add]
  suffices : ∑ i in I \ ρ.finsupport x₀, (ρ i) x₀ = ∑ i in I \ ρ.finsupport x₀, 0
  rw [this, Finset.sum_const_zero]
  apply Finset.sum_congr rfl
  rintro x hx
  simp only [Finset.mem_sdiff, ρ.mem_finsupport, mem_support, Classical.not_not] at hx
  exact hx.2

theorem PartitionOfUnity.sum_finsupport_smul {s : Set X} (ρ : PartitionOfUnity ι X s) {x₀ : X}
    {M : Type _} [AddCommGroup M] [Module ℝ M] (φ : ι → X → M) :
    ∑ i in ρ.finsupport x₀, ρ i x₀ • φ i x₀ = ∑ᶠ i, ρ i x₀ • φ i x₀ := by
  apply (finsum_eq_sum_of_support_subset _ _).symm
  erw [ρ.coe_finsupport x₀, support_smul]
  exact inter_subset_left _ _

end

