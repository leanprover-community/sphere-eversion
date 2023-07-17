import Mathbin.Topology.PartitionOfUnity

noncomputable section

open scoped Topology Filter BigOperators

open Set Function Filter

section

variable {ι X : Type _} [TopologicalSpace X]

theorem PartitionOfUnity.exists_finset_nhd' {s : Set X} (ρ : PartitionOfUnity ι X s) (x₀ : X) :
    ∃ I : Finset ι,
      (∀ᶠ x in 𝓝[s] x₀, ∑ i in I, ρ i x = 1) ∧ ∀ᶠ x in 𝓝 x₀, (support fun i => ρ i x) ⊆ I :=
  by
  rcases ρ.locally_finite.exists_finset_support x₀ with ⟨I, hI⟩
  refine' ⟨I, _, hI⟩
  refine' eventually_nhds_within_iff.mpr (hI.mono fun x hx x_in => _)
  have : ∑ᶠ i : ι, ρ i x = ∑ i : ι in I, ρ i x := finsum_eq_sum_of_support_subset _ hx
  rwa [eq_comm, ρ.sum_eq_one x_in] at this 

theorem PartitionOfUnity.exists_finset_nhd (ρ : PartitionOfUnity ι X univ) (x₀ : X) :
    ∃ I : Finset ι, ∀ᶠ x in 𝓝 x₀, ∑ i in I, ρ i x = 1 ∧ (support fun i => ρ i x) ⊆ I :=
  by
  rcases ρ.exists_finset_nhd' x₀ with ⟨I, H⟩
  use I
  rwa [nhdsWithin_univ, ← eventually_and] at H 

/-- The support of a partition of unity at a point as a `finset`. -/
def PartitionOfUnity.finsupport {s : Set X} (ρ : PartitionOfUnity ι X s) (x₀ : X) : Finset ι :=
  (ρ.LocallyFinite.point_finite x₀).toFinset

@[simp]
theorem PartitionOfUnity.coe_finsupport {s : Set X} (ρ : PartitionOfUnity ι X s) (x₀ : X) :
    (ρ.finsupport x₀ : Set ι) = support fun i => ρ i x₀ :=
  by
  dsimp only [PartitionOfUnity.finsupport]
  rw [finite.coe_to_finset]
  rfl

@[simp]
theorem PartitionOfUnity.mem_finsupport {s : Set X} (ρ : PartitionOfUnity ι X s) (x₀ : X) {i} :
    i ∈ ρ.finsupport x₀ ↔ i ∈ support fun i => ρ i x₀ := by
  simp only [PartitionOfUnity.finsupport, mem_support, finite.mem_to_finset, mem_set_of_eq]

/- ./././Mathport/Syntax/Translate/Expr.lean:336:4: warning: unsupported (TODO): `[tacs] -/
/-- Try to prove something is in a set by applying `set.mem_univ`. -/
unsafe def tactic.mem_univ : tactic Unit :=
  sorry

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic tactic.mem_univ -/
theorem PartitionOfUnity.sum_finsupport {s : Set X} (ρ : PartitionOfUnity ι X s) {x₀ : X}
    (hx₀ : x₀ ∈ s := by
      run_tac
        tactic.mem_univ) :
    ∑ i in ρ.finsupport x₀, ρ i x₀ = 1 :=
  by
  have := ρ.sum_eq_one hx₀
  rwa [finsum_eq_sum_of_support_subset] at this 
  rw [ρ.coe_finsupport]
  exact subset.rfl

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic tactic.mem_univ -/
theorem PartitionOfUnity.sum_finsupport' {s : Set X} (ρ : PartitionOfUnity ι X s) {x₀ : X}
    (hx₀ : x₀ ∈ s := by
      run_tac
        tactic.mem_univ)
    {I : Finset ι} (hI : ρ.finsupport x₀ ⊆ I) : ∑ i in I, ρ i x₀ = 1 := by
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
    ∑ i in ρ.finsupport x₀, ρ i x₀ • φ i x₀ = ∑ᶠ i, ρ i x₀ • φ i x₀ :=
  by
  apply (finsum_eq_sum_of_support_subset _ _).symm
  erw [ρ.coe_finsupport x₀, support_smul]
  exact inter_subset_left _ _

end

