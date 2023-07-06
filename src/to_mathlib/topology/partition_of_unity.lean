import topology.partition_of_unity

noncomputable theory

open_locale topological_space filter  big_operators
open set function filter

section
variables {ι X : Type*} [topological_space X]

lemma partition_of_unity.exists_finset_nhd' {s : set X} (ρ : partition_of_unity ι X s) (x₀ : X) :
  ∃ I : finset ι, (∀ᶠ x in 𝓝[s] x₀, ∑ i in I, ρ i x = 1) ∧ ∀ᶠ x in 𝓝 x₀, support (λ i, ρ i x) ⊆ I  :=
begin
  rcases ρ.locally_finite.exists_finset_support x₀ with ⟨I, hI⟩,
  refine ⟨I, _, hI⟩,
  refine eventually_nhds_within_iff.mpr (hI.mono $ λ x hx x_in, _),
  have : ∑ᶠ (i : ι), ρ i x = ∑ (i : ι) in I, ρ i x := finsum_eq_sum_of_support_subset _ hx,
  rwa [eq_comm, ρ.sum_eq_one x_in] at this
end

lemma partition_of_unity.exists_finset_nhd (ρ : partition_of_unity ι X univ) (x₀ : X) :
  ∃ I : finset ι, ∀ᶠ x in 𝓝 x₀, ∑ i in I, ρ i x = 1 ∧ support (λ i, ρ i x) ⊆ I  :=
begin
  rcases ρ.exists_finset_nhd' x₀ with ⟨I, H⟩,
  use I,
  rwa [nhds_within_univ , ← eventually_and] at H
end

/-- The support of a partition of unity at a point as a `finset`. -/
def partition_of_unity.finsupport {s : set X} (ρ : partition_of_unity ι X s) (x₀ : X) : finset ι :=
(ρ.locally_finite.point_finite x₀).to_finset

@[simp] lemma partition_of_unity.coe_finsupport {s : set X} (ρ : partition_of_unity ι X s) (x₀ : X) :
(ρ.finsupport x₀ : set ι) = support (λ i, ρ i x₀) :=
begin
  dsimp only [partition_of_unity.finsupport],
  rw finite.coe_to_finset,
  refl
end

@[simp] lemma partition_of_unity.mem_finsupport {s : set X} (ρ : partition_of_unity ι X s)
  (x₀ : X) {i} : i ∈ ρ.finsupport x₀ ↔ i ∈ support (λ i, ρ i x₀) :=
by simp only [partition_of_unity.finsupport, mem_support, finite.mem_to_finset, mem_set_of_eq]

/-- Try to prove something is in a set by applying `set.mem_univ`. -/
meta def tactic.mem_univ : tactic unit := `[apply set.mem_univ]

lemma partition_of_unity.sum_finsupport {s : set X} (ρ : partition_of_unity ι X s) {x₀ : X}
  (hx₀ : x₀ ∈ s . tactic.mem_univ) :
  ∑ i in ρ.finsupport x₀, ρ i x₀ = 1 :=
begin
  have := ρ.sum_eq_one hx₀,
  rwa finsum_eq_sum_of_support_subset at this,
  rw [ρ.coe_finsupport],
  exact subset.rfl
end

lemma partition_of_unity.sum_finsupport' {s : set X} (ρ : partition_of_unity ι X s) {x₀ : X}
  (hx₀ : x₀ ∈ s . tactic.mem_univ) {I : finset ι} (hI : ρ.finsupport x₀ ⊆ I):
  ∑ i in I, ρ i x₀ = 1 :=
begin
  classical,
  rw [← finset.sum_sdiff hI, ρ.sum_finsupport hx₀],
  suffices : ∑ i in I \ ρ.finsupport x₀, ρ i x₀ = 0, by rw [this, zero_add],
  suffices : ∑ i in I \ ρ.finsupport x₀, (ρ i) x₀ = ∑ i in I \ ρ.finsupport x₀, 0,
  rw [this, finset.sum_const_zero],
  apply finset.sum_congr rfl,
  rintros x hx,
  simp only [finset.mem_sdiff, ρ.mem_finsupport, mem_support, not_not] at hx,
  exact hx.2
end


lemma partition_of_unity.sum_finsupport_smul {s : set X} (ρ : partition_of_unity ι X s) {x₀ : X}
  {M : Type*} [add_comm_group M] [module ℝ M]
  (φ : ι → X → M) :
  ∑ i in ρ.finsupport x₀, ρ i x₀ • φ i x₀ = ∑ᶠ i, ρ i x₀ • φ i x₀ :=
begin
  apply (finsum_eq_sum_of_support_subset _ _).symm,
  erw [ρ.coe_finsupport x₀, support_smul],
  exact inter_subset_left _ _
end

end
