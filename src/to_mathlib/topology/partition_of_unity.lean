import topology.partition_of_unity

namespace partition_of_unity

open_locale topological_space big_operators
open function set

variables {ι X : Type*} {U : ι → set X} {s : set X} [topological_space X]
variables (p : partition_of_unity ι X s) (hp : p.is_subordinate U)
include hp

lemma exists_finset_nhd (ho : ∀ i, is_open (U i)) (x : X) :
  ∃ (is : finset ι) {n : set X} (hn₁ : n ∈ 𝓝 x) (hn₂ : n ⊆ ⋂ i ∈ is, U i), ∀ (z ∈ n),
    support (λ i, p i z) ⊆ is :=
begin
  -- Ridiculous proof
  obtain ⟨n, hn, hn'⟩ := p.locally_finite x,
  classical,
  let is := hn'.to_finset.filter (λ i, x ∈ U i),
  let js := hn'.to_finset.filter (λ j, x ∉ U j),
  refine ⟨is, n ∩ (⋂ j ∈ js, (tsupport (p j))ᶜ) ∩ (⋂ i ∈ is, U i),
    filter.inter_mem (filter.inter_mem hn _) _, inter_subset_right _ _, λ z hz, _⟩,
  { refine (filter.bInter_finset_mem js).mpr (λ j hj, is_closed.compl_mem_nhds
      (is_closed_tsupport _) _),
    simp only [finset.mem_filter, finite.mem_to_finset, mem_set_of_eq] at hj,
    exact set.not_mem_subset (hp j) hj.2, },
  { refine (filter.bInter_finset_mem is).mpr (λ i hi, _),
    simp only [finset.mem_filter, finite.mem_to_finset, mem_set_of_eq] at hi,
    exact (ho i).mem_nhds hi.2, },
  { have hz' : z ∈ n,
    { rw inter_assoc at hz,
      exact mem_of_mem_inter_left hz, },
    have h₁ : support (λ i, p i z) ⊆ hn'.to_finset,
    { simp only [finite.coe_to_finset, mem_set_of_eq],
      exact λ i hi, ⟨z, mem_inter hi hz'⟩, },
    have hz₂ : ∀ j ∈ hn'.to_finset, j ∈ js → z ∉ support (p j),
    { rintros j - hj,
      replace hz := mem_of_mem_inter_right (mem_of_mem_inter_left hz),
      simp only [finset.mem_filter, finite.mem_to_finset, mem_set_of_eq, mem_Inter, mem_compl_eq,
        and_imp] at hz,
      simp only [finset.mem_filter, finite.mem_to_finset, mem_set_of_eq] at hj,
      exact set.not_mem_subset (subset_tsupport (p j)) (hz j hj.1 hj.2), },
    intros i hi,
    suffices : i ∉ js,
    { simp only [finset.mem_filter, not_and, not_not_mem] at this,
      simp only [finset.coe_filter, finite.coe_to_finset, sep_set_of, mem_set_of_eq],
      refine ⟨_, this (h₁ hi)⟩,
      specialize h₁ hi,
      simpa using h₁, },
    exact λ contra, hz₂ i (h₁ hi) contra hi, },
end

lemma finsum_smul_eq {F : Type*} [add_comm_group F] [module ℝ F]
  (f : ι → X → F) (g : X → F)
  (hfg : ∀ i x, x ∈ s ∩ U i → f i x = g x) {x : X} (hx : x ∈ s) :
  ∑ᶠ i, p i x • f i x = g x :=
begin
  suffices : ∀ i, p i x • f i x = p i x • g x,
  { simp_rw [this, ← finsum_smul, p.sum_eq_one hx, one_smul], },
  intros i,
  by_cases hxi : x ∈ U i,
  { rw hfg i x (set.mem_inter hx hxi), },
  { suffices : x ∉ function.support (p i),
    { simp only [function.mem_support, not_not] at this,
      simp [this], },
    exact λ contra, hxi (hp i (subset_tsupport _ contra)), },
end

end partition_of_unity
