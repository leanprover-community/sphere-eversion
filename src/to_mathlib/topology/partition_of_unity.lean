import topology.partition_of_unity

namespace partition_of_unity

open_locale topological_space big_operators
open function set

variables {ι X : Type*} {U : ι → set X} {s : set X} [topological_space X]
variables (p : partition_of_unity ι X s) (hp : p.is_subordinate U)
include hp

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
