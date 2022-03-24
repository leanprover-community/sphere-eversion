import geometry.manifold.partition_of_unity
import to_mathlib.topology.partition_of_unity

namespace smooth_partition_of_unity

open_locale big_operators

variables {ι E H M F : Type*} {U : ι → set M} {s : set M}
variables [normed_group E] [normed_space ℝ E] [finite_dimensional ℝ E]
variables [topological_space H] {I : model_with_corners ℝ E H}
variables [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
variables (p : smooth_partition_of_unity ι I M s) (hp : p.is_subordinate U)
variables (f : ι → M → F) (g : M → F)

lemma finsum_smul_eq [add_comm_group F] [module ℝ F]
  (hfg : ∀ i x, x ∈ s ∩ U i → f i x = g x) {x : M} (hx : x ∈ s) :
  ∑ᶠ i, p i x • f i x = g x :=
p.to_partition_of_unity.finsum_smul_eq hp f g hfg hx

end smooth_partition_of_unity
