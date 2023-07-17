import Mathlib.Topology.Constructions
import Mathlib.Topology.LocallyFinite

open Set Function Filter

open scoped Topology Filter

universe u

variable {ι : Type u} {X Y : Type _} [TopologicalSpace X] [TopologicalSpace Y]

-- This needs to go into topology.constructions which imports locally_finite and defines the
-- product topology.
theorem LocallyFinite.prod_right {f : ι → Set X} (hf : LocallyFinite f) (g : ι → Set Y) :
    LocallyFinite fun i => f i ×ˢ g i :=
  (hf.preimage_continuous continuous_fst).subset fun _ ↦ prod_subset_preimage_fst _ _

theorem LocallyFinite.prod_left {f : ι → Set X} (hf : LocallyFinite f) (g : ι → Set Y) :
    LocallyFinite fun i => g i ×ˢ f i :=
  (hf.preimage_continuous continuous_snd).subset fun _ ↦ prod_subset_preimage_snd _ _
