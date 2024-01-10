import Mathlib.Topology.PartialHomeomorph

variable {α β : Type _} [TopologicalSpace α] [TopologicalSpace β] (e : PartialHomeomorph α β)

namespace PartialHomeomorph

theorem isOpen_symm_image_iff_of_subset_target {s : Set β} (hs : s ⊆ e.target) :
    IsOpen (e.symm '' s) ↔ IsOpen s := by
  refine' ⟨fun h => _, fun h => e.symm.image_isOpen_of_isOpen h hs⟩
  have hs' : e.symm '' s ⊆ e.source := by
    rw [e.symm_image_eq_source_inter_preimage hs]
    apply Set.inter_subset_left
  rw [← e.image_symm_image_of_subset_target hs]
  exact e.image_isOpen_of_isOpen h hs'

theorem isOpen_image_iff_of_subset_source {s : Set α} (hs : s ⊆ e.source) :
    IsOpen s ↔ IsOpen (e '' s) := by
  rw [← e.symm.isOpen_symm_image_iff_of_subset_target (hs : s ⊆ e.symm.target), e.symm_symm]

end PartialHomeomorph
