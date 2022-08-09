import topology.local_homeomorph

variables {α β : Type*} [topological_space α] [topological_space β] (e : local_homeomorph α β)

namespace local_homeomorph

-- TODO When migrating this, strengthen Mathlib's `local_homeomorph.image_open_of_open`
lemma is_open_symm_image_iff_of_subset_target {s : set β} (hs : s ⊆ e.target) :
  is_open (e.symm '' s) ↔ is_open s :=
begin
  refine ⟨λ h, _, λ h, e.symm.image_open_of_open h hs⟩,
  have hs' : e.symm '' s ⊆ e.source,
  { rw e.symm_image_eq_source_inter_preimage hs, apply set.inter_subset_left, },
  rw ← e.to_local_equiv.image_symm_image_of_subset_target hs,
  exact e.image_open_of_open h hs',
end

end local_homeomorph
