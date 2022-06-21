import logic.equiv.local_equiv

namespace local_equiv

open set

variables {α β : Type*} (e : local_equiv α β)

lemma image_subset_target_of_subset_source {s : set α} (hs : s ⊆ e.source) :
  e '' s ⊆ e.target :=
(e.image_eq_target_inter_inv_preimage hs).symm ▸ set.inter_subset_left _ _

lemma symm_image_image_eq_of_subset_source {s : set α} (hs : s ⊆ e.source) :
  e.symm '' (e '' s) = s :=
begin
  ext,
  simp only [mem_image, exists_exists_and_eq_and],
  refine ⟨_, λ hx, ⟨x, hx, e.left_inv (hs hx)⟩⟩,
  rintros ⟨y, hy, rfl⟩,
  rwa e.left_inv (hs hy),
end

lemma symm_image_subset_preimage_of_subset_target {s : set β} (hs : s ⊆ e.target) :
  e.symm '' s ⊆ e ⁻¹' s :=
begin
  intros x hx,
  obtain ⟨y, hy, rfl⟩ := hx,
  simp only [mem_preimage],
  convert hy,
  rw ← e.eq_symm_apply (e.symm_maps_to (hs hy)) (hs hy),
end

end local_equiv
