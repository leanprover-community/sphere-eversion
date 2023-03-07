import topology.metric_space.hausdorff_distance

open set metric
open_locale topology

variables {α β : Type*} [pseudo_metric_space α] [pseudo_metric_space β]

namespace metric

lemma thickening_ball (x : α) (ε δ : ℝ) : thickening ε (ball x δ) ⊆ ball x (ε + δ) :=
begin
  intro y,
  simp only [mem_thickening_iff, mem_ball],
  rintros ⟨z, hz, hz'⟩,
  calc dist y x ≤ dist y z + dist z x : dist_triangle _ _ _
  ... < ε + δ :  add_lt_add hz' hz
end

lemma inf_dist_pos_iff_not_mem_closure {x : α} {s : set α} (hs : s.nonempty) :
  0 < inf_dist x s ↔ x ∉ closure s :=
by rw [is_closed_closure.not_mem_iff_inf_dist_pos hs.closure, inf_dist_eq_closure]

end metric
open metric

lemma is_compact.exists_thickening_image {f : α → β} {K : set α} {U : set β}
  (hK : is_compact K) (ho : is_open U) (hf : continuous f) (hKU : maps_to f K U) :
  ∃ (ε > 0) (V ∈ 𝓝ˢ K), thickening ε (f '' V) ⊆ U :=
begin
  rcases (hK.image hf).exists_thickening_subset_open ho hKU.image_subset with ⟨r, hr₀, hr⟩,
  refine ⟨r / 2, half_pos hr₀, f ⁻¹' (thickening (r / 2) (f '' K)),
    (is_open_thickening.preimage hf).mem_nhds_set.2 $ image_subset_iff.mp $
      self_subset_thickening (half_pos hr₀) _, _⟩,
  calc thickening (r / 2) (f '' (f ⁻¹' thickening (r / 2) (f '' K)))
     ⊆ thickening (r / 2) (thickening (r / 2) (f '' K)) :
    thickening_subset_of_subset _ (image_preimage_subset _ _)
  ... ⊆ thickening (r / 2 + r / 2) (f '' K) : thickening_thickening_subset _ _ _
  ... = thickening r (f '' K) : by rw [add_halves]
  ... ⊆ U : hr
end
