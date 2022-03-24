import topology.metric_space.hausdorff_distance

/-
TODO: think about versions assuming less than a metric space.
-/

open set
open_locale topological_space

namespace metric

variables {α β : Type*} [pseudo_metric_space α] [pseudo_metric_space β]
lemma ball_subset_thickening {x : α} {E : set α} (hx : x ∈ E) (δ : ℝ) : ball x δ ⊆ thickening δ E :=
by simp_rw [thickening_eq_bUnion_ball, subset_bUnion_of_mem hx]

lemma thickening_union (ε : ℝ) (s t : set α) :
  thickening ε (s ∪ t) = thickening ε s ∪ thickening ε t :=
by { ext x, simp [mem_thickening_iff, or_and_distrib_right, exists_or_distrib] }

lemma thickening_ball (x : α) (ε δ : ℝ) : thickening ε (ball x δ) ⊆ ball x (ε + δ) :=
begin
  intro y,
  simp only [mem_thickening_iff, mem_ball],
  rintros ⟨z, hz, hz'⟩,
  calc dist y x ≤ dist y z + dist z x : dist_triangle _ _ _
  ... < ε + δ :  add_lt_add hz' hz
end

lemma _root_.is_open.exists_thickening {U K : set α} (hU : is_open U)
  (hK : is_compact K) (hK' : K ⊆ U) :
  ∃ ε > 0, metric.thickening ε K ⊆ U :=
begin
  apply hK.induction_on,
  { use [1, zero_lt_one],
    simp },
  { rintros s t hst ⟨ε, ε_pos, h⟩,
    use [ε, ε_pos],
    exact (thickening_subset_of_subset ε hst).trans h },
  { rintros s t ⟨ε, ε_pos, hε⟩ ⟨δ, δ_pos, hδ⟩,
    refine ⟨min ε δ, lt_min ε_pos δ_pos, _⟩,
    rw thickening_union,
    apply union_subset,
    exact (thickening_mono (min_le_left ε δ) s).trans hε,
    exact (thickening_mono (min_le_right ε δ) t).trans hδ },
  { intros x hx,
    rcases metric.mem_nhds_iff.mp (hU.mem_nhds (hK' hx)) with ⟨ε, ε_pos, hε⟩,
    refine ⟨ball x (ε/2), mem_nhds_within_of_mem_nhds $ ball_mem_nhds x (half_pos ε_pos),
            ⟨ε/2, half_pos ε_pos, _⟩⟩,
    have := thickening_ball x (ε/2) (ε/2),
    rw add_halves at this,
    exact this.trans hε }
end

/--
  is this true without the additional assumptions on `α`?
-/
lemma _root_.is_open.exists_thickening_image [locally_compact_space α] [regular_space α]
  {f : α → β} {K : set α} {U : set β} (hU : is_open U) (hK : is_compact K)
  (hf : continuous f) (hKU : f '' K ⊆ U) :
  ∃ (ε > 0) (V ∈ 𝓝ˢ K), metric.thickening ε (f '' V) ⊆ U :=
begin
  obtain ⟨K₂, hK₂, hKK₂, hK₂U⟩ :=
  exists_compact_between hK (hU.preimage hf) (image_subset_iff.mp hKU),
  obtain ⟨ε, hε, h2KU⟩ := hU.exists_thickening (hK₂.image hf) (image_subset_iff.mpr hK₂U),
  refine ⟨ε, hε, K₂, subset_interior_iff_mem_nhds_set.mp hKK₂, h2KU⟩,
end

end metric
