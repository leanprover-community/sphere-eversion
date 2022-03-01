import topology.metric_space.hausdorff_distance

/-
TODO: think about versions assuming less than a metric space.
-/

open set

namespace metric

lemma thickening_union {α : Type*} [metric_space α] (ε : ℝ) (s t : set α) :
  thickening ε (s ∪ t) = thickening ε s ∪ thickening ε t :=
begin
  ext x,
  simp only [mem_thickening_iff, mem_union],
  split,
  { rintros ⟨z, z_in|z_in, hz⟩; [left, right] ; tauto },
  { rintros (⟨z, z_in, hz⟩|⟨z, z_in, hz⟩) ; refine ⟨z, _, hz⟩ ; tauto }
end

lemma thickening_ball {α : Type*} [metric_space α] (x : α) (ε δ : ℝ)  :
  thickening ε (ball x δ) ⊆ ball x (ε + δ) :=
begin
  intro y,
  simp only [mem_thickening_iff, mem_ball],
  rintros ⟨z, hz, hz'⟩,
  calc dist y x ≤ dist y z + dist z x : dist_triangle _ _ _
  ... < ε + δ :  add_lt_add hz' hz
end

lemma _root_.is_open.exists_thickening {α : Type*} [metric_space α] {U K : set α} (h : is_open U)
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
    rcases metric.mem_nhds_iff.mp (h.mem_nhds (hK' hx)) with ⟨ε, ε_pos, hε⟩,
    refine ⟨ball x (ε/2), mem_nhds_within_of_mem_nhds $ ball_mem_nhds x (half_pos ε_pos),
            ⟨ε/2, half_pos ε_pos, _⟩⟩,
    have := thickening_ball x (ε/2) (ε/2),
    rw add_halves at this,
    exact this.trans hε }
end

end metric
