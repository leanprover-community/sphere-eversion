import Mathbin.Topology.MetricSpace.HausdorffDistance

open Set Metric

open scoped Topology

variable {α β : Type _} [PseudoMetricSpace α] [PseudoMetricSpace β]

namespace Metric

theorem thickening_ball (x : α) (ε δ : ℝ) : thickening ε (ball x δ) ⊆ ball x (ε + δ) :=
  by
  intro y
  simp only [mem_thickening_iff, mem_ball]
  rintro ⟨z, hz, hz'⟩
  calc
    dist y x ≤ dist y z + dist z x := dist_triangle _ _ _
    _ < ε + δ := add_lt_add hz' hz

theorem infDist_pos_iff_not_mem_closure {x : α} {s : Set α} (hs : s.Nonempty) :
    0 < infDist x s ↔ x ∉ closure s := by
  rw [is_closed_closure.not_mem_iff_inf_dist_pos hs.closure, inf_dist_eq_closure]

end Metric

open Metric

theorem IsCompact.exists_thickening_image {f : α → β} {K : Set α} {U : Set β} (hK : IsCompact K)
    (ho : IsOpen U) (hf : Continuous f) (hKU : MapsTo f K U) :
    ∃ ε > 0, ∃ V ∈ 𝓝ˢ K, thickening ε (f '' V) ⊆ U :=
  by
  rcases(hK.image hf).exists_thickening_subset_open ho hKU.image_subset with ⟨r, hr₀, hr⟩
  refine'
    ⟨r / 2, half_pos hr₀, f ⁻¹' thickening (r / 2) (f '' K),
      (is_open_thickening.preimage hf).mem_nhdsSet.2 <|
        image_subset_iff.mp <| self_subset_thickening (half_pos hr₀) _,
      _⟩
  calc
    thickening (r / 2) (f '' (f ⁻¹' thickening (r / 2) (f '' K))) ⊆
        thickening (r / 2) (thickening (r / 2) (f '' K)) :=
      thickening_subset_of_subset _ (image_preimage_subset _ _)
    _ ⊆ thickening (r / 2 + r / 2) (f '' K) := (thickening_thickening_subset _ _ _)
    _ = thickening r (f '' K) := by rw [add_halves]
    _ ⊆ U := hr

