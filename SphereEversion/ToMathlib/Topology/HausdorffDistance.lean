import Mathlib.Topology.MetricSpace.HausdorffDistance

open Set Metric

open scoped Topology

variable {α β : Type _} [PseudoMetricSpace α] [PseudoMetricSpace β]

namespace Metric

theorem thickening_ball (x : α) (ε δ : ℝ) : thickening ε (ball x δ) ⊆ ball x (ε + δ) := by
  rw [← thickening_singleton, ← thickening_singleton]
  apply thickening_thickening_subset

theorem infDist_pos_iff_not_mem_closure {x : α} {s : Set α} (hs : s.Nonempty) :
    0 < infDist x s ↔ x ∉ closure s := by
  rw [isClosed_closure.not_mem_iff_infDist_pos hs.closure, infDist_closure]

end Metric

open Metric

theorem IsCompact.exists_thickening_image {f : α → β} {K : Set α} {U : Set β} (hK : IsCompact K)
    (ho : IsOpen U) (hf : Continuous f) (hKU : MapsTo f K U) :
    ∃ ε > 0, ∃ V ∈ 𝓝ˢ K, thickening ε (f '' V) ⊆ U := by
  rcases (hK.image hf).exists_thickening_subset_open ho hKU.image_subset with ⟨r, hr₀, hr⟩
  refine ⟨r / 2, half_pos hr₀, f ⁻¹' thickening (r / 2) (f '' K),
    hf.tendsto_nhdsSet (mapsTo_image _ _) (thickening_mem_nhdsSet _ (half_pos hr₀)), ?_⟩
  calc
    thickening (r / 2) (f '' (f ⁻¹' thickening (r / 2) (f '' K))) ⊆
        thickening (r / 2) (thickening (r / 2) (f '' K)) :=
      thickening_subset_of_subset _ (image_preimage_subset _ _)
    _ ⊆ thickening (r / 2 + r / 2) (f '' K) := (thickening_thickening_subset _ _ _)
    _ = thickening r (f '' K) := by rw [add_halves]
    _ ⊆ U := hr
