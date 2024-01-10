import Mathlib.Geometry.Manifold.ChartedSpace
import SphereEversion.ToMathlib.Topology.LocalHomeomorph

namespace ChartedSpace

open Set

variable (H : Type _) (M : Type _) [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]

@[simp]
theorem iUnion_source_eq_univ : (⋃ x : M, (chartAt H x).source) = (univ : Set M) :=
  eq_univ_iff_forall.mpr fun x => mem_iUnion.mpr ⟨x, mem_chart_source H x⟩

variable {M}

theorem isOpen_iff (s : Set M) :
    IsOpen s ↔ ∀ x : M, IsOpen <| chartAt H x '' ((chartAt H x).source ∩ s) := by
  refine' ⟨fun h x => (chartAt H x).image_isOpen_of_isOpen' h, fun h => _⟩
  rw [← s.inter_univ, ← iUnion_source_eq_univ H M, s.inter_iUnion]
  refine' isOpen_iUnion fun x => _
  have : s ∩ (chartAt H x).source ⊆ (chartAt H x).source := inter_subset_right _ _
  rw [(chartAt H x).isOpen_image_iff_of_subset_source this, inter_comm]
  exact h x

end ChartedSpace
