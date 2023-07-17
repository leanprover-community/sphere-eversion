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
    IsOpen s ↔ ∀ x : M, IsOpen <| chartAt H x '' ((chartAt H x).source ∩ s) :=
  by
  refine' ⟨fun h x => (chart_at H x).image_open_of_open' h, fun h => _⟩
  rw [← s.inter_univ, ← Union_source_eq_univ H M, s.inter_Union]
  refine' isOpen_iUnion fun x => _
  have : s ∩ (chart_at H x).source ⊆ (chart_at H x).source := inter_subset_right _ _
  rw [(chart_at H x).isOpen_image_iff_of_subset_source this, inter_comm]
  exact h x

end ChartedSpace

