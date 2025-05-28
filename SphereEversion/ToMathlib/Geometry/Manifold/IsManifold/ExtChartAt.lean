import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt

open scoped Topology

open Metric hiding mem_nhds_iff ball

open Set

section

variable {𝕜 E M H : Type*} [NontriviallyNormedField 𝕜]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] (I : ModelWithCorners 𝕜 E H)

namespace ChartedSpace

/-- If `M` is a `ChartedSpace` we can use the preferred chart at any point to transfer a
ball in coordinate space into a set in `M`. These can be a useful neighbourhood basis. -/
def ball (x : M) (r : ℝ) :=
  (extChartAt I x).symm '' Metric.ball (extChartAt I x x) r

theorem nhds_hasBasis_balls_of_open_cov [I.Boundaryless] (x : M) {ι : Type*} {s : ι → Set M}
    (s_op : ∀ j, IsOpen <| s j) (cov : (⋃ j, s j) = univ) :
    (𝓝 x).HasBasis (fun r ↦ 0 < r ∧ Metric.ball (extChartAt I x x) r ⊆ (extChartAt I x).target ∧
        ∃ j, ChartedSpace.ball I x r ⊆ s j)
      (ChartedSpace.ball I x) := by
  -- TODO golf etc
  obtain ⟨j, hj⟩ : ∃ j, x ∈ s j := by simpa only [mem_iUnion, ← cov] using mem_univ x
  replace hj : s j ∈ 𝓝 x := mem_nhds_iff.mpr ⟨s j, Subset.rfl, s_op j, hj⟩
  have hx : (extChartAt I x).source ∈ 𝓝 x := extChartAt_source_mem_nhds x
  refine Filter.hasBasis_iff.mpr fun n ↦ ⟨fun hn ↦ ?_, ?_⟩
  · let m := s j ∩ n ∩ (extChartAt I x).source
    have hm : m ∈ 𝓝 x := Filter.inter_mem (Filter.inter_mem hj hn) hx
    replace hm : extChartAt I x '' m ∈ 𝓝 (extChartAt I x x) :=
      extChartAt_image_nhds_mem_nhds_of_boundaryless hm
    obtain ⟨r, hr₀, hr₁⟩ :=
      (Filter.hasBasis_iff.mp (@nhds_basis_ball E _ (extChartAt I x x)) _).mp hm
    refine ⟨r, ⟨hr₀, hr₁.trans ?_, ⟨j, ?_⟩⟩, ?_⟩
    · exact ((extChartAt I x).mapsTo.mono inter_subset_right Subset.rfl).image_subset
    · suffices m ⊆ s j by
        refine Subset.trans ?_ this
        convert monotone_image (f := (extChartAt I x).symm) hr₁
        exact (PartialEquiv.symm_image_image_of_subset_source _ inter_subset_right).symm
      exact inter_subset_left.trans inter_subset_left
    · suffices m ⊆ n by
        refine Subset.trans ?_ this
        convert monotone_image (f := (extChartAt I x).symm) hr₁
        exact (PartialEquiv.symm_image_image_of_subset_source _ inter_subset_right).symm
      exact inter_subset_left.trans inter_subset_right
  · rintro ⟨r, ⟨hr₀, hr₁, -⟩, hr₂⟩
    replace hr₀ : Metric.ball (extChartAt I x x) r ∈ 𝓝 (extChartAt I x x) := ball_mem_nhds _ hr₀
    rw [← map_extChartAt_nhds_of_boundaryless, Filter.mem_map] at hr₀
    replace hr₀ := Filter.inter_mem hx hr₀
    rw [← (extChartAt I x).symm_image_eq_source_inter_preimage hr₁] at hr₀
    filter_upwards [hr₀] using hr₂

end ChartedSpace

end
