import geometry.manifold.smooth_manifold_with_corners

import to_mathlib.topology.local_homeomorph

namespace charted_space

section topological_space

open set

variables (H : Type*) (M : Type*) [topological_space H] [topological_space M] [charted_space H M]

@[simp] lemma Union_source_eq_univ : (⋃ (x : M), (chart_at H x).source) = (univ : set M) :=
eq_univ_iff_forall.mpr (λ x, mem_Union.mpr ⟨x, mem_chart_source H x⟩)

variables {M}

lemma is_open_iff (s : set M) :
  is_open s ↔ ∀ (x : M), is_open $ chart_at H x '' ((chart_at H x).source ∩ s) :=
begin
  refine ⟨λ h x, (chart_at H x).image_open_of_open' h, λ h, _⟩,
  rw [← s.inter_univ, ← Union_source_eq_univ H M, s.inter_Union],
  refine is_open_Union (λ x, _),
  have : s ∩ (chart_at H x).source ⊆ (chart_at H x).source := inter_subset_right _ _,
  rw [(chart_at H x).is_open_image_iff_of_subset_source this, inter_comm],
  exact h x,
end

end topological_space

section normed_add_comm_group

open_locale topological_space
open metric (hiding mem_nhds_iff ball) set

variables {E M H : Type*} [topological_space H] [topological_space M] [charted_space H M]
variables [normed_add_comm_group E] [normed_space ℝ E]
variables (I : model_with_corners ℝ E H) [model_with_corners.boundaryless I]

lemma ext_chart_at_map_nhds_of_boundaryless {x : M} :
  filter.map (ext_chart_at I x) (𝓝 x) = 𝓝 (ext_chart_at I x x) :=
by rw [ext_chart_at_map_nhds I x, model_with_corners.boundaryless.range_eq_univ, nhds_within_univ]

lemma ext_chart_at_image_nhd_mem_nhds_of_boundaryless {x : M} {s : set M} (h : s ∈ 𝓝 x) :
  (ext_chart_at I x) '' s ∈ 𝓝 (ext_chart_at I x x) :=
begin
  rw [← ext_chart_at_map_nhds_of_boundaryless, filter.mem_map],
  filter_upwards [h] using subset_preimage_image (ext_chart_at I x) s,
end

def ball (x : M) (r : ℝ) := (ext_chart_at I x).symm '' metric.ball (ext_chart_at I x x) r

lemma nhds_has_basis_balls_of_open_cov (x : M)
  {ι : Type*} {s : ι → set M} (s_op : ∀ j, is_open $ s j) (cov : (⋃ j, s j) = univ) :
  (𝓝 x).has_basis (λ r, 0 < r ∧
                         metric.ball (ext_chart_at I x x) r ⊆ (ext_chart_at I x).target ∧
                         ∃ j, charted_space.ball I x r ⊆ s j)
                   (charted_space.ball I x) :=
begin
  -- MASSIVE golfing opportunity!
  obtain ⟨j, hj⟩ : ∃ j, x ∈ s j, by { simpa only [mem_Union, ← cov] using mem_univ x, },
  replace hj : s j ∈ 𝓝 x := mem_nhds_iff.mpr ⟨s j, subset.rfl, s_op j, hj⟩,
  have hx : (ext_chart_at I x).source ∈ 𝓝 x := ext_chart_at_source_mem_nhds I x,
  refine filter.has_basis_iff.mpr (λ n, ⟨λ hn, _, _⟩),
  { let m := s j ∩ n ∩ (ext_chart_at I x).source,
    have hm : m ∈ 𝓝 x := filter.inter_mem (filter.inter_mem hj hn) hx,
    replace hm : (ext_chart_at I x) '' m ∈ 𝓝 (ext_chart_at I x x) :=
      ext_chart_at_image_nhd_mem_nhds_of_boundaryless I hm,
    obtain ⟨r, hr₀, hr₁⟩ :=
      (filter.has_basis_iff.mp (@nhds_basis_ball E _ (ext_chart_at I x x)) _).mp hm,
    refine ⟨r, ⟨hr₀, hr₁.trans _, ⟨j, _⟩⟩, _⟩,
    { exact ((ext_chart_at I x).maps_to.mono (inter_subset_right _ _) subset.rfl).image_subset },
    { suffices : m ⊆ s j,
      { refine subset.trans _ this,
        convert monotone_image hr₁,
        exact (local_equiv.symm_image_image_of_subset_source _
          (set.inter_subset_right _ _)).symm, },
      exact (set.inter_subset_left _ _).trans (set.inter_subset_left _ _), },
    { suffices : m ⊆ n,
      { refine subset.trans _ this,
        convert monotone_image hr₁,
        exact (local_equiv.symm_image_image_of_subset_source _
          (set.inter_subset_right _ _)).symm, },
      exact (set.inter_subset_left _ _).trans (set.inter_subset_right _ _), }, },
  { rintros ⟨r, ⟨hr₀, hr₁, -⟩, hr₂⟩,
    replace hr₀ : metric.ball (ext_chart_at I x x) r ∈ 𝓝 (ext_chart_at I x x) := ball_mem_nhds _ hr₀,
    rw [← ext_chart_at_map_nhds_of_boundaryless, filter.mem_map] at hr₀,
    replace hr₀ := filter.inter_mem hx hr₀,
    rw ← (ext_chart_at I x).symm_image_eq_source_inter_preimage hr₁ at hr₀,
    filter_upwards [hr₀] using hr₂, },
end

end normed_add_comm_group

end charted_space
