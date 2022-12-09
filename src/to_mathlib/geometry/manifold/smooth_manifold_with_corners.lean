import geometry.manifold.smooth_manifold_with_corners

open_locale topological_space
open metric (hiding mem_nhds_iff ball) set

variables {𝕜 E M H : Type*} [nontrivially_normed_field 𝕜]
variables [topological_space H] [topological_space M] [charted_space H M]
variables [normed_add_comm_group E] [normed_space 𝕜 E]
variables (I : model_with_corners 𝕜 E H)

lemma map_ext_chart_at_nhds_of_boundaryless [I.boundaryless] {x : M} :
  filter.map (ext_chart_at I x) (𝓝 x) = 𝓝 (ext_chart_at I x x) :=
by rw [map_ext_chart_at_nhds I x, model_with_corners.boundaryless.range_eq_univ, nhds_within_univ]

lemma ext_chart_at_image_nhd_mem_nhds_of_boundaryless [I.boundaryless]
  {x : M} {s : set M} (h : s ∈ 𝓝 x) :
  (ext_chart_at I x) '' s ∈ 𝓝 (ext_chart_at I x x) :=
begin
  rw [← map_ext_chart_at_nhds_of_boundaryless, filter.mem_map],
  filter_upwards [h] using subset_preimage_image (ext_chart_at I x) s,
end

namespace charted_space

/-- If `M` is a `charted_space` we can use the preferred chart at any point to transfer a
ball in coordinate space into a set in `M`. These can be a useful neighbourhood basis. -/
def ball (x : M) (r : ℝ) := (ext_chart_at I x).symm '' metric.ball (ext_chart_at I x x) r

lemma nhds_has_basis_balls_of_open_cov [I.boundaryless] (x : M)
  {ι : Type*} {s : ι → set M} (s_op : ∀ j, is_open $ s j) (cov : (⋃ j, s j) = univ) :
  (𝓝 x).has_basis (λ r, 0 < r ∧
                         metric.ball (ext_chart_at I x x) r ⊆ (ext_chart_at I x).target ∧
                         ∃ j, charted_space.ball I x r ⊆ s j)
                   (charted_space.ball I x) :=
begin
  -- TODO golf etc
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
    rw [← map_ext_chart_at_nhds_of_boundaryless, filter.mem_map] at hr₀,
    replace hr₀ := filter.inter_mem hx hr₀,
    rw ← (ext_chart_at I x).symm_image_eq_source_inter_preimage hr₁ at hr₀,
    filter_upwards [hr₀] using hr₂, },
end

end charted_space
