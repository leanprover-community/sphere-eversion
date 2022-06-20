import geometry.manifold.cont_mdiff

open set function filter charted_space smooth_manifold_with_corners
open_locale topological_space manifold

/-! ### Definition of smooth functions between manifolds -/

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
-- declare a smooth manifold `M` over the pair `(E, H)`.
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{H : Type*} [topological_space H] (I : model_with_corners 𝕜 E H)
{M : Type*} [topological_space M] [charted_space H M] [Is : smooth_manifold_with_corners I M]
-- declare a smooth manifold `M'` over the pair `(E', H')`.
{E' : Type*} [normed_group E'] [normed_space 𝕜 E']
{H' : Type*} [topological_space H'] (I' : model_with_corners 𝕜 E' H')
{M' : Type*} [topological_space M'] [charted_space H' M'] [I's : smooth_manifold_with_corners I' M']
-- declare a smooth manifold `N` over the pair `(F, G)`.
{F : Type*} [normed_group F] [normed_space 𝕜 F]
{G : Type*} [topological_space G] {J : model_with_corners 𝕜 F G}
{N : Type*} [topological_space N] [charted_space G N] [Js : smooth_manifold_with_corners J N]
-- declare a smooth manifold `N'` over the pair `(F', G')`.
{F' : Type*} [normed_group F'] [normed_space 𝕜 F']
{G' : Type*} [topological_space G'] {J' : model_with_corners 𝕜 F' G'}
{N' : Type*} [topological_space N'] [charted_space G' N'] [J's : smooth_manifold_with_corners J' N']
-- declare functions, sets, points and smoothness indices
{f f₁ : M → M'} {s s₁ t : set M} {x : M} {m n : with_top ℕ}

-- The following results generalize `cont_mdiff_within_at_iff'`

namespace local_homeomorph
/-- Given a chart `f` on a manifold with corners, `f.extend` is the extended chart to the model
vector space. -/
@[simp, mfld_simps] def extend (f : local_homeomorph M H) : local_equiv M E :=
f.to_local_equiv ≫ I.to_local_equiv

lemma extend_source {f : local_homeomorph M H} : (f.extend I).source = f.source :=
by rw [extend, local_equiv.trans_source, I.source_eq, preimage_univ, inter_univ]

end local_homeomorph


variables {I I'} [smooth_manifold_with_corners I M] [smooth_manifold_with_corners I' M']

/-- One can reformulate smoothness within a set at a point as continuity within this set at this
point, and smoothness in the corresponding extended chart. -/
lemma cont_mdiff_within_at_iff_of_mem_source
  {c : local_homeomorph M H} (hc : c ∈ maximal_atlas I M)
  {d : local_homeomorph M' H'} (hd : d ∈ maximal_atlas I' M')
  (hx : x ∈ c.source) (hy : f x ∈ d.source) :
  cont_mdiff_within_at I I' n f s x ↔ continuous_within_at f s x ∧
    cont_diff_within_at 𝕜 n (d.extend I' ∘ f ∘ (c.extend I).symm)
    ((c.extend I).target ∩ (c.extend I).symm ⁻¹' (s ∩ f ⁻¹' (d.extend I').source))
    (c.extend I x) :=
begin
  refine ((cont_diff_within_at_local_invariant_prop I I' n).lift_prop_within_at_indep_chart
    hc hx hd hy).trans _,
  rw [cont_diff_within_at_prop, iff_eq_eq],
  congr' 2,
  mfld_set_tac
end

/-- One can reformulate smoothness on a set as continuity on this set, and smoothness in two given
charts that contain the set. -/
lemma cont_mdiff_on_iff_of_subset_source
  {c : local_homeomorph M H} (hc : c ∈ maximal_atlas I M)
  {d : local_homeomorph M' H'} (hd : d ∈ maximal_atlas I' M')
  (hs : s ⊆ c.source) (h2s : f '' s ⊆ d.source) :
  cont_mdiff_on I I' n f s ↔ continuous_on f s ∧
    cont_diff_on 𝕜 n (d.extend I' ∘ f ∘ (c.extend I).symm)
    ((c.extend I).target ∩
      (c.extend I).symm ⁻¹' (s ∩ f ⁻¹' (d.extend I').source)) :=
begin -- todo: cleanup
  split,
  { refine λ H, ⟨H.continuous_on, _⟩,
    rintro x' ⟨h1x', h2x', h3x'⟩,
    rw [mem_preimage] at h3x',
    convert ((cont_mdiff_within_at_iff_of_mem_source hc hd _ _).mp (H _ h2x')).2,
    rw [local_equiv.right_inv _ h1x'],
    rw [← local_homeomorph.extend_source I, ← local_equiv.symm_target],
    rw [← local_equiv.symm_source] at h1x',
    apply local_equiv.maps_to _ h1x',
    rwa [local_homeomorph.extend_source] at h3x' },
  { rintro ⟨h1, h2⟩ x' hx',
    refine (cont_mdiff_within_at_iff_of_mem_source hc hd (hs hx') (h2s $ mem_image_of_mem f hx')).mpr
      ⟨h1.continuous_within_at hx', _⟩,
    apply h2,
    simp only [hx', hs hx', h2s (mem_image_of_mem f hx'), local_homeomorph.extend,
      local_equiv.coe_trans, model_with_corners.to_local_equiv_coe, local_homeomorph.coe_coe,
      comp_app, local_equiv.trans_target, model_with_corners.target_eq,
    model_with_corners.to_local_equiv_coe_symm, local_equiv.coe_trans_symm,
    local_homeomorph.coe_coe_symm,
    local_equiv.trans_source, model_with_corners.source_eq, preimage_univ, inter_univ, mem_inter_eq,
    mem_range_self,
    mem_preimage, model_with_corners.left_inv, local_homeomorph.map_source, and_self,
    local_homeomorph.left_inv] }
end

-- rename or remove depending on whether this is useful
lemma cont_mdiff_on_iff_of_subset_source_special_case {x : M} {y : M'}
  (hs : s ⊆ (chart_at H x).source)
  (h2s : f '' s ⊆ (chart_at H' y).source) :
  cont_mdiff_on I I' n f s ↔ continuous_on f s ∧
    cont_diff_on 𝕜 n ((ext_chart_at I' y) ∘ f ∘ (ext_chart_at I x).symm)
    ((ext_chart_at I x).target ∩
      (ext_chart_at I x).symm ⁻¹' (s ∩ f ⁻¹' (ext_chart_at I' y).source)) :=
cont_mdiff_on_iff_of_subset_source (structure_groupoid.chart_mem_maximal_atlas _ x)
  (structure_groupoid.chart_mem_maximal_atlas _ y) hs h2s

lemma smooth_on_iff_of_subset_source
  {c : local_homeomorph M H} (hc : c ∈ maximal_atlas I M)
  {d : local_homeomorph M' H'} (hd : d ∈ maximal_atlas I' M')
  (hs : s ⊆ c.source) (h2s : f '' s ⊆ d.source) :
  smooth_on I I' f s ↔ continuous_on f s ∧
    cont_diff_on 𝕜 ⊤ (d.extend I' ∘ f ∘ (c.extend I).symm)
    ((c.extend I).target ∩
      (c.extend I).symm ⁻¹' (s ∩ f ⁻¹' (d.extend I').source)) :=
cont_mdiff_on_iff_of_subset_source hc hd hs h2s
