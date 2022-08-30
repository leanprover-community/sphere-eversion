import geometry.manifold.algebra.smooth_functions
import geometry.manifold.instances.real
import topology.metric_space.partition_of_unity
import global.smooth_embedding

noncomputable theory

open_locale manifold
open set metric

section
variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
  {H : Type*} [topological_space H]
  (I : model_with_corners 𝕜 E H)
  {M : Type*} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
  {E' : Type*} [normed_add_comm_group E'] [normed_space 𝕜 E']
  {H' : Type*} [topological_space H']
  (I' : model_with_corners 𝕜 E' H')
  {M' : Type*} [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M']

/-- Definition `def:localisation_data`. -/
structure localisation_data (f : M → M') :=
(ι ι' : Type*)
(hι : encodable ι)
(φ : ι → open_smooth_embedding (model_with_corners_self 𝕜 E) E I M)
(ψ : ι' → open_smooth_embedding (model_with_corners_self 𝕜 E') E' I' M')
(j : ι → ι')
(h₁ : (⋃ i, (φ i) '' (ball (0:E) 1)) = univ)
(h₂ : (⋃ i', (ψ i') '' (ball (0:E') 1)) = univ)
(h₃ : ∀ i, range (f ∘ (φ i)) ⊆ (ψ (j i)) '' (ball (0:E') 1))
(h₄ : locally_finite $ λ i', range (ψ i'))

namespace localisation_data

variables {f : M → M'} {I I'} (ld : localisation_data I I' f)

abbreviation ψj := ld.ψ ∘ ld.j

end localisation_data

end

section
variables
  {E : Type*} [normed_add_comm_group E] [normed_space ℝ E] [finite_dimensional ℝ E]
  {M : Type*} [topological_space M] [sigma_compact_space M] [locally_compact_space M] [t2_space M]
  {H : Type*} [topological_space H] (I : model_with_corners ℝ E H) [model_with_corners.boundaryless I]
  [nonempty M] [charted_space H M] [smooth_manifold_with_corners I M]
  (E' : Type*) [normed_add_comm_group E'] [normed_space ℝ E'] [finite_dimensional ℝ E']
  {H' : Type*} [topological_space H'] (I' : model_with_corners ℝ E' H') [model_with_corners.boundaryless I']
  {M' : Type*} [metric_space M'] [sigma_compact_space M'] [locally_compact_space M']
  [nonempty M'] [charted_space H' M']
  [smooth_manifold_with_corners I' M']

variables (M')

lemma nice_atlas_target :
  ∃ n, ∃ ψ : index_type n → open_smooth_embedding 𝓘(ℝ, E') E' I' M',
  locally_finite (λ i', range (ψ i')) ∧
  (⋃ i', ψ i' '' ball 0 1) = univ :=
let h := (nice_atlas E' I' (λ j : punit, @is_open_univ M' _) (by simp [eq_univ_iff_forall])) in
⟨h.some, h.some_spec.some, h.some_spec.some_spec.2⟩

/-- A collection of charts on a manifold `M'` which are smooth open embeddings with domain the whole
model space, and which cover the manifold when restricted in each case to the unit ball. -/
def target_charts (i' : index_type (nice_atlas_target E' I' M').some) :
  open_smooth_embedding 𝓘(ℝ, E') E' I'  M' :=
(nice_atlas_target E' I' M').some_spec.some i'

lemma target_charts_cover : (⋃ i', (target_charts E' I' M' i') '' (ball (0:E') 1)) = univ :=
(nice_atlas_target E' I' M').some_spec.some_spec.2

variables (E) {M'} {f : M → M'} (hf : continuous f)

lemma nice_atlas_domain :
  ∃ n, ∃ φ : index_type n → open_smooth_embedding 𝓘(ℝ, E) E I M,
  (∀ i, ∃ i', (range (φ i)) ⊆ f ⁻¹' (⇑(target_charts E' I' M' i') '' (ball (0:E') 1))) ∧
  locally_finite (λ i, range (φ i)) ∧
  (⋃ i, φ i '' ball 0 1) = univ :=
nice_atlas E I
  (λ i', ((target_charts E' I' M' i').open_map (ball 0 1) is_open_ball).preimage hf)
  (by rw [← preimage_Union, target_charts_cover, preimage_univ])

/-- Lemma `lem:ex_localisation`
  Any continuous map between manifolds has some localisation data. -/
def std_localisation_data : localisation_data I I' f :=
{ ι := index_type (nice_atlas_domain E I E' I' hf).some,
  ι' := index_type (nice_atlas_target E' I' M').some,
  hι := index_type_encodable _,
  φ := (nice_atlas_domain E I E' I' hf).some_spec.some,
  ψ := target_charts E' I' M',
  j := λ i, ((nice_atlas_domain E I E' I' hf).some_spec.some_spec.1 i).some,
  h₁ := (nice_atlas_domain E I E' I' hf).some_spec.some_spec.2.2,
  h₂ := target_charts_cover E' I' M',
  h₃ := λ i, begin
    rw range_comp,
    rintros - ⟨y, hy, rfl⟩,
    exact ((nice_atlas_domain E I E' I' hf).some_spec.some_spec.1 i).some_spec hy,
  end,
  h₄ := (nice_atlas_target E' I' M').some_spec.some_spec.1 }

/-- Lemma `lem:localisation_stability`. -/
lemma localisation_stability {f : M → M'} (hf : continuous f)
  (ld : localisation_data I I' f) :
  ∃ (ε : M → ℝ) (hε : ∀ m, 0 < ε m) (hε' : continuous ε),
    ∀ (g : M → M') (hg : ∀ m, dist (g m) (f m) < ε m) i, range (g ∘ ld.φ i) ⊆ range (ld.ψj i) :=
begin
  let K : ld.ι' → set M' := λ i, ld.ψ i '' closed_ball 0 1,
  let U : ld.ι' → set M' := λ i, range $ ld.ψ i,
  have hK : ∀ i, is_closed (K i) := λ i, is_compact.is_closed
    (is_compact.image (is_compact_closed_ball 0 1) (ld.ψ i).continuous),
  have hK' : locally_finite K := ld.h₄.subset (λ i, image_subset_range (ld.ψ i) (closed_ball 0 1)),
  have hU : ∀ i, is_open (U i) := λ i, (ld.ψ i).is_open_range,
  have hKU : ∀ i, K i ⊆ U i := λ i, image_subset_range _ _,
  obtain ⟨δ, hδ₀, hδ₁⟩ := exists_continuous_real_forall_closed_ball_subset hK hU hKU hK',
  refine ⟨δ ∘ f, λ m, hδ₀ (f m), by continuity, λ g hg i, _⟩,
  rintros - ⟨e, rfl⟩,
  have hi : f (ld.φ i e) ∈ K (ld.j i) :=
    image_subset _ ball_subset_closed_ball (ld.h₃ i (mem_range_self e)),
  exact hδ₁ (ld.j i) (f $ ld.φ i e) hi (le_of_lt (hg _)),
end

end
