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
  {E : Type*} [inner_product_space ℝ E]
  {M : Type*} [topological_space M] [sigma_compact_space M] [locally_compact_space M] [t2_space M]
  [nonempty M] [charted_space E M] [smooth_manifold_with_corners 𝓘(ℝ, E) M]
  (E' : Type*) [inner_product_space ℝ E']
  {M' : Type*} [metric_space M'] [sigma_compact_space M'] [locally_compact_space M']
  [nonempty M'] [charted_space E' M']
  [smooth_manifold_with_corners 𝓘(ℝ, E') M']

variables (M')

lemma nice_atlas_target :
  ∃ n, ∃ ψ : index_type n → open_smooth_embedding 𝓘(ℝ, E') E' 𝓘(ℝ, E') M',
  locally_finite (λ i', range (ψ i')) ∧
  (⋃ i', ψ i' '' ball 0 1) = univ :=
let H := (nice_atlas E' (λ j : punit, @is_open_univ M' _) (by simp [eq_univ_iff_forall])) in
⟨H.some, H.some_spec.some, H.some_spec.some_spec.2⟩

/-- A collection of charts on a manifold `M'` which are smooth open embeddings with domain the whole
model space, and which cover the manifold when restricted in each case to the unit ball. -/
def target_charts (i' : index_type (nice_atlas_target E' M').some) :
  open_smooth_embedding 𝓘(ℝ, E') E' 𝓘(ℝ, E') M' :=
(nice_atlas_target E' M').some_spec.some i'

lemma target_charts_cover : (⋃ i', (target_charts E' M' i') '' (ball (0:E') 1)) = univ :=
(nice_atlas_target E' M').some_spec.some_spec.2

variables {M'} {f : M → M'} (hf : continuous f)

lemma nice_atlas_domain :
  ∃ n, ∃ φ : index_type n → open_smooth_embedding 𝓘(ℝ, E) E 𝓘(ℝ, E) M,
  (∀ i, ∃ i', (range (φ i)) ⊆ f ⁻¹' (⇑(target_charts E' M' i') '' (ball (0:E') 1))) ∧
  locally_finite (λ i, range (φ i)) ∧
  (⋃ i, φ i '' ball 0 1) = univ :=
nice_atlas E
  (λ i', ((target_charts E' M' i').open_map (ball 0 1) is_open_ball).preimage hf)
  (by rw [← preimage_Union, target_charts_cover, preimage_univ])

/-- Lemma `lem:ex_localisation`
  Any continuous map between manifolds has some localisation data. -/
def std_localisation_data : localisation_data 𝓘(ℝ, E) 𝓘(ℝ, E') f :=
{ ι := index_type (nice_atlas_domain E' hf).some,
  ι' := index_type (nice_atlas_target E' M').some,
  hι := index_type_encodable _,
  φ := (nice_atlas_domain E' hf).some_spec.some,
  ψ := target_charts E' M',
  j := λ i, ((nice_atlas_domain E' hf).some_spec.some_spec.1 i).some,
  h₁ := (nice_atlas_domain E' hf).some_spec.some_spec.2.2,
  h₂ := target_charts_cover E' M',
  h₃ := λ i, begin
    rw range_comp,
    rintros - ⟨y, hy, rfl⟩,
    exact ((nice_atlas_domain E' hf).some_spec.some_spec.1 i).some_spec hy,
  end,
  h₄ := (nice_atlas_target E' M').some_spec.some_spec.1 }

end
