import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.MetricSpace.PartitionOfUnity
import SphereEversion.Global.SmoothEmbedding

noncomputable section

open scoped Manifold

open Set Metric

section

variable {𝕜 : Type _} [NontriviallyNormedField 𝕜] {E : Type _} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type _} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) {M : Type _}
  [TopologicalSpace M] [ChartedSpace H M] [SmoothManifoldWithCorners I M] {E' : Type _}
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type _} [TopologicalSpace H']
  (I' : ModelWithCorners 𝕜 E' H') {M' : Type _} [TopologicalSpace M'] [ChartedSpace H' M']
  [SmoothManifoldWithCorners I' M']

/-- Definition `def:localisation_data`. -/
structure LocalisationData (f : M → M') where
  cont : Continuous f
  ι' : Type _
  N : ℕ
  φ : IndexType N → OpenSmoothEmbedding 𝓘(𝕜, E) E I M
  ψ : ι' → OpenSmoothEmbedding 𝓘(𝕜, E') E' I' M'
  j : IndexType N → ι'
  h₁ : (⋃ i, φ i '' ball (0 : E) 1) = univ
  h₂ : (⋃ i', ψ i' '' ball (0 : E') 1) = univ
  h₃ : ∀ i, range (f ∘ φ i) ⊆ ψ (j i) '' ball (0 : E') 1
  h₄ : LocallyFinite fun i' => range (ψ i')
  lf_φ : LocallyFinite fun i => range (φ i)

namespace LocalisationData

variable {f : M → M'} {I I'} (ld : LocalisationData I I' f)

abbrev ψj :=
  ld.ψ ∘ ld.j

/-- The type indexing the source charts of the given localisation data. -/
def ι (L : LocalisationData I I' f) :=
  IndexType L.N

theorem iUnion_succ' {β : Type _} (s : ld.ι → Set β) (i : IndexType ld.N) :
    (⋃ j ≤ i, s j) = (⋃ j < i, s j) ∪ s i :=
  by
  simp only [(fun j => le_iff_lt_or_eq : ∀ j, j ≤ i ↔ j < i ∨ j = i)]
  erw [bUnion_union, bUnion_singleton]
  rfl

open Filter

end LocalisationData

end

section

open ModelWithCorners

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {M : Type _}
  [TopologicalSpace M] [SigmaCompactSpace M] [LocallyCompactSpace M] [T2Space M] {H : Type _}
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [Boundaryless I] [Nonempty M] [ChartedSpace H M]
  [SmoothManifoldWithCorners I M] (E' : Type _) [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [FiniteDimensional ℝ E'] {H' : Type _} [TopologicalSpace H'] (I' : ModelWithCorners ℝ E' H')
  [Boundaryless I'] {M' : Type _} [MetricSpace M'] [SigmaCompactSpace M'] [LocallyCompactSpace M']
  [Nonempty M'] [ChartedSpace H' M'] [SmoothManifoldWithCorners I' M']

variable (M')

theorem nice_atlas_target :
    ∃ n,
      ∃ ψ : IndexType n → OpenSmoothEmbedding 𝓘(ℝ, E') E' I' M',
        (LocallyFinite fun i' => range (ψ i')) ∧ (⋃ i', ψ i' '' ball 0 1) = univ :=
  let h := nice_atlas E' I' (fun j : PUnit => @isOpen_univ M' _) (by simp [eq_univ_iff_forall])
  ⟨h.some, h.choose_spec.some, h.choose_spec.choose_spec.2⟩

/-- A collection of charts on a manifold `M'` which are smooth open embeddings with domain the whole
model space, and which cover the manifold when restricted in each case to the unit ball. -/
def targetCharts (i' : IndexType (nice_atlas_target E' I' M').some) :
    OpenSmoothEmbedding 𝓘(ℝ, E') E' I' M' :=
  (nice_atlas_target E' I' M').choose_spec.some i'

theorem targetCharts_cover : (⋃ i', targetCharts E' I' M' i' '' ball (0 : E') 1) = univ :=
  (nice_atlas_target E' I' M').choose_spec.choose_spec.2

variable (E) {M'} {f : M → M'} (hf : Continuous f)

theorem nice_atlas_domain :
    ∃ n,
      ∃ φ : IndexType n → OpenSmoothEmbedding 𝓘(ℝ, E) E I M,
        (∀ i, ∃ i', range (φ i) ⊆ f ⁻¹' (⇑(targetCharts E' I' M' i') '' ball (0 : E') 1)) ∧
          (LocallyFinite fun i => range (φ i)) ∧ (⋃ i, φ i '' ball 0 1) = univ :=
  nice_atlas E I
    (fun i' => ((targetCharts E' I' M' i').open_map (ball 0 1) isOpen_ball).preimage hf)
    (by rw [← preimage_Union, targetCharts_cover, preimage_univ])

/-- Lemma `lem:ex_localisation`
  Any continuous map between manifolds has some localisation data. -/
def stdLocalisationData : LocalisationData I I' f
    where
  cont := hf
  N := (nice_atlas_domain E I E' I' hf).some
  ι' := IndexType (nice_atlas_target E' I' M').some
  φ := (nice_atlas_domain E I E' I' hf).choose_spec.some
  ψ := targetCharts E' I' M'
  j i := ((nice_atlas_domain E I E' I' hf).choose_spec.choose_spec.1 i).some
  h₁ := (nice_atlas_domain E I E' I' hf).choose_spec.choose_spec.2.2
  h₂ := targetCharts_cover E' I' M'
  h₃ i := by
    rw [range_comp]
    rintro - ⟨y, hy, rfl⟩
    exact ((nice_atlas_domain E I E' I' hf).choose_spec.choose_spec.1 i).choose_spec hy
  h₄ := (nice_atlas_target E' I' M').choose_spec.choose_spec.1
  lf_φ := (nice_atlas_domain E I E' I' hf).choose_spec.choose_spec.2.1

variable {E E' I I'}

/-- Lemma `lem:localisation_stability`. -/
theorem localisation_stability {f : M → M'} (ld : LocalisationData I I' f) :
    ∃ (ε : M → ℝ) (hε : ∀ m, 0 < ε m) (hε' : Continuous ε),
      ∀ (g : M → M') (hg : ∀ m, dist (g m) (f m) < ε m) (i), range (g ∘ ld.φ i) ⊆ range (ld.ψj i) :=
  by
  let K : ld.ι' → Set M' := fun i => ld.ψ i '' closed_ball 0 1
  let U : ld.ι' → Set M' := fun i => range <| ld.ψ i
  have hK : ∀ i, IsClosed (K i) := fun i =>
    IsCompact.isClosed (IsCompact.image (is_compact_closed_ball 0 1) (ld.ψ i).continuous)
  have hK' : LocallyFinite K := ld.h₄.subset fun i => image_subset_range (ld.ψ i) (closed_ball 0 1)
  have hU : ∀ i, IsOpen (U i) := fun i => (ld.ψ i).isOpen_range
  have hKU : ∀ i, K i ⊆ U i := fun i => image_subset_range _ _
  obtain ⟨δ, hδ₀, hδ₁⟩ := exists_continuous_real_forall_closed_ball_subset hK hU hKU hK'
  have := ld.cont
  refine' ⟨δ ∘ f, fun m => hδ₀ (f m), by continuity, fun g hg i => _⟩
  rintro - ⟨e, rfl⟩
  have hi : f (ld.φ i e) ∈ K (ld.j i) :=
    image_subset _ ball_subset_closed_ball (ld.h₃ i (mem_range_self e))
  exact hδ₁ (ld.j i) (f <| ld.φ i e) hi (le_of_lt (hg _))

namespace LocalisationData

protected def ε (ld : LocalisationData I I' f) : M → ℝ :=
  (localisation_stability ld).some

theorem ε_pos (ld : LocalisationData I I' f) : ∀ m, 0 < ld.ε m :=
  (localisation_stability ld).choose_spec.some

theorem ε_cont (ld : LocalisationData I I' f) : Continuous ld.ε :=
  (localisation_stability ld).choose_spec.choose_spec.some

theorem ε_spec (ld : LocalisationData I I' f) :
    ∀ (g : M → M') (hg : ∀ m, dist (g m) (f m) < ld.ε m) (i : ld.ι),
      range (g ∘ ld.φ i) ⊆ range (ld.ψj i) :=
  (localisation_stability ld).choose_spec.choose_spec.choose_spec

end LocalisationData

end

