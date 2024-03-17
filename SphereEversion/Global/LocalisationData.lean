import Mathlib.Topology.MetricSpace.PartitionOfUnity
import SphereEversion.Global.SmoothEmbedding

noncomputable section

open scoped Manifold

open Set Metric

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [SmoothManifoldWithCorners I M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] (I' : ModelWithCorners 𝕜 E' H')
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [SmoothManifoldWithCorners I' M']

/-- Definition `def:localisation_data`. -/
structure LocalisationData (f : M → M') where
  cont : Continuous f
  ι' : Type*
  N : ℕ
  φfun : IndexType N → (E → M)
  φ : (i : IndexType N) → OpenSmoothEmbeddingMR 𝓘(𝕜, E) I (φfun i) ⊤
  ψfun : ι' → (E' → M')
  ψ : (i : ι') → OpenSmoothEmbeddingMR 𝓘(𝕜, E') I' (ψfun i) ⊤
  j : IndexType N → ι'
  h₁ : (⋃ i, φ i '' ball (0 : E) 1) = univ
  h₂ : (⋃ i', ψ i' '' ball (0 : E') 1) = univ
  h₃ : ∀ i, range (f ∘ φ i) ⊆ ψ (j i) '' ball (0 : E') 1
  h₄ : LocallyFinite fun i' ↦ range (ψ i')
  lf_φ : LocallyFinite fun i ↦ range (φ i)

namespace LocalisationData

variable {f : M → M'} {I I'} (ld : LocalisationData I I' f)

abbrev ψj : (n : IndexType ld.N) → OpenSmoothEmbeddingMR 𝓘(𝕜, E') I' (ld.ψfun (ld.j n)) ⊤ :=
  fun n ↦ ld.ψ (ld.j n)

/-- The type indexing the source charts of the given localisation data. -/
def ι (L : LocalisationData I I' f) :=
  IndexType L.N

theorem iUnion_succ' {β : Type*} (s : ld.ι → Set β) (i : IndexType ld.N) :
    (⋃ j ≤ i, s j) = (⋃ j < i, s j) ∪ s i := by
  simp only [(fun _ ↦ le_iff_lt_or_eq : ∀ j, j ≤ i ↔ j < i ∨ j = i)]
  erw [biUnion_union, biUnion_singleton]
  rfl

open Filter

end LocalisationData

end

section

open ModelWithCorners

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [SigmaCompactSpace M] [LocallyCompactSpace M] [T2Space M]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [Boundaryless I] [Nonempty M]
  [ChartedSpace H M] [SmoothManifoldWithCorners I M]
  (E' : Type*) [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] (I' : ModelWithCorners ℝ E' H') [Boundaryless I']
  {M' : Type*} [MetricSpace M'] [SigmaCompactSpace M'] [LocallyCompactSpace M']
  [Nonempty M'] [ChartedSpace H' M'] [SmoothManifoldWithCorners I' M']

variable (M')

theorem nice_atlas_target :
    ∃ n,
      ∃ ψfun : IndexType n → (E' → M'),
      ∃ ψ : (i : IndexType n) → OpenSmoothEmbeddingMR 𝓘(ℝ, E') I' (ψfun i) ⊤,
        (LocallyFinite fun i' ↦ range (ψ i')) ∧ (⋃ i', ψ i' '' ball 0 1) = univ := by
  let h := nice_atlas E' I' (fun _ : Unit ↦ isOpen_univ (X := M')) (by simp [eq_univ_iff_forall])
  choose n ψfun ψ _ hloc hunion using h
  exact ⟨n, ψfun, ψ, hloc, hunion⟩

-- TODO: need to adapt this; the unbundled design is getting *really* painful here...
/-- A collection of charts on a manifold `M'` which are smooth open embeddings with domain the whole
model space, and which cover the manifold when restricted in each case to the unit ball. -/
def targetCharts (i' : IndexType (nice_atlas_target E' I' M').choose) :
    OpenSmoothEmbedding 𝓘(ℝ, E') E' I' M' :=
  sorry --(nice_atlas_target E' I' M').choose_spec.choose i'

theorem targetCharts_cover : (⋃ i', targetCharts E' I' M' i' '' ball (0 : E') 1) = univ :=
  sorry --(nice_atlas_target E' I' M').choose_spec.choose_spec.2

variable (E) {M'}
variable {f : M → M'} (hf : Continuous f)

theorem nice_atlas_domain :
    ∃ n,
      ∃ φf : IndexType n → (E → M),
      ∃ φ : (i : IndexType n) → OpenSmoothEmbeddingMR 𝓘(ℝ, E) I (φf i) ⊤,
        (∀ i, ∃ i', range (φ i) ⊆ f ⁻¹' (targetCharts E' I' M' i' '' ball (0 : E') 1)) ∧
          (LocallyFinite fun i ↦ range (φ i)) ∧ (⋃ i, φ i '' ball 0 1) = univ :=
  -- TODO: update!
  sorry /-nice_atlas E I
    (fun i' ↦ ((targetCharts E' I' M' i').isOpenMap (ball 0 1) isOpen_ball).preimage hf)
    (by rw [← preimage_iUnion, targetCharts_cover, preimage_univ]) -/

/-- Lemma `lem:ex_localisation`
  Any continuous map between manifolds has some localisation data. -/
def stdLocalisationData : LocalisationData I I' f where
  cont := hf
  N := sorry --(nice_atlas_domain E I E' I' hf).choose
  ι' := IndexType (nice_atlas_target E' I' M').choose
  φfun := sorry
  φ := sorry --(nice_atlas_domain E I E' I' hf).choose_spec.choose
  ψ := sorry -- targetCharts E' I' M'
  j i := sorry --((nice_atlas_domain E I E' I' hf).choose_spec.choose_spec.1 i).choose
  h₁ := sorry --(nice_atlas_domain E I E' I' hf).choose_spec.choose_spec.2.2
  h₂ := targetCharts_cover E' I' M'
  h₃ i := by
    rw [range_comp]
    rintro - ⟨y, hy, rfl⟩
    sorry --exact ((nice_atlas_domain E I E' I' hf).choose_spec.choose_spec.1 i).choose_spec hy
  h₄ := sorry --(nice_atlas_target E' I' M').choose_spec.choose_spec.1
  lf_φ := sorry --(nice_atlas_domain E I E' I' hf).choose_spec.choose_spec.2.1

variable {E E' I I'}

/-- Lemma `lem:localisation_stability`. -/
theorem localisation_stability {f : M → M'} (ld : LocalisationData I I' f) :
    ∃ (ε : M → ℝ) (_hε : ∀ m, 0 < ε m) (_hε' : Continuous ε),
      ∀ (g : M → M') (_hg : ∀ m, dist (g m) (f m) < ε m) (i), range (g ∘ ld.φ i) ⊆ range (ld.ψj i) := by
  let K : ld.ι' → Set M' := fun i ↦ ld.ψ i '' closedBall 0 1
  let U : ld.ι' → Set M' := fun i ↦ range <| ld.ψ i
  have hK : ∀ i, IsClosed (K i) := fun i ↦
    IsCompact.isClosed (IsCompact.image (isCompact_closedBall 0 1) (ld.ψ i).continuous)
  have hK' : LocallyFinite K := ld.h₄.subset fun i ↦ image_subset_range (ld.ψ i) (closedBall 0 1)
  have hU : ∀ i, IsOpen (U i) := fun i ↦ (ld.ψ i).isOpen_range
  have hKU : ∀ i, K i ⊆ U i := fun i ↦ image_subset_range _ _
  obtain ⟨δ, hδ₀, hδ₁⟩ := exists_continuous_real_forall_closedBall_subset hK hU hKU hK'
  have := ld.cont
  refine ⟨δ ∘ f, fun m ↦ hδ₀ (f m), by continuity, fun g hg i ↦ ?_⟩
  rintro - ⟨e, rfl⟩
  have hi : f (ld.φ i e) ∈ K (ld.j i) :=
    image_subset _ ball_subset_closedBall (ld.h₃ i (mem_range_self e))
  exact hδ₁ (ld.j i) (f <| ld.φ i e) hi (le_of_lt (hg _))

namespace LocalisationData

protected def ε (ld : LocalisationData I I' f) : M → ℝ :=
  (localisation_stability ld).choose

theorem ε_pos (ld : LocalisationData I I' f) : ∀ m, 0 < ld.ε m :=
  (localisation_stability ld).choose_spec.choose

theorem ε_cont (ld : LocalisationData I I' f) : Continuous ld.ε :=
  (localisation_stability ld).choose_spec.choose_spec.choose

theorem ε_spec (ld : LocalisationData I I' f) :
    ∀ (g : M → M') (_hg : ∀ m, dist (g m) (f m) < ld.ε m) (i : ld.ι),
      range (g ∘ ld.φ i) ⊆ range (ld.ψj i) :=
  (localisation_stability ld).choose_spec.choose_spec.choose_spec

variable (I I')

theorem _root_.exists_stability_dist {f : M → M'} (hf : Continuous f) :
    ∃ ε : M → ℝ, (∀ m, 0 < ε m) ∧ Continuous ε ∧
      ∀ x : M,
        ∃ φfun : E → M, ∃ φ : OpenSmoothEmbeddingMR 𝓘(ℝ, E) I φfun ⊤,
        ∃ ψfun : E' → M', ∃ ψ : OpenSmoothEmbeddingMR 𝓘(ℝ, E') I' ψfun ⊤,
          x ∈ range φ ∧
          ∀ (g : M → M'), (∀ m, dist (g m) (f m) < ε m) → range (g ∘ φ) ⊆ range ψ := by
  let L := stdLocalisationData E I E' I' hf
  use L.ε, L.ε_pos, L.ε_cont
  intro x
  rcases mem_iUnion.mp <| eq_univ_iff_forall.mp L.h₁ x with ⟨i, hi⟩
  use L.φfun i, L.φ i, L.ψ (L.j i), L.ψj i, mem_range_of_mem_image (φ L i) _ hi
  have := L.ε_spec
  tauto

end LocalisationData

end
