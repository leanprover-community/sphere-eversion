import Mathlib.Geometry.Manifold.PartitionOfUnity

/-! results about smooth cut-off functions: move to Geometry/Manifold/PartitionOfUnity -/
open Set Filter

open scoped Manifold Topology

-- all these lemmas have been PRed -- for manifolds, and bundled maps
-- xxx: (why) do we use unbundled versions? in any case, these lemmas follow quickly from the
-- bundled versions

section PR9873
variable {ι : Type uι} {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F] {H : Type uH}
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H) {M : Type uM} [TopologicalSpace M]
  [ChartedSpace H M] [SmoothManifoldWithCorners I M]

theorem exists_smooth_zero_one_nhds_of_isClosed [T2Space M] [NormalSpace M] [SigmaCompactSpace M]
    {s t : Set M} (hs : IsClosed s) (ht : IsClosed t) (hd : Disjoint s t) :
    ∃ f : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯, (∀ᶠ x in 𝓝ˢ s, f x = 0) ∧ (∀ᶠ x in 𝓝ˢ t, f x = 1) ∧
      ∀ x, f x ∈ Icc (0 : ℝ) 1 := sorry

theorem exists_smooth_one_nhds_of_interior [T2Space M] [NormalSpace M] [SigmaCompactSpace M]
    {s t : Set M} (hs : IsClosed s) (hd : s ⊆ interior t) :
    ∃ f : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯, (∀ᶠ x in 𝓝ˢ s, f x = 1) ∧ (∀ x, x ∉ t → f x = 0) ∧
      ∀ x, f x ∈ Icc (0 : ℝ) 1 := sorry

end PR9873

-- These are the above lemmas applied to a normed space, and with unbundled design.
theorem exists_contDiff_zero_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {s t : Set E} (hs : IsClosed s) (ht : IsClosed t) (hd : Disjoint s t) :
    ∃ f : E → ℝ, ContDiff ℝ ∞ f ∧ EqOn f 0 s ∧ EqOn f 1 t ∧ ∀ x, f x ∈ Icc (0 : ℝ) 1 :=
  let ⟨f, hfs, hft, hf01⟩ := exists_smooth_zero_one_of_closed 𝓘(ℝ, E) hs ht hd
  ⟨f, f.smooth.contDiff, hfs, hft, hf01⟩

theorem exists_contDiff_zero_one_nhds {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {s t : Set E} (hs : IsClosed s) (ht : IsClosed t) (hd : Disjoint s t) :
    ∃ f : E → ℝ, ContDiff ℝ ∞ f ∧ (∀ᶠ x in 𝓝ˢ s, f x = 0) ∧ (∀ᶠ x in 𝓝ˢ t, f x = 1) ∧
      ∀ x, f x ∈ Icc (0 : ℝ) 1 :=
  let ⟨f, hfs, hft, hf01⟩ := exists_smooth_zero_one_nhds_of_isClosed 𝓘(ℝ, E) hs ht hd
  ⟨f, f.smooth.contDiff, hfs, hft, hf01⟩

theorem exists_contDiff_one_nhds_of_interior {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {s t : Set E} (hs : IsClosed s) (hd : s ⊆ interior t) :
    ∃ f : E → ℝ, ContDiff ℝ ∞ f ∧ (∀ᶠ x in 𝓝ˢ s, f x = 1) ∧ (∀ x, x ∉ t → f x = 0) ∧
      ∀ x, f x ∈ Icc (0 : ℝ) 1 :=
  let ⟨f, hfs, hft, hf01⟩ := exists_smooth_one_nhds_of_interior 𝓘(ℝ, E) hs hd
  ⟨f, f.smooth.contDiff, hfs, hft, hf01⟩
