import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import SphereEversion.ToMathlib.Geometry.Manifold.Algebra.SmoothGerm
import SphereEversion.ToMathlib.Geometry.Manifold.Algebra.LieGroup
import SphereEversion.ToMathlib.Analysis.Convex.Basic
import SphereEversion.ToMathlib.Topology.Support
import SphereEversion.ToMathlib.Topology.LocallyFinite

noncomputable section

open scoped Topology Filter Manifold BigOperators

open Set Function Filter

section

variable {ι : Type _} {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type _}
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type _} [TopologicalSpace M]
  [ChartedSpace H M] {s : Set M} {F : Type _} [NormedAddCommGroup F] [NormedSpace ℝ F]

variable [FiniteDimensional ℝ E] [SmoothManifoldWithCorners I M]

theorem SmoothPartitionOfUnity.contMDiffAt_sum (ρ : SmoothPartitionOfUnity ι I M s) {n : ℕ∞}
    {x₀ : M} {φ : ι → M → F} (hφ : ∀ i, x₀ ∈ tsupport (ρ i) → ContMDiffAt I 𝓘(ℝ, F) n (φ i) x₀) :
    ContMDiffAt I 𝓘(ℝ, F) n (fun x => ∑ᶠ i, ρ i x • φ i x) x₀ := by
  refine' contMDiffAt_finsum (ρ.locallyFinite.smul_left _) fun i => _
  by_cases hx : x₀ ∈ tsupport (ρ i)
  · exact ContMDiffAt.smul ((ρ i).smooth.of_le le_top).contMDiffAt (hφ i hx)
  · exact contMDiffAt_of_not_mem (compl_subset_compl.mpr (tsupport_smul_left (ρ i) (φ i)) hx) n

theorem SmoothPartitionOfUnity.contDiffAt_sum {s : Set E}
    (ρ : SmoothPartitionOfUnity ι 𝓘(ℝ, E) E s) {n : ℕ∞} {x₀ : E} {φ : ι → E → F}
    (hφ : ∀ i, x₀ ∈ tsupport (ρ i) → ContDiffAt ℝ n (φ i) x₀) :
    ContDiffAt ℝ n (fun x => ∑ᶠ i, ρ i x • φ i x) x₀ := by
  simp only [← contMDiffAt_iff_contDiffAt] at *
  exact ρ.contMDiffAt_sum hφ

end

section

variable {ι : Type _}

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {H : Type _}
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type _} [TopologicalSpace M]
  [ChartedSpace H M] [SmoothManifoldWithCorners I M] [SigmaCompactSpace M] [T2Space M]

section

variable {F : Type _} [AddCommGroup F] [Module ℝ F]

-- TODO [Yury]: this is true for a continuous partition of unity
theorem SmoothPartitionOfUnity.finite_tsupport {s : Set M} (ρ : SmoothPartitionOfUnity ι I M s)
    (x : M) : {i | x ∈ tsupport (ρ i)}.Finite := by
  rcases ρ.locallyFinite x with ⟨t, t_in, ht⟩
  apply ht.subset
  rintro i hi
  simp only [inter_comm]
  exact mem_closure_iff_nhds.mp hi t t_in

def SmoothPartitionOfUnity.fintsupport {s : Set M} (ρ : SmoothPartitionOfUnity ι I M s) (x : M) :
    Finset ι :=
  (ρ.finite_tsupport x).toFinset

theorem SmoothPartitionOfUnity.mem_fintsupport_iff {s : Set M} (ρ : SmoothPartitionOfUnity ι I M s)
    (x : M) (i : ι) : i ∈ ρ.fintsupport x ↔ x ∈ tsupport (ρ i) :=
  Finite.mem_toFinset _

theorem SmoothPartitionOfUnity.eventually_fintsupport_subset {s : Set M}
    (ρ : SmoothPartitionOfUnity ι I M s) (x : M) :
    ∀ᶠ y in 𝓝 x, ρ.fintsupport y ⊆ ρ.fintsupport x := by
  apply (ρ.locallyFinite.closure.eventually_subset (fun _ => isClosed_closure) x).mono
  intro y hy z hz
  rw [SmoothPartitionOfUnity.mem_fintsupport_iff] at *
  exact hy hz

def SmoothPartitionOfUnity.finsupport {ι : Type _} {E : Type _} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {H : Type _} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {M : Type _} [TopologicalSpace M] [ChartedSpace H M]
    [SmoothManifoldWithCorners I M] {s} (ρ : SmoothPartitionOfUnity ι I M s) (x : M) : Finset ι :=
  ρ.toPartitionOfUnity.finsupport x

/-- Weaker version of `smooth_partition_of_unity.eventually_fintsupport_subset`. -/
theorem SmoothPartitionOfUnity.finsupport_subset_fintsupport {s : Set M}
    (ρ : SmoothPartitionOfUnity ι I M s) (x : M) :
    ρ.finsupport x ⊆ ρ.fintsupport x := fun i hi ↦ by
  rw [ρ.mem_fintsupport_iff]
  apply subset_closure
  exact (ρ.toPartitionOfUnity.mem_finsupport x).mp hi

theorem SmoothPartitionOfUnity.eventually_finsupport_subset {s : Set M}
    (ρ : SmoothPartitionOfUnity ι I M s) (x : M) :
    ∀ᶠ y in 𝓝 x, ρ.finsupport y ⊆ ρ.fintsupport x := by
  apply (ρ.eventually_fintsupport_subset x).mono
  exact fun y hy => (ρ.finsupport_subset_fintsupport y).trans hy

theorem SmoothPartitionOfUnity.sum_germ {s : Set M} (ρ : SmoothPartitionOfUnity ι I M s) {x : M}
    (hx : x ∈ interior s := by simp) :
    ∑ i in ρ.fintsupport x, (ρ i : smoothGerm I x) = 1 := by
  have : ∀ᶠ y in 𝓝 x, y ∈ interior s := isOpen_interior.eventually_mem hx
  have : ∀ᶠ y in 𝓝 x, (⇑(∑ i : ι in ρ.fintsupport x, ρ i)) y = 1 := by
    filter_upwards [ρ.eventually_finsupport_subset x, this] with y hy hy'
    rw [SmoothMap.coe_sum, Finset.sum_apply]
    apply ρ.toPartitionOfUnity.sum_finsupport' (interior_subset hy') hy
  rw [← smoothGerm.coe_sum]
  exact smoothGerm.coe_eq_coe _ _ 1 this

def SmoothPartitionOfUnity.combine {s : Set M} (ρ : SmoothPartitionOfUnity ι I M s) (φ : ι → M → F)
    (x : M) : F :=
  ∑ᶠ i, ρ i x • φ i x

-- TODO: move to Mathlib attribute [simps] SmoothPartitionOfUnity.toPartitionOfUnity

theorem SmoothPartitionOfUnity.germ_combine_mem {s : Set M} (ρ : SmoothPartitionOfUnity ι I M s)
    (φ : ι → M → F) {x : M}
    (hx : x ∈ interior s := by simp) :
    (ρ.combine φ : Germ (𝓝 x) F) ∈
      reallyConvexHull (smoothGerm I x) ((fun i => (φ i : Germ (𝓝 x) F)) '' ρ.fintsupport x) := by
  change x ∈ interior s at hx
  have : (ρ.combine φ : Germ (𝓝 x) F) =
      ∑ i in ρ.fintsupport x, (ρ i : smoothGerm I x) • (φ i : Germ (𝓝 x) F) := by
    suffices (ρ.combine φ : Germ (𝓝 x) F) = ↑(∑ i in ρ.fintsupport x, ((ρ i : M → ℝ) • φ i : M → F))
      by rw [this, Germ.coe_sum]; rfl
    rw [Germ.coe_eq]
    filter_upwards [ρ.eventually_finsupport_subset x] with x' hx'
    simp_rw [SmoothPartitionOfUnity.combine, Finset.sum_apply, Pi.smul_apply']
    rw [finsum_eq_sum_of_support_subset]
    refine' Subset.trans _ (Finset.coe_subset.mpr hx')
    rw [SmoothPartitionOfUnity.finsupport, PartitionOfUnity.finsupport, Finite.coe_toFinset]
    apply support_smul_subset_left
  rw [this]
  apply sum_mem_reallyConvexHull
  · intro i _
    apply eventually_of_forall
    apply ρ.nonneg
  · apply ρ.sum_germ hx
  · intro i hi
    exact mem_image_of_mem _ hi

end

end
