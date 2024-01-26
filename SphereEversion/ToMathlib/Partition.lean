import Mathlib.Geometry.Manifold.PartitionOfUnity
import SphereEversion.ToMathlib.Analysis.Convex.Basic
import SphereEversion.ToMathlib.Geometry.Manifold.Algebra.SmoothGerm

noncomputable section

open scoped Topology Filter Manifold BigOperators

open Set Function Filter

section -- unused, but might be nice API: PRed in #10019 (depending on #10020)

variable {ι : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*}
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] {s : Set M} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

variable [FiniteDimensional ℝ E] [SmoothManifoldWithCorners I M]

theorem SmoothPartitionOfUnity.contMDiffAt_sum (ρ : SmoothPartitionOfUnity ι I M s) {n : ℕ∞}
    {x₀ : M} {φ : ι → M → F} (hφ : ∀ i, x₀ ∈ tsupport (ρ i) → ContMDiffAt I 𝓘(ℝ, F) n (φ i) x₀) :
    ContMDiffAt I 𝓘(ℝ, F) n (fun x ↦ ∑ᶠ i, ρ i x • φ i x) x₀ := by
  refine contMDiffAt_finsum (ρ.locallyFinite.smul_left _) fun i ↦ ?_
  by_cases hx : x₀ ∈ tsupport (ρ i)
  · exact ContMDiffAt.smul ((ρ i).smooth.of_le le_top).contMDiffAt (hφ i hx)
  · exact contMDiffAt_of_not_mem (compl_subset_compl.mpr (tsupport_smul_subset_left (ρ i) (φ i)) hx) n

theorem SmoothPartitionOfUnity.contDiffAt_sum {s : Set E}
    (ρ : SmoothPartitionOfUnity ι 𝓘(ℝ, E) E s) {n : ℕ∞} {x₀ : E} {φ : ι → E → F}
    (hφ : ∀ i, x₀ ∈ tsupport (ρ i) → ContDiffAt ℝ n (φ i) x₀) :
    ContDiffAt ℝ n (fun x ↦ ∑ᶠ i, ρ i x • φ i x) x₀ := by
  simp only [← contMDiffAt_iff_contDiffAt] at *
  exact ρ.contMDiffAt_sum hφ

end

section

variable {ι : Type*}

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {H : Type*}
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [SmoothManifoldWithCorners I M] [SigmaCompactSpace M] [T2Space M]

section -- up to sum_germ, PRed in #10015 (the remainder needs smooth germs)

variable {F : Type*} [AddCommGroup F] [Module ℝ F]

namespace PartitionOfUnity

variable {s : Set M} (ρ : PartitionOfUnity ι M s) (x : M)

theorem finite_tsupport : {i | x ∈ tsupport (ρ i)}.Finite := by
  rcases ρ.locallyFinite x with ⟨t, t_in, ht⟩
  apply ht.subset
  rintro i hi
  simp only [inter_comm]
  exact mem_closure_iff_nhds.mp hi t t_in

def fintsupport : Finset ι :=
  (ρ.finite_tsupport x).toFinset

theorem mem_fintsupport_iff (i : ι) : i ∈ ρ.fintsupport x ↔ x ∈ tsupport (ρ i) :=
  Finite.mem_toFinset _

theorem eventually_fintsupport_subset : ∀ᶠ y in 𝓝 x, ρ.fintsupport y ⊆ ρ.fintsupport x := by
  apply (ρ.locallyFinite.closure.eventually_subset (fun _ ↦ isClosed_closure) x).mono
  intro y hy z hz
  rw [PartitionOfUnity.mem_fintsupport_iff] at *
  exact hy hz

end PartitionOfUnity

namespace SmoothPartitionOfUnity

variable {s : Set M} (ρ : SmoothPartitionOfUnity ι I M s) (x : M)

theorem finite_tsupport : {i | x ∈ tsupport (ρ i)}.Finite :=
  PartitionOfUnity.finite_tsupport ρ.toPartitionOfUnity _

def fintsupport {s : Set M} (ρ : SmoothPartitionOfUnity ι I M s) (x : M) :
    Finset ι :=
  (ρ.finite_tsupport x).toFinset

theorem mem_fintsupport_iff (i : ι) : i ∈ ρ.fintsupport x ↔ x ∈ tsupport (ρ i) :=
  Finite.mem_toFinset _

theorem eventually_fintsupport_subset : ∀ᶠ y in 𝓝 x, ρ.fintsupport y ⊆ ρ.fintsupport x :=
  ρ.toPartitionOfUnity.eventually_fintsupport_subset _

def finsupport {ι : Type*} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [SmoothManifoldWithCorners I M] {s} (ρ : SmoothPartitionOfUnity ι I M s) (x : M) : Finset ι :=
  ρ.toPartitionOfUnity.finsupport x

/-- Weaker version of `smooth_partition_of_unity.eventually_fintsupport_subset`. -/
theorem finsupport_subset_fintsupport : ρ.finsupport x ⊆ ρ.fintsupport x := fun i hi ↦ by
  rw [ρ.mem_fintsupport_iff]
  apply subset_closure
  exact (ρ.toPartitionOfUnity.mem_finsupport x).mp hi

theorem eventually_finsupport_subset : ∀ᶠ y in 𝓝 x, ρ.finsupport y ⊆ ρ.fintsupport x :=
  (ρ.eventually_fintsupport_subset x).mono
    fun y hy ↦ (ρ.finsupport_subset_fintsupport y).trans hy

variable {x} in
theorem sum_germ (hx : x ∈ interior s := by simp) :
    ∑ i in ρ.fintsupport x, (ρ i : smoothGerm I x) = 1 := by
  have : ∀ᶠ y in 𝓝 x, y ∈ interior s := isOpen_interior.eventually_mem hx
  have : ∀ᶠ y in 𝓝 x, (⇑(∑ i : ι in ρ.fintsupport x, ρ i)) y = 1 := by
    filter_upwards [ρ.eventually_finsupport_subset x, this] with y hy hy'
    rw [SmoothMap.coe_sum, Finset.sum_apply]
    apply ρ.toPartitionOfUnity.sum_finsupport' (interior_subset hy') hy
  rw [← smoothGerm.coe_sum]
  exact smoothGerm.coe_eq_coe _ _ 1 this

def combine (ρ : SmoothPartitionOfUnity ι I M s) (φ : ι → M → F) (x : M) : F :=
  ∑ᶠ i, ρ i x • φ i x

-- PRed to mathlib as well
-- TODO: move to Mathlib attribute [simps] SmoothPartitionOfUnity.toPartitionOfUnity

variable {x} in
theorem germ_combine_mem (φ : ι → M → F) (hx : x ∈ interior s := by simp) :
    (ρ.combine φ : Germ (𝓝 x) F) ∈
      reallyConvexHull (smoothGerm I x) ((fun i ↦ (φ i : Germ (𝓝 x) F)) '' ρ.fintsupport x) := by
  change x ∈ interior s at hx
  have : (ρ.combine φ : Germ (𝓝 x) F) =
      ∑ i in ρ.fintsupport x, (ρ i : smoothGerm I x) • (φ i : Germ (𝓝 x) F) := by
    suffices (ρ.combine φ : Germ (𝓝 x) F) = ↑(∑ i in ρ.fintsupport x, ((ρ i : M → ℝ) • φ i : M → F)) by
      rw [this, Germ.coe_sum]; rfl
    rw [Germ.coe_eq]
    filter_upwards [ρ.eventually_finsupport_subset x] with x' hx'
    simp_rw [SmoothPartitionOfUnity.combine, Finset.sum_apply, Pi.smul_apply']
    rw [finsum_eq_sum_of_support_subset]
    refine Subset.trans ?_ (Finset.coe_subset.mpr hx')
    rw [SmoothPartitionOfUnity.finsupport, PartitionOfUnity.finsupport, Finite.coe_toFinset]
    apply support_smul_subset_left
  rw [this]
  refine sum_mem_reallyConvexHull ?_ (ρ.sum_germ hx) (fun i hi ↦ mem_image_of_mem _ hi)
  · intro i _
    apply eventually_of_forall
    apply ρ.nonneg

end SmoothPartitionOfUnity

end

end
