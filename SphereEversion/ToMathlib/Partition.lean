module

public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import SphereEversion.ToMathlib.Analysis.Convex.Basic
public import SphereEversion.ToMathlib.Geometry.Manifold.Algebra.SmoothGerm

@[expose] public section

noncomputable section

open scoped Topology
open Set Function Filter

variable {ι : Type*}

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

section

variable {F : Type*} [AddCommGroup F] [Module ℝ F]

namespace SmoothPartitionOfUnity

variable {s : Set M} (ρ : SmoothPartitionOfUnity ι I M s) {x : M}

theorem sum_germ (hx : x ∈ interior s := by simp) :
    ∑ i ∈ ρ.fintsupport x, (ρ i : smoothGerm I x) = 1 := by
  have : ∀ᶠ y in 𝓝 x, y ∈ interior s := isOpen_interior.eventually_mem hx
  have : ∀ᶠ y in 𝓝 x, (⇑(∑ i ∈ ρ.fintsupport x, ρ i)) y = 1 := by
    filter_upwards [ρ.eventually_finsupport_subset x, this] with y hy hy'
    rw [SmoothMap.coe_sum, Finset.sum_apply]
    apply ρ.toPartitionOfUnity.sum_finsupport' (interior_subset hy') hy
  rw [← smoothGerm.coe_sum]
  exact smoothGerm.coe_eq_coe _ _ 1 this

def combine (ρ : SmoothPartitionOfUnity ι I M s) (φ : ι → M → F) (x : M) : F :=
  ∑ᶠ i, ρ i x • φ i x

theorem germ_combine_mem (φ : ι → M → F) (hx : x ∈ interior s := by simp) :
    (ρ.combine φ : Germ (𝓝 x) F) ∈
      reallyConvexHull (smoothGerm I x) ((fun i ↦ (φ i : Germ (𝓝 x) F)) '' ρ.fintsupport x) := by
  change x ∈ interior s at hx
  have : (ρ.combine φ : Germ (𝓝 x) F) =
      ∑ i ∈ ρ.fintsupport x, (ρ i : smoothGerm I x) • (φ i : Germ (𝓝 x) F) := by
    suffices (ρ.combine φ : Germ (𝓝 x) F) =
        ↑(∑ i ∈ ρ.fintsupport x, ((ρ i : M → ℝ) • φ i : M → F)) by
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
    filter_upwards using fun a ↦ ρ.nonneg i a

end SmoothPartitionOfUnity

end
