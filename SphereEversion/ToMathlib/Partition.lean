import Mathlib.Geometry.Manifold.PartitionOfUnity
import SphereEversion.ToMathlib.Geometry.Manifold.ContMDiff
import SphereEversion.ToMathlib.Geometry.Manifold.Algebra.SmoothGerm
import SphereEversion.ToMathlib.Geometry.Manifold.Algebra.LieGroup
import SphereEversion.ToMathlib.Analysis.Convex.Basic
import SphereEversion.ToMathlib.Topology.Support
import SphereEversion.ToMathlib.Topology.LocallyFinite
import SphereEversion.ToMathlib.Topology.PartitionOfUnity

noncomputable section

open scoped Topology Filter Manifold BigOperators

open Set Function Filter

section

variable {ι : Type _} {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type _}
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type _} [TopologicalSpace M]
  [ChartedSpace H M] {s : Set M} {F : Type _} [NormedAddCommGroup F] [NormedSpace ℝ F]

variable [FiniteDimensional ℝ E] [SmoothManifoldWithCorners I M]

theorem SmoothPartitionOfUnity.cont_diff_at_sum (ρ : SmoothPartitionOfUnity ι I M s) {n : ℕ∞}
    {x₀ : M} {φ : ι → M → F} (hφ : ∀ i, x₀ ∈ tsupport (ρ i) → ContMDiffAt I 𝓘(ℝ, F) n (φ i) x₀) :
    ContMDiffAt I 𝓘(ℝ, F) n (fun x => ∑ᶠ i, ρ i x • φ i x) x₀ :=
  by
  refine' contMDiffAt_finsum (ρ.locally_finite.smul_left _) fun i => _
  by_cases hx : x₀ ∈ tsupport (ρ i)
  · exact ContMDiffAt.smul ((ρ i).smooth.of_le le_top).contMDiffAt (hφ i hx)
  · exact contMDiffAt_of_not_mem (compl_subset_compl.mpr (tsupport_smul_left (ρ i) (φ i)) hx) n

theorem SmoothPartitionOfUnity.contDiffAt_sum' {s : Set E}
    (ρ : SmoothPartitionOfUnity ι 𝓘(ℝ, E) E s) {n : ℕ∞} {x₀ : E} {φ : ι → E → F}
    (hφ : ∀ i, x₀ ∈ tsupport (ρ i) → ContDiffAt ℝ n (φ i) x₀) :
    ContDiffAt ℝ n (fun x => ∑ᶠ i, ρ i x • φ i x) x₀ :=
  by
  rw [← contMDiffAt_iff_contDiffAt]
  apply ρ.cont_diff_at_sum
  intro i
  rw [contMDiffAt_iff_contDiffAt]
  exact hφ i

end

section

variable {ι : Type _}

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {H : Type _}
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type _} [TopologicalSpace M]
  [ChartedSpace H M] [SmoothManifoldWithCorners I M] [SigmaCompactSpace M] [T2Space M]

section

variable {F : Type _} [AddCommGroup F] [Module ℝ F]

theorem SmoothPartitionOfUnity.finite_tsupport {s : Set M} (ρ : SmoothPartitionOfUnity ι I M s)
    (x : M) : {i | x ∈ tsupport (ρ i)}.Finite :=
  by
  rcases ρ.locally_finite x with ⟨t, t_in, ht⟩
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
    (ρ : SmoothPartitionOfUnity ι I M s) (x : M) : ∀ᶠ y in 𝓝 x, ρ.fintsupport y ⊆ ρ.fintsupport x :=
  by
  apply (ρ.locally_finite.closure.eventually_subset (fun _ => isClosed_closure) x).mono
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
    (ρ : SmoothPartitionOfUnity ι I M s) (x : M) : ρ.finsupport x ⊆ ρ.fintsupport x :=
  by
  rintro i hi
  rw [ρ.mem_fintsupport_iff]
  apply subset_closure
  exact (ρ.to_partition_of_unity.mem_finsupport x).mp hi

theorem SmoothPartitionOfUnity.eventually_finsupport_subset {s : Set M}
    (ρ : SmoothPartitionOfUnity ι I M s) (x : M) : ∀ᶠ y in 𝓝 x, ρ.finsupport y ⊆ ρ.fintsupport x :=
  by
  apply (ρ.eventually_fintsupport_subset x).mono
  exact fun y hy => (ρ.finsupport_subset_fintsupport y).trans hy

/- ./././Mathport/Syntax/Translate/Expr.lean:336:4: warning: unsupported (TODO): `[tacs] -/
/-- Try to prove something is in the interior of a set by using this set is `univ`. -/
unsafe def tactic.mem_interior_univ : tactic Unit :=
  sorry

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic tactic.mem_interior_univ -/
theorem SmoothPartitionOfUnity.sum_germ {s : Set M} (ρ : SmoothPartitionOfUnity ι I M s) {x : M}
    (hx : x ∈ interior s := by
      run_tac
        tactic.mem_interior_univ) :
    ∑ i in ρ.fintsupport x, (ρ i : smoothGerm I x) = 1 :=
  by
  have : ∀ᶠ y in 𝓝 x, y ∈ interior s := is_open_interior.eventually_mem hx
  have : ∀ᶠ y in 𝓝 x, (⇑(∑ i : ι in ρ.fintsupport x, ρ i)) y = 1 :=
    by
    apply ((ρ.eventually_finsupport_subset x).And this).mono
    rintro y ⟨hy, hy'⟩
    rw [SmoothMap.coe_sum, Finset.sum_apply]
    apply ρ.to_partition_of_unity.sum_finsupport' (interior_subset hy') hy
  rw [← smoothGerm.coe_sum]
  exact smoothGerm.coe_eq_coe _ _ 1 this

def SmoothPartitionOfUnity.combine {s : Set M} (ρ : SmoothPartitionOfUnity ι I M s) (φ : ι → M → F)
    (x : M) : F :=
  ∑ᶠ i, ρ i x • φ i x

attribute [simps] SmoothPartitionOfUnity.toPartitionOfUnity

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic tactic.mem_interior_univ -/
theorem SmoothPartitionOfUnity.germ_combine_mem {s : Set M} (ρ : SmoothPartitionOfUnity ι I M s)
    (φ : ι → M → F) {x : M}
    (hx : x ∈ interior s := by
      run_tac
        tactic.mem_interior_univ) :
    (ρ.combine φ : Germ (𝓝 x) F) ∈
      reallyConvexHull (smoothGerm I x) ((fun i => (φ i : Germ (𝓝 x) F)) '' ρ.fintsupport x) :=
  by
  change x ∈ interior s at hx
  have :
    (ρ.combine φ : germ (𝓝 x) F) =
      ∑ i in ρ.fintsupport x, (ρ i : smoothGerm I x) • (φ i : germ (𝓝 x) F) :=
    by
    suffices (ρ.combine φ : germ (𝓝 x) F) = ↑(∑ i in ρ.fintsupport x, ((ρ i : M → ℝ) • φ i : M → F))
      by rw [this, Germ.coe_sum]; rfl
    rw [germ.coe_eq]
    filter_upwards [ρ.eventually_finsupport_subset x] with x' hx'
    simp_rw [SmoothPartitionOfUnity.combine, Finset.sum_apply, Pi.smul_apply']
    rw [finsum_eq_sum_of_support_subset]
    refine' subset_trans _ (Finset.coe_subset.mpr hx')
    rw [SmoothPartitionOfUnity.finsupport, PartitionOfUnity.finsupport, finite.coe_to_finset]
    apply support_smul_subset_left
  rw [this]
  apply sum_mem_reallyConvexHull
  · intro i hi
    apply eventually_of_forall
    apply ρ.nonneg
  · apply ρ.sum_germ hx
  · intro i hi
    exact mem_image_of_mem _ hi

end

end

