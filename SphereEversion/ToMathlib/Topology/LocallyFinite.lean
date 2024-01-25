import Mathlib.Algebra.SMulWithZero
import Mathlib.GroupTheory.GroupAction.Pi
import Mathlib.Topology.LocallyFinite

open Function Set

-- PRed in #10020
theorem LocallyFinite.smul_left {ι : Type*} {X : Type*} [TopologicalSpace X] {M : Type*}
    {R : Type*} [Zero R] [Zero M] [SMulWithZero R M]
    {s : ι → X → R} (h : LocallyFinite fun i ↦ support <| s i) (f : ι → X → M) :
    LocallyFinite fun i ↦ support (s i • f i) :=
  h.subset fun i x ↦ mt <| fun h ↦ by rw [Pi.smul_apply', h, zero_smul]

theorem LocallyFinite.smul_right {ι : Type*} {X : Type*} [TopologicalSpace X] {M : Type*}
    {R : Type*} [Zero R] [Zero M] [SMulZeroClass R M]
    {f : ι → X → M} (h : LocallyFinite fun i ↦ support <| f i) (s : ι → X → R) :
    LocallyFinite fun i ↦ support <| s i • f i :=
  h.subset fun i x ↦ mt <| fun h ↦ by rw [Pi.smul_apply', h, smul_zero]

section

variable {ι X : Type*} [TopologicalSpace X]

-- TODO: remove this; we don't want to have this lemma in mathlib.
-- See https://github.com/leanprover-community/mathlib4/pull/9813#discussion_r1455617707.
@[to_additive]
theorem LocallyFinite.exists_finset_mulSupport_eq {M : Type*} [CommMonoid M] {ρ : ι → X → M}
    (hρ : LocallyFinite fun i ↦ mulSupport <| ρ i) (x₀ : X) :
    ∃ I : Finset ι, (mulSupport fun i ↦ ρ i x₀) = I := by
  use (hρ.point_finite x₀).toFinset
  rw [Finite.coe_toFinset]
  rfl

end

open scoped Topology

open Filter

-- submitted as PR mathlib4#9813
theorem LocallyFinite.eventually_subset {ι X : Type*} [TopologicalSpace X] {s : ι → Set X}
    (hs : LocallyFinite s) (hs' : ∀ i, IsClosed (s i)) (x : X) :
    ∀ᶠ y in 𝓝 x, {i | y ∈ s i} ⊆ {i | x ∈ s i} := by
  filter_upwards [hs.iInter_compl_mem_nhds hs' x] with y hy i hi
  simp only [mem_iInter, mem_compl_iff] at hy
  exact not_imp_not.mp (hy i) hi
