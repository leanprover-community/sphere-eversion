import Mathlib.Algebra.SMulWithZero
import Mathlib.GroupTheory.GroupAction.Pi
import Mathlib.Topology.LocallyFinite

open Function Set

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
