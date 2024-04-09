/-
Copyright (c) 2021 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Floris van Doorn
-/
import Mathlib.Analysis.Convex.AmpleSet
import Mathlib.Analysis.NormedSpace.Connected

/-!
# Ample subsets of real vector spaces

In this file we study ample set in real vector spaces. A set is ample if all its connected
component have full convex hull. We then prove this property is invariant under a number of affine
geometric operations.

As trivial examples, the empty set and the univ set are ample. After proving those fact,
the second part of the file proves that a linear subspace with codimension at least 2 has a
ample complement. This is the crucial geometric ingredient which allows to apply convex integration
to the theory of immersions in positive codimension.

All vector spaces in the file (and more generally in this folder) are real vector spaces.

## Implementation notes

The definition of ample subset asks for a vector space structure and a topology on the ambient type
without any link between those structures, but we will only be using these for finite dimensional
vector spaces with their natural topology.
-/

/-! ## Subspaces of codimension at least 2 have ample complement -/
section Lemma213

open Set
variable {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [TopologicalAddGroup F] [ContinuousSMul ℝ F]

-- PRed in #11342
/-- Let `E` be a linear subspace in a real vector space. If `E` has codimension at
least two then its complement is ample. -/
theorem AmpleSet.of_one_lt_codim {E : Submodule ℝ F} (hcodim : 1 < Module.rank ℝ (F ⧸ E)) :
    AmpleSet (Eᶜ : Set F) := fun x hx ↦ by
  rw [E.connectedComponentIn_eq_self_of_one_lt_codim hcodim hx, eq_univ_iff_forall]
  intro y
  by_cases h : y ∈ E
  · obtain ⟨z, hz⟩ : ∃ z, z ∉ E := by
      rw [← not_forall, ← Submodule.eq_top_iff']
      rintro rfl
      simp [rank_zero_iff.2 inferInstance] at hcodim
    refine segment_subset_convexHull ?_ ?_ (mem_segment_sub_add y z) <;>
      simpa [sub_eq_add_neg, Submodule.add_mem_iff_right _ h]
  · exact subset_convexHull ℝ (Eᶜ : Set F) h

end Lemma213

open scoped Pointwise
-- PRed in #12046
/-- Affine translations of ample sets are ample. -/
theorem AmpleSet.vadd {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [ContinuousAdd E]
    {s : Set E} (h : AmpleSet s) {y : E} :
    AmpleSet (y +ᵥ s) :=
  h.image (ContinuousAffineEquiv.constVAdd ℝ E y)
