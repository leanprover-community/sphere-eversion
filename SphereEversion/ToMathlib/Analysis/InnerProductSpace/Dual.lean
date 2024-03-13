import Mathlib.Analysis.InnerProductSpace.Dual
import SphereEversion.ToMathlib.Analysis.InnerProductSpace.Projection

open scoped RealInnerProductSpace

open Submodule InnerProductSpace

open LinearMap (ker)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "Δ" => spanLine

local notation "{." x "}ᗮ" => spanOrthogonal x

local notation "pr[" x "]ᗮ" => projSpanOrthogonal x

theorem orthogonal_span_toDual_symm (π : E →L[ℝ] ℝ) :
    {.(InnerProductSpace.toDual ℝ E).symm π}ᗮ = ker π := by
  ext x
  suffices (∀ a : ℝ, ⟪a • (toDual ℝ E).symm π, x⟫ = 0) ↔ π x = 0 by
    simp only [orthogonal, mem_mk, Set.mem_setOf_eq, LinearMap.mem_ker, ← toDual_symm_apply]
    change (∀ (u : E), u ∈ span ℝ {(LinearIsometryEquiv.symm (toDual ℝ E)) π} → inner u x = 0) ↔ _
    simpa only [mem_span_singleton, forall_exists_index, forall_apply_eq_imp_iff, toDual_symm_apply]
  constructor
  · intro h
    simpa using h 1
  · intro h a
    rw [inner_smul_left]
    simp [h]
