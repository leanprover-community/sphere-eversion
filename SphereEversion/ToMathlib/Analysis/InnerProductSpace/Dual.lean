import Mathlib.Analysis.InnerProductSpace.Dual
import SphereEversion.ToMathlib.Analysis.InnerProductSpace.Projection

open scoped RealInnerProductSpace

open Submodule InnerProductSpace

open LinearMap (ker)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

@[inherit_doc] local notation "Δ" => spanLine

@[inherit_doc] local notation "{." x "}ᗮ" => spanOrthogonal x

@[inherit_doc] local notation "pr[" x "]ᗮ" => projSpanOrthogonal x

theorem orthogonal_span_toDual_symm (π : E →L[ℝ] ℝ) :
    {.(InnerProductSpace.toDual ℝ E).symm π}ᗮ = ker π := by
  ext x
  suffices (∀ a : ℝ, ⟪a • (toDual ℝ E).symm π, x⟫ = 0) ↔ π x = 0 by
    simp only [orthogonal, mem_mk, LinearMap.mem_ker, ← toDual_symm_apply]
    change (∀ (u : E), u ∈ span ℝ {(LinearIsometryEquiv.symm (toDual ℝ E)) π} → inner _ u x = 0) ↔ _
    simpa
  refine ⟨fun h ↦ ?_, fun h _ ↦ ?_⟩
  · simpa using h 1
  · simp [inner_smul_left, h]
