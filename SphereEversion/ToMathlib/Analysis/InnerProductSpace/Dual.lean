import Mathbin.Analysis.InnerProductSpace.Dual
import Project.ToMathlib.Analysis.InnerProductSpace.Projection

open scoped RealInnerProductSpace

open Submodule InnerProductSpace

open LinearMap (ker)

variable {E : Type _} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- ignore the next line which is fixing a pretty-printer bug
local notation "Δ" v:55 => Submodule.span ℝ {v}

local notation "Δ" v:55 => Submodule.span ℝ ({v} : Set E)

-- ignore the next line which is fixing a pretty-printer bug
local notation "{." x "}ᗮ" => (Submodule.span ℝ {x})ᗮ

local notation "{." x "}ᗮ" => (Submodule.span ℝ ({x} : Set E))ᗮ

local notation "pr[" x "]ᗮ" => orthogonalProjection (Submodule.span ℝ {x})ᗮ

theorem orthogonal_span_toDual_symm (π : E →L[ℝ] ℝ) :
    {.(InnerProductSpace.toDual ℝ E).symm π}ᗮ = ker π :=
  by
  ext x
  suffices (∀ a : ℝ, ⟪a • (to_dual ℝ E).symm π, x⟫ = 0) ↔ π x = 0
    by
    simp only [orthogonal, mem_mk, Set.mem_setOf_eq, LinearMap.mem_ker, ← to_dual_symm_apply]
    simpa only [mem_span_singleton, forall_exists_index, forall_apply_eq_imp_iff',
      to_dual_symm_apply]
  constructor
  · intro h
    simpa using h 1
  · intro h a
    rw [inner_smul_left]
    simp [h]

