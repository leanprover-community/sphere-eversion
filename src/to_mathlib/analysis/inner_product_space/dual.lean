import analysis.inner_product_space.dual

import to_mathlib.analysis.inner_product_space.projection

open_locale real_inner_product_space
open submodule inner_product_space linear_map (ker)

variables {E : Type*} [normed_add_comm_group E] [inner_product_space ℝ E] [complete_space E]

-- ignore the next line which is fixing a pretty-printer bug
local notation (name := line_printing_only) `Δ` v:55 := submodule.span ℝ {v}
local notation `Δ` v:55 := submodule.span ℝ ({v} : set E)
-- ignore the next line which is fixing a pretty-printer bug
local notation (name := module_span_printing_only) `{.` x `}ᗮ` := (submodule.span ℝ {x})ᗮ
local notation `{.` x `}ᗮ` := (submodule.span ℝ ({x} : set E))ᗮ
local notation `pr[`x`]ᗮ` := orthogonal_projection (submodule.span ℝ {x})ᗮ


lemma orthogonal_span_to_dual_symm (π : E →L[ℝ] ℝ) :
  {.(inner_product_space.to_dual ℝ E).symm π}ᗮ = ker π :=
begin
  ext x,
  suffices : (∀ (a : ℝ), ⟪a • ((to_dual ℝ E).symm) π, x⟫ = 0) ↔ π x = 0,
  { simp only [orthogonal, mem_mk, set.mem_set_of_eq, linear_map.mem_ker, ← to_dual_symm_apply],
    simpa only [mem_span_singleton, forall_exists_index, forall_apply_eq_imp_iff', to_dual_symm_apply]},

  split,
  { intros h,
    simpa using h 1 },
  { intros h a,
    rw inner_smul_left,
    simp [h] }
end
