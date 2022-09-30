/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import geometry.manifold.instances.sphere

open_locale manifold
open metric finite_dimensional function

noncomputable theory

local attribute [instance] fact_finite_dimensional_of_finrank_eq_succ

-- for `analysis.inner_product_space.calculus`
-- note the similar `has_strict_fderiv_at_norm_sq` which has stricter type-class assumptions
lemma has_fderiv_at_norm_sq {𝕜 : Type*} {E : Type*} [is_R_or_C 𝕜] [inner_product_space 𝕜 E]
  [normed_space ℝ E] :
  has_fderiv_at (λ (x : E), ∥x∥ ^ 2) (0 : E →L[ℝ] ℝ) 0 :=
begin
  simp only [sq, ← inner_self_eq_norm_mul_norm],
  convert (is_R_or_C.re_clm : 𝕜 →L[ℝ] ℝ).has_fderiv_at.comp _
    ((has_fderiv_at_id (0:E)).inner (has_fderiv_at_id (0:E))),
  ext x,
  simp,
end
