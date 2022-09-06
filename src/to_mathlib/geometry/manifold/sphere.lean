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

variables {E : Type*} [inner_product_space ℝ E]

lemma has_fderiv_at_stereo_inv_fun_aux (v : E) :
  has_fderiv_at (stereo_inv_fun_aux v) (continuous_linear_map.id ℝ E) 0 :=
begin
  have h₀ : has_fderiv_at (λ w : E, ∥w∥ ^ 2) (0 : E →L[ℝ] ℝ) 0 := has_fderiv_at_norm_sq,
  have h₁ : has_fderiv_at (λ w : E, (∥w∥ ^ 2 + 4)⁻¹) (0 : E →L[ℝ] ℝ) 0,
  { convert (has_fderiv_at_inv _).comp _ (h₀.add (has_fderiv_at_const 4 0)); simp },
  have h₂ : has_fderiv_at (λ w, (4:ℝ) • w + (∥w∥ ^ 2 - 4) • v)
    ((4:ℝ) • continuous_linear_map.id ℝ E) 0,
  { convert ((has_fderiv_at_const (4:ℝ) 0).smul (has_fderiv_at_id 0)).add
      ((h₀.sub (has_fderiv_at_const (4:ℝ) 0)).smul (has_fderiv_at_const v 0)),
    ext w,
    simp, },
  convert h₁.smul h₂,
  ext w,
  simp,
end

lemma has_fderiv_at_stereo_inv_fun_aux_comp_coe (v : E) :
  has_fderiv_at (stereo_inv_fun_aux v ∘ (coe : (ℝ ∙ v)ᗮ → E)) (ℝ ∙ v)ᗮ.subtypeL 0 :=
begin
  have : has_fderiv_at
    (stereo_inv_fun_aux v)
    (continuous_linear_map.id ℝ E)
    ((ℝ ∙ v)ᗮ.subtypeL 0) :=
    has_fderiv_at_stereo_inv_fun_aux v,
  convert this.comp (0 : (ℝ ∙ v)ᗮ) (by apply continuous_linear_map.has_fderiv_at),
end

variables {n : ℕ} [fact (finrank ℝ E = n + 1)]

include n
variables (n)

@[simp] lemma stereographic_apply_neg (v : sphere (0:E) 1) :
  stereographic (norm_eq_of_mem_sphere v) (-v) = 0 :=
by simp [stereographic_apply, orthogonal_projection_orthogonal_complement_singleton_eq_zero]

@[simp] lemma stereographic_neg_apply (v : sphere (0:E) 1) :
  stereographic (norm_eq_of_mem_sphere (-v)) v = 0 :=
begin
  convert stereographic_apply_neg n (-v),
  ext1,
  simp,
end

variables {n}

lemma range_mfderiv_coe_sphere (v : sphere (0:E) 1) :
  (mfderiv (𝓡 n) 𝓘(ℝ, E) (coe : sphere (0:E) 1 → E) v : tangent_space (𝓡 n) v →L[ℝ] E).range
  = (ℝ ∙ (v:E))ᗮ :=
begin
  rw ((cont_mdiff_coe_sphere v).mdifferentiable_at le_top).mfderiv,
  simp only [chart_at, stereographic', stereographic_neg_apply n, fderiv_within_univ,
    linear_isometry_equiv.to_homeomorph_symm, linear_isometry_equiv.coe_to_homeomorph,
    linear_isometry_equiv.map_zero] with mfld_simps,
  let U :=
    (orthonormal_basis.from_orthogonal_span_singleton n (ne_zero_of_mem_unit_sphere (-v))).repr,
  change (fderiv ℝ ((stereo_inv_fun_aux (-v : E) ∘ coe) ∘ U.symm) 0).range = (ℝ ∙ (v:E))ᗮ,
  have : has_fderiv_at
      (stereo_inv_fun_aux (-v : E) ∘ (coe : (ℝ ∙ (↑(-v):E))ᗮ → E))
      (ℝ ∙ (↑(-v):E))ᗮ.subtypeL
      (U.symm 0),
  { convert has_fderiv_at_stereo_inv_fun_aux_comp_coe (-v:E),
    simp },
  rw (this.comp 0 U.symm.to_continuous_linear_equiv.has_fderiv_at).fderiv,
  convert (U.symm : euclidean_space ℝ (fin n) ≃ₗᵢ[ℝ] (ℝ ∙ (↑(-v):E))ᗮ).range_comp
      (ℝ ∙ (↑(-v):E))ᗮ.subtype using 1,
  simp only [submodule.range_subtype, coe_neg_sphere],
  congr' 1,
  -- we must show `submodule.span ℝ {v} = submodule.span ℝ {-v}`
  apply submodule.span_eq_span,
  { simp only [set.singleton_subset_iff, set_like.mem_coe],
    rw ← submodule.neg_mem_iff,
    exact submodule.mem_span_singleton_self (-v) },
  { simp only [set.singleton_subset_iff, set_like.mem_coe],
    rw submodule.neg_mem_iff,
    exact submodule.mem_span_singleton_self v },
end

lemma mfderiv_coe_sphere_injective (v : sphere (0:E) 1) :
  injective (mfderiv (𝓡 n) 𝓘(ℝ, E) (coe : sphere (0:E) 1 → E) v) :=
begin
  rw ((cont_mdiff_coe_sphere v).mdifferentiable_at le_top).mfderiv,
  simp only [chart_at, stereographic', stereographic_neg_apply n, fderiv_within_univ,
    linear_isometry_equiv.to_homeomorph_symm, linear_isometry_equiv.coe_to_homeomorph,
    linear_isometry_equiv.map_zero] with mfld_simps,
  let U :=
    (orthonormal_basis.from_orthogonal_span_singleton n (ne_zero_of_mem_unit_sphere (-v))).repr,
  change injective (fderiv ℝ ((stereo_inv_fun_aux (-v : E) ∘ coe) ∘ U.symm) 0),
  have : has_fderiv_at
      (stereo_inv_fun_aux (-v : E) ∘ (coe : (ℝ ∙ (↑(-v):E))ᗮ → E))
      (ℝ ∙ (↑(-v):E))ᗮ.subtypeL
      (U.symm 0),
  { convert has_fderiv_at_stereo_inv_fun_aux_comp_coe (-v:E),
    simp },
  rw (this.comp 0 U.symm.to_continuous_linear_equiv.has_fderiv_at).fderiv,
  simpa using subtype.coe_injective,
end
