import to_mathlib.analysis.calculus

import analysis.calculus.cont_diff

noncomputable theory

open function

section
universes u₁ u₂ u₃ u₄ u₅

open continuous_linear_map

variables {𝕜 : Type u₁} [nondiscrete_normed_field 𝕜]
  {M₁ : Type u₂} [normed_group M₁] [normed_space 𝕜 M₁]
  {M₂ : Type u₃} [normed_group M₂] [normed_space 𝕜 M₂]
  {M₃ : Type u₄} [normed_group M₃] [normed_space 𝕜 M₃]
  {M₄ : Type u₅} [normed_group M₄] [normed_space 𝕜 M₄]

-- The next definition won't be used here, it's practice before the next one.

/-- Defines continuous linear maps between two products by blocks:
given `(A : M₁ →L[𝕜] M₃)`, `(B : M₂ →L[𝕜] M₃)`, `(C : M₁ →L[𝕜] M₄)` and `(D : M₂ →L[𝕜] M₄)`,
construct the continuous linear map with "matrix":
A B
C D. -/
def continuous_linear_map.blocks (A : M₁ →L[𝕜] M₃) (B : M₂ →L[𝕜] M₃)
  (C : M₁ →L[𝕜] M₄) (D : M₂ →L[𝕜] M₄) : (M₁ × M₂) →L[𝕜] (M₃ × M₄) :=
(A.coprod B).prod (C.coprod D)

/-- Given `(A : M₁ ≃L[𝕜] M₃)`, `(C : M₁ →L[𝕜] M₄)` and `(D : M₂ ≃L[𝕜] M₄)`,
construct the continuous linear equiv with "matrix"
A 0
C D.
  -/
def continuous_linear_equiv.lower_triangular (A : M₁ ≃L[𝕜] M₃)
  (C : M₁ →L[𝕜] M₄) (D : M₂ ≃L[𝕜] M₄) : (M₁ × M₂) ≃L[𝕜] (M₃ × M₄) :=
continuous_linear_equiv.equiv_of_inverse (((A : M₁ →L[𝕜] M₃).comp (fst 𝕜 M₁ M₂)).prod (C.coprod D))
(((A.symm : M₃ →L[𝕜] M₁).comp (fst 𝕜 M₃ M₄)).prod
((-((D.symm : M₄ →L[𝕜] M₂).comp C).comp (A.symm : M₃ →L[𝕜] M₁)).coprod D.symm))
(λ ⟨x, y⟩, by simp only [prod_apply, coe_comp', continuous_linear_equiv.coe_coe, coe_fst', comp_app,
           coprod_apply, continuous_linear_equiv.symm_apply_apply, neg_apply,
           continuous_linear_equiv.map_add, neg_add_cancel_left])
(λ ⟨x, y⟩, by simp only [prod_apply, coe_comp', continuous_linear_equiv.coe_coe, coe_fst', comp_app,
           coprod_apply, neg_apply, continuous_linear_equiv.apply_symm_apply,
           continuous_linear_equiv.map_add, continuous_linear_equiv.map_neg, add_neg_cancel_left])

end

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {E : Type*} [normed_group E] [normed_space 𝕜 E] [complete_space E]
  {F : Type*} [normed_group F] [normed_space 𝕜 F]
  {G : Type*} [normed_group G] [normed_space 𝕜 G]
  {n : with_top ℕ}

lemma homeomorph.cont_diff_at_symm (f : homeomorph E F) {f₀' : E ≃L[𝕜] F} {a : F}
  (hf' : has_fderiv_at f (f₀' : E →L[𝕜] F) (f.symm a)) (hf : cont_diff_at 𝕜 n f (f.symm a)) :
  cont_diff_at 𝕜 n (f.symm) a :=
f.to_local_homeomorph.cont_diff_at_symm trivial hf' hf

/-- If a homeomorphism `f` is continuously differentiable and its (first) derivative is everywhere
invertible then `f.symm` is also continuously differentiable. -/
lemma homeomorph.cont_diff_symm (f : homeomorph E F) {f' : E → E ≃L[𝕜] F}
  (hf' : ∀ x, has_fderiv_at f (f' x : E →L[𝕜] F) x) (hf : cont_diff 𝕜 n f) :
  cont_diff 𝕜 n (f.symm) :=
cont_diff_iff_cont_diff_at.mpr $ λ x, f.cont_diff_at_symm (hf' $ f.symm x) hf.cont_diff_at

lemma cont_diff_parametric_symm [complete_space F] {f : E → F ≃ₜ G} {f' : E → F → F ≃L[𝕜] G}
  (hf' : ∀ x y, has_fderiv_at (f x) (f' x y : F →L[𝕜] G) y)
  (hf : cont_diff 𝕜 n (λ p : E × F, f p.1 p.2)) :
  cont_diff 𝕜 n (λ p : E × G, (f p.1).symm p.2) :=
begin
  let φ : (E × F) ≃ₜ (E × G) :=
  { to_fun := λ p : E × F, (p.1, f p.1 p.2),
    inv_fun := λ p : E × G, (p.1, (f p.1).symm p.2),
    left_inv := sorry,
    right_inv := sorry,
    continuous_to_fun := sorry,
    continuous_inv_fun := sorry },
  let d₁f := partial_fderiv_fst 𝕜 (λ x y, f x y),
  let Dφ : E × F → (E × F) ≃L[𝕜] E × G :=
    λ x, (continuous_linear_equiv.refl 𝕜 E).lower_triangular (d₁f x.1 x.2) (f' x.1 x.2),
  have hderiv : ∀ (x : E × F), has_fderiv_at φ (Dφ x : (E × F) →L[𝕜] E × G) x,
  { rintros ⟨x, y⟩,
    dsimp [φ, Dφ],
    apply has_fderiv_at.prod,
    { simp only [continuous_linear_equiv.coe_refl, continuous_linear_map.id_comp,
      has_fderiv_at_fst] },
    sorry },
  exact cont_diff_snd.comp (φ.cont_diff_symm hderiv (cont_diff_fst.prod hf))
end
