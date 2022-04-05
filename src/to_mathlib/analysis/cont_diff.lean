import analysis.calculus.inverse
import analysis.calculus.cont_diff

import to_mathlib.analysis.calculus

noncomputable theory

open_locale topological_space filter
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

lemma continuous_linear_equiv.continuous_lower_triangular {X : Type*} [topological_space X]
  {A : X → M₁ ≃L[𝕜] M₃} {C : X → M₁ →L[𝕜] M₄} {D : X → M₂ ≃L[𝕜] M₄}
  (hA : continuous (λ x, (A x : M₁ →L[𝕜] M₃))) (hC : continuous C)
  (hD : continuous (λ x, (D x : M₂ →L[𝕜] M₄))) :
  continuous (λ x, ((A x).lower_triangular (C x) (D x) : (M₁ × M₂) →L[𝕜] (M₃ × M₄))) :=
begin
  change continuous (λ x, (((A x: M₁ →L[𝕜] M₃).comp (fst 𝕜 M₁ M₂)).prod ((C x).coprod $ D x))),
  sorry
end

end

section
variables (𝕜 : Type*) [nondiscrete_normed_field 𝕜]
  {E : Type*} [normed_group E] [normed_space 𝕜 E]
  {F : Type*} [normed_group F] [normed_space 𝕜 F]
  {G : Type*} [normed_group G] [normed_space 𝕜 G]
  {n : with_top ℕ}

-- The next two definitions aren't used in the end, but they may still go to mathlib
def strict_differentiable_at (f : E → F) (x) :=
∃ φ : E →L[𝕜] F, has_strict_fderiv_at f φ x

def strict_differentiable (f : E → F) :=
∀ x, strict_differentiable_at 𝕜 f x

variables {𝕜}

lemma strict_differentiable_at.differentiable_at {f : E → F} {x : E}
  (h : strict_differentiable_at 𝕜 f x) : differentiable_at 𝕜 f x :=
exists.elim h (λ φ hφ, ⟨φ, hφ.has_fderiv_at⟩)

lemma differentiable_at.has_fderiv_at_coprod {f : E × F → G} {x : E × F}
  (hf : differentiable_at 𝕜 f x) {φ : E →L[𝕜] G} {ψ : F →L[𝕜] G}
  (hφ : has_fderiv_at (λ p, f (p, x.2)) φ x.1) (hψ : has_fderiv_at (λ q, f (x.1, q)) ψ x.2) :
  has_fderiv_at f (φ.coprod ψ) x :=
begin

  sorry
end

variables [complete_space E]

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

lemma equiv.continuous_symm_of_cont_diff (φ : E ≃ F) {Dφ : E → E ≃L[𝕜] F}
  (hφ : ∀ x, has_strict_fderiv_at φ (Dφ x : E →L[𝕜] F) x) :
  continuous φ.symm :=
begin
  rw continuous_iff_continuous_at,
  intros x,
  let y := φ.symm x,
  let g := (hφ y).local_inverse φ (Dφ y) y,
  rw ← φ.apply_symm_apply x,
  have ev_eq : g =ᶠ[𝓝 (φ y)] φ.symm,
  { apply (hφ y).eventually_right_inverse.mono,
    rintros x (hx : φ (g x) = x),
    exact (equiv.eq_symm_apply φ).mpr hx },
  apply continuous_at.congr _ ev_eq,
  apply (hφ y).local_inverse_continuous_at
end

def equiv.to_homeomorph_of_cont_diff (φ : E ≃ F) {Dφ : E → E ≃L[𝕜] F}
  (hφ : ∀ x, has_strict_fderiv_at φ (Dφ x : E →L[𝕜] F) x) : E ≃ₜ F :=
{ continuous_to_fun := differentiable.continuous (λ x, (hφ x).differentiable_at),
  continuous_inv_fun := φ.continuous_symm_of_cont_diff hφ,
  ..φ}

end

section
variables (𝕜 : Type*) [is_R_or_C 𝕜]
  {E : Type*} [normed_group E] [normed_space 𝕜 E]
  {F : Type*} [normed_group F] [normed_space 𝕜 F]
  {G : Type*} [normed_group G] [normed_space 𝕜 G]
  {n : with_top ℕ}


local notation `∂₁` := partial_fderiv_fst 𝕜
local notation `∂₂` := partial_fderiv_snd 𝕜

lemma cont_diff_parametric_symm [complete_space E] [complete_space F]
  {f : E → F ≃ₜ G} {f' : E → F → F ≃L[𝕜] G}
  (hf : cont_diff 𝕜 ⊤ (λ p : E × F, f p.1 p.2))
  (hf' : ∀ x y, ∂₂ (λ x y, f x y) x y = f' x y) :
  cont_diff 𝕜 ⊤ (λ p : E × G, (f p.1).symm p.2) :=
begin
  let φ₀ : (E × F) ≃ (E × G) :=
  { to_fun := λ p : E × F, (p.1, f p.1 p.2),
    inv_fun := λ p : E × G, (p.1, (f p.1).symm p.2),
    left_inv := λ x, by simp,
    right_inv := λ x, by simp },
  let ff := λ x y, f x y,
  have hff : cont_diff 𝕜 ⊤ (uncurry ff) := hf,
  let d₁f := ∂₁ ff,
  let Dφ : E × F → (E × F) ≃L[𝕜] E × G :=
    λ x, (continuous_linear_equiv.refl 𝕜 E).lower_triangular (d₁f x.1 x.2) (f' x.1 x.2),
  let Dφ' : E × F → (E × F) →L[𝕜] E × G := λ x, Dφ x,
  have hderiv : ∀ (x : E × F), has_strict_fderiv_at φ₀ (Dφ' x) x,
  { rintros p,
    apply has_strict_fderiv_at_of_has_fderiv_at_of_continuous_at,
    { apply filter.eventually_of_forall,
      rintros ⟨x, y⟩,
      apply has_fderiv_at.prod,
      { simp only [continuous_linear_equiv.coe_refl, continuous_linear_map.id_comp,
        has_fderiv_at_fst] },
      have diff : differentiable 𝕜 (uncurry $ λ x y, f x y) := hf.differentiable le_top,
      apply differentiable_at.has_fderiv_at_coprod,
      { apply (hf.differentiable le_top) },
      { dsimp [d₁f],
        exact diff.differentiable_at.has_fderiv_at_partial_fst },
      { rw ← hf' x y,
        dsimp,
        exact diff.differentiable_at.has_fderiv_at_partial_snd } },
    { apply continuous.continuous_at,
      apply continuous_linear_equiv.continuous_lower_triangular,
      { exact continuous_const },
      { exact hff.cont_diff_top_partial_fst.continuous },
      { simp_rw ← hf',
        exact hff.cont_diff_top_partial_snd.continuous } } },
  let φ := φ₀.to_homeomorph_of_cont_diff hderiv,
  exact cont_diff_snd.comp (φ.cont_diff_symm (λ x, (hderiv x).has_fderiv_at)
    (cont_diff_fst.prod hf)),
end

end
