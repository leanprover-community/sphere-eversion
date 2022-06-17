import analysis.calculus.inverse
import analysis.calculus.cont_diff

import to_mathlib.analysis.calculus
import to_mathlib.analysis.normed_space.operator_norm

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
(hA.compL continuous_const).prodL (hC.coprodL hD)

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

-- PR to linear_algebra.prod
@[simp]
lemma linear_map.coprod_comp_inl_inr {R : Type*} {M : Type*} {M₂ : Type*} {M₃ : Type*} [semiring R]
  [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃] [module R M]
  [module R M₂] [module R M₃] (f : M × M₂ →ₗ[R] M₃) :
  (f.comp (linear_map.inl R M M₂)).coprod (f.comp (linear_map.inr R M M₂)) = f :=
by rw [← linear_map.comp_coprod, linear_map.coprod_inl_inr, linear_map.comp_id]

-- PR to topology.algebra.module.basic
@[simp]
lemma continuous_linear_map.coprod_comp_inl_inr {R₁ : Type*} [semiring R₁] {M₁ : Type*} [topological_space M₁]
  [add_comm_monoid M₁] {M₂ : Type*} [topological_space M₂] [add_comm_monoid M₂]
  {M₃ : Type*} [topological_space M₃] [add_comm_monoid M₃] [module R₁ M₁]
  [module R₁ M₂] [module R₁ M₃] [has_continuous_add M₃] (f : M₁ × M₂ →L[R₁] M₃) :
  (f.comp (continuous_linear_map.inl R₁ M₁ M₂)).coprod (f.comp (continuous_linear_map.inr R₁ M₁ M₂)) = f :=
continuous_linear_map.coe_injective (f : M₁ × M₂ →ₗ[R₁] M₃).coprod_comp_inl_inr

lemma differentiable_at.has_fderiv_at_coprod_partial {f : E → F → G} {x : E} {y : F}
  (hf : differentiable_at 𝕜 (uncurry f) (x, y)) :
  has_fderiv_at (uncurry f)
                ((partial_fderiv_fst 𝕜 f x y).coprod (partial_fderiv_snd 𝕜 f x y)) (x, y) :=
begin
  rcases hf with ⟨θ, hθ⟩,
  rwa [fderiv_partial_fst hθ, fderiv_partial_snd hθ, θ.coprod_comp_inl_inr]
end

lemma differentiable_at.has_fderiv_at_coprod {f : E → F → G} {x : E} {y : F}
  (hf : differentiable_at 𝕜 (uncurry f) (x, y)) {φ : E →L[𝕜] G} {ψ : F →L[𝕜] G}
  (hφ : has_fderiv_at (λ p, f p y) φ x) (hψ : has_fderiv_at (f x) ψ y) :
  has_fderiv_at (uncurry f) (φ.coprod ψ) (x, y) :=
begin
  rw [hφ.unique hf.has_fderiv_at_partial_fst, hψ.unique hf.has_fderiv_at_partial_snd],
  exact hf.has_fderiv_at_coprod_partial
end

variables [complete_space E]

lemma homeomorph.cont_diff_at_symm (f : homeomorph E F) {f₀' : E ≃L[𝕜] F} {a : F}
  (hf' : has_fderiv_at f (f₀' : E →L[𝕜] F) (f.symm a)) (hf : cont_diff_at 𝕜 n f (f.symm a)) :
  cont_diff_at 𝕜 n (f.symm) a :=
f.to_local_homeomorph.cont_diff_at_symm trivial hf' hf

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
variables {𝕜 : Type*} [is_R_or_C 𝕜]
  {E : Type*} [normed_group E] [normed_space 𝕜 E]
  {F : Type*} [normed_group F] [normed_space 𝕜 F]
  {G : Type*} [normed_group G] [normed_space 𝕜 G]
  {n : with_top ℕ}


local notation `∂₁` := partial_fderiv_fst 𝕜
local notation `∂₂` := partial_fderiv_snd 𝕜

lemma cont_diff_parametric_symm [complete_space E] [complete_space F]
  {f : E → F ≃ G} {f' : E → F → F ≃L[𝕜] G}
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
      rw show (λ (x : E × F), (f x.fst) x.snd) = uncurry (λ x y, f x y), by { ext, refl },
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

section
variables {E : Type*} [normed_group E] [normed_space ℝ E] [complete_space E]

lemma cont_diff_parametric_symm_of_deriv_pos {f : E → ℝ → ℝ} (hf : cont_diff ℝ ⊤ ↿f)
  (hderiv : ∀ x t, partial_deriv_snd f x t > 0) (hsurj : ∀ x, surjective $ f x) :
  cont_diff ℝ ⊤  (λ p : E × ℝ, (strict_mono.order_iso_of_surjective (f p.1)
                                (strict_mono_of_deriv_pos $ hderiv p.1) (hsurj p.1)).symm p.2) :=
begin
  have hmono := λ x, strict_mono_of_deriv_pos (hderiv x),
  let F := λ x, (strict_mono.order_iso_of_surjective (f x) (hmono x) $ hsurj x).to_equiv,
  change cont_diff ℝ ⊤ (λ (p : E × ℝ), (F p.1).symm p.snd),
  refine cont_diff_parametric_symm hf _,
  exact λ x t, continuous_linear_equiv.units_equiv_aut ℝ (units.mk0 (deriv (f x) t) $ ne_of_gt (hderiv x t)) ,
  intros x t,
  suffices : partial_fderiv_snd ℝ f x t 1 = partial_deriv_snd f x t,
  { ext v,
    simpa only [rel_iso.coe_fn_to_equiv, continuous_linear_equiv.coe_coe,
      continuous_linear_equiv.units_equiv_aut_apply, units.coe_mk0, one_mul] },
  apply partial_fderiv_snd_one
end

end
