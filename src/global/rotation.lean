/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import to_mathlib.analysis.cont_diff
import analysis.special_functions.trigonometric.deriv

/-! # Rotation about an axis, considered as a function in that axis -/

noncomputable theory

variables (E : Type*) [inner_product_space ℝ E] [finite_dimensional ℝ E]

/-- The identification of a finite-dimensional inner product space with its algebraic dual. -/
def to_dual : E ≃ₗ[ℝ] (E →ₗ[ℝ] ℝ) :=
(inner_product_space.to_dual ℝ E).to_linear_equiv ≪≫ₗ linear_map.to_continuous_linear_map.symm

variables {E} (Ω : alternating_map ℝ E ℝ (fin 3))
include E Ω

/-- Linear map from `E` to `E →ₗ[ℝ] E` constructed from a 3-form `Ω` on `E` and an identification of
`E` with its dual.  Effectively, the Hodge star operation.  (Under appropriate hypotheses it turns
out that the image of this map is in `𝔰𝔬(E)`, the skew-symmetric operators, which can be identified
with `Λ²E`.) -/
def A : E →ₗ[ℝ] (E →ₗ[ℝ] E) :=
begin
  let z : alternating_map ℝ E ℝ (fin 0) ≃ₗ[ℝ] ℝ :=
    alternating_map.const_linear_equiv_of_is_empty.symm,
  let y : alternating_map ℝ E ℝ (fin 1) →ₗ[ℝ] E →ₗ[ℝ] ℝ :=
    (linear_map.llcomp ℝ E (alternating_map ℝ E ℝ (fin 0)) ℝ z) ∘ₗ
      alternating_map.curry_left_linear_map,
  let y' : alternating_map ℝ E ℝ (fin 1) →ₗ[ℝ] E :=
    (linear_map.llcomp ℝ (alternating_map ℝ E ℝ (fin 1)) (E →ₗ[ℝ] ℝ) E (to_dual E).symm) y,
  let x : alternating_map ℝ E ℝ (fin 2) →ₗ[ℝ] E →ₗ[ℝ] E :=
    (linear_map.llcomp ℝ E (alternating_map ℝ E ℝ (fin 1)) _ y') ∘ₗ
      alternating_map.curry_left_linear_map,
  exact x ∘ₗ Ω.curry_left_linear_map,
end

lemma A_apply_self (v : E) : A Ω v v = 0 := by simp [A]

attribute [irreducible] A

/-- The map `A`, upgraded from linear to continuous-linear; useful for calculus. -/
def A' : E →L[ℝ] (E →L[ℝ] E) :=
(↑(linear_map.to_continuous_linear_map : (E →ₗ[ℝ] E) ≃ₗ[ℝ] (E →L[ℝ] E))
  ∘ₗ (A Ω)).to_continuous_linear_map

@[simp] lemma A'_apply (v : E) : A' Ω v = (A Ω v).to_continuous_linear_map := rfl

/-- A family of endomorphisms of `E`, parametrized by `ℝ × E`. The idea is that for nonzero `v : E`
and `t : ℝ` this endomorphism should be the rotation by the angle `t` about the axis spanned by `v`,
although this definition does not itself impose enough conditions to ensure that meaning. -/
def rot (p : ℝ × E) : E →L[ℝ] E :=
(ℝ ∙ p.2).subtypeL ∘L (orthogonal_projection (ℝ ∙ p.2) : E →L[ℝ] (ℝ ∙ p.2))
  + real.cos (p.1 * real.pi) • (ℝ ∙ p.2)ᗮ.subtypeL ∘L (orthogonal_projection (ℝ ∙ p.2)ᗮ : E →L[ℝ] (ℝ ∙ p.2)ᗮ)
  + real.sin (p.1 * real.pi) • (A Ω p.2).to_continuous_linear_map

/-- Alternative form of the construction `rot`, convenient for the smoothness calculation. -/
def rot_aux (p : ℝ × E) : E →L[ℝ] E :=
real.cos (p.1 * real.pi) • continuous_linear_map.id ℝ E +
  ((1 - real.cos (p.1 * real.pi)) • (ℝ ∙ p.2).subtypeL ∘L (orthogonal_projection (ℝ ∙ p.2) : E →L[ℝ] (ℝ ∙ p.2))
    + real.sin (p.1 * real.pi) • (A' Ω p.2))

lemma rot_eq_aux : rot Ω = rot_aux Ω :=
begin
  ext1 p,
  dsimp [rot, rot_aux],
  rw id_eq_sum_orthogonal_projection_self_orthogonal_complement (ℝ ∙ p.2),
  simp only [smul_add, sub_smul, one_smul],
  abel,
end

/-- The map `rot` is smooth on `ℝ × (E \ {0})`. -/
lemma cont_diff_rot {p : ℝ × E} (hp : p.2 ≠ 0) : cont_diff_at ℝ ⊤ (rot Ω) p :=
begin
  simp only [rot_eq_aux],
  refine (cont_diff_at_fst.mul_const.cos.smul cont_diff_at_const).add _,
  refine ((cont_diff_at_const.sub cont_diff_at_fst.mul_const.cos).smul _).add
    (cont_diff_at_fst.mul_const.sin.smul _),
  { exact (cont_diff_at_orthogonal_projection_singleton hp).comp _ cont_diff_at_snd },
  { exact (A' Ω).cont_diff.cont_diff_at.comp _ cont_diff_at_snd },
end

/-- The map `rot` sends `{0} × E` to the identity. -/
lemma rot_zero (v : E) : rot Ω (0, v) = continuous_linear_map.id ℝ E :=
begin
  ext w,
  simpa [rot] using (eq_sum_orthogonal_projection_self_orthogonal_complement (ℝ ∙ v) w).symm,
end

/-- The map `rot` sends `(1, v)` to a transformation which on `(ℝ ∙ v)ᗮ` acts as the negation. -/
lemma rot_one (v : E) {w : E} (hw : w ∈ (ℝ ∙ v)ᗮ) : rot Ω (1, v) w = - w :=
by simp [rot, orthogonal_projection_eq_self_iff.mpr hw,
  orthogonal_projection_mem_subspace_orthogonal_complement_eq_zero hw]

/-- The map `rot` sends `(v, t)` to a transformation preserving `v`. -/
lemma rot_self (p : ℝ × E) : rot Ω p p.2 = p.2 :=
begin
  have H : ↑(orthogonal_projection (ℝ ∙ p.2) p.2) = p.2 :=
    orthogonal_projection_eq_self_iff.mpr (submodule.mem_span_singleton_self p.2),
  simp [rot, A_apply_self, orthogonal_projection_orthogonal_complement_singleton_eq_zero, H],
end

lemma inj_on_rot (p : ℝ × E) : set.inj_on (rot Ω p) (ℝ ∙ p.2)ᗮ :=
sorry  -- expect to need nondegeneracy of `Ω` for this
