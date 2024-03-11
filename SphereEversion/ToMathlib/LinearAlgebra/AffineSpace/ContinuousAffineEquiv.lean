/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
import Mathlib.Topology.Algebra.Module.Basic

/-!
# Continuous affine equivalences

In this file, we define continuous affine equivalences, which are affine equivalences
which are continuous with continuous inverse.

## Main definitions
* `ContinuousAffineEquiv.refl k P`: the identity map as a `ContinuousAffineEquiv`;
* `e.symm`: the inverse map of a `ContinuousAffineEquiv` as a `ContinuousAffineEquiv`;
* `e.trans e'`: composition of two `ContinuousAffineEquiv`s; note that the order
  follows `mathlib`'s `CategoryTheory` convention (apply `e`, then `e'`),
  not the convention used in function composition and compositions of bundled morphisms.

## TODO
- equip `AffineEquiv k P P` with a `Group` structure,
with multiplication corresponding to composition in `AffineEquiv.group`.

- am I missing further basic API? fix remaining (few) sorries
- relate continuous linear equivalences and continuous affine equivalences

-/

open Function

/-- A continuous affine equivalence between two affine topological spaces is an affine equivalence
such that forward and inverse maps are continuous. -/
structure ContinuousAffineEquiv (k P₁ P₂ : Type*) {V₁ V₂ : Type*} [Ring k]
  [AddCommGroup V₁] [Module k V₁] [AddTorsor V₁ P₁] [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]
  [TopologicalSpace P₁] [TopologicalSpace P₂] extends P₁ ≃ᵃ[k] P₂ where
  continuous_toFun : Continuous toFun := by continuity
  continuous_invFun : Continuous invFun := by continuity

@[inherit_doc]
notation:25 P₁ " ≃ᵃL[" k:25 "] " P₂:0 => ContinuousAffineEquiv k P₁ P₂

variable {k P₁ P₂ P₃ P₄ V₁ V₂ V₃ V₄ : Type*} [Ring k]
  [AddCommGroup V₁] [Module k V₁] [AddTorsor V₁ P₁]
  [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]
  [AddCommGroup V₃] [Module k V₃] [AddTorsor V₃ P₃]
  [AddCommGroup V₄] [Module k V₄] [AddTorsor V₄ P₄]
  [TopologicalSpace P₁] [AddCommMonoid P₁] [Module k P₁]
  [TopologicalSpace P₂] [AddCommMonoid P₂] [Module k P₂]
  [TopologicalSpace P₃] --[AddCommMonoid P₃] [Module k P₃]
  [TopologicalSpace P₄] --[AddCommMonoid P₄] [Module k P₄]

namespace ContinuousAffineEquiv

-- not needed below, but perhaps still useful?
-- simpVarHead linter complains, so removed @[simp]
theorem toAffineEquiv_mk (f : P₁ ≃ᵃ[k] P₂) (h₁ : Continuous f.toFun) (h₂ : Continuous f.invFun) :
    toAffineEquiv (mk f h₁ h₂) = f :=
  rfl

theorem toAffineEquiv_injective : Injective (toAffineEquiv : (P₁ ≃ᵃL[k] P₂) → P₁ ≃ᵃ[k] P₂) := by
  rintro ⟨e, econt, einv_cont⟩ ⟨e', e'cont, e'inv_cont⟩ H
  congr

instance equivLike : EquivLike (P₁ ≃ᵃL[k] P₂) P₁ P₂ where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' _ _ h _ := toAffineEquiv_injective (DFunLike.coe_injective h)

instance : CoeFun (P₁ ≃ᵃL[k] P₂) fun _ ↦ P₁ → P₂ :=
  DFunLike.hasCoeToFun

@[ext]
theorem ext {e e' : P₁ ≃ᵃL[k] P₂} (h : ∀ x, e x = e' x) : e = e' :=
  DFunLike.ext _ _ h

-- linter complains... @[simp]
theorem coe_toEquiv (e : P₁ ≃ᵃL[k] P₂) : ⇑e.toEquiv = e :=
  rfl

-- coe_coe lemma?

-- AffineEquiv has lots of lemmas that coercions are injective - needed?
-- AffineEquiv has coe_mk and mk' lemmas; do I need them?

section ReflSymmTrans

variable (k P₁) in
/-- Identity map as a `ContinuousAffineEquiv`. -/
def refl : P₁ ≃ᵃL[k] P₁ where
  toEquiv := Equiv.refl P₁
  linear := LinearEquiv.refl k V₁
  map_vadd' _ _ := rfl

@[simp]
theorem coe_refl : ⇑(refl k P₁) = id :=
  rfl

@[simp]
theorem refl_apply (x : P₁) : refl k P₁ x = x :=
  rfl

@[simp]
theorem toAffineEquiv_refl : (refl k P₁).toAffineEquiv = AffineEquiv.refl k P₁ :=
  rfl

@[simp]
theorem toEquiv_refl : (refl k P₁).toEquiv = Equiv.refl P₁ :=
  rfl

/-- Inverse of a continuous affine equivalence as a continuous affine equivalence. -/
@[symm]
def symm (e : P₁ ≃ᵃL[k] P₂) : P₂ ≃ᵃL[k] P₁ where
  toAffineEquiv := e.toAffineEquiv.symm
  continuous_toFun := e.continuous_invFun
  continuous_invFun := e.continuous_toFun

@[simp]
theorem symm_toAffineEquiv (e : P₁ ≃ᵃL[k] P₂) : e.toAffineEquiv.symm = e.symm.toAffineEquiv :=
  rfl

@[simp]
theorem symm_toEquiv (e : P₁ ≃ᵃL[k] P₂) : e.toEquiv.symm = e.symm.toEquiv := rfl

-- custom simps projections??

-- bijectivity, range_eq??

@[simp]
theorem apply_symm_apply (e : P₁ ≃ᵃL[k] P₂) (p : P₂) : e (e.symm p) = p :=
  e.toEquiv.apply_symm_apply p

@[simp]
theorem symm_apply_apply (e : P₁ ≃ᵃL[k] P₂) (p : P₁) : e.symm (e p) = p :=
  e.toEquiv.symm_apply_apply p

theorem apply_eq_iff_eq_symm_apply (e : P₁ ≃ᵃL[k] P₂) {p₁ p₂} : e p₁ = p₂ ↔ p₁ = e.symm p₂ :=
  e.toEquiv.apply_eq_iff_eq_symm_apply

theorem apply_eq_iff_eq (e : P₁ ≃ᵃL[k] P₂) {p₁ p₂ : P₁} : e p₁ = e p₂ ↔ p₁ = p₂ :=
  e.toEquiv.apply_eq_iff_eq

@[simp]
theorem symm_symm (e : P₁ ≃ᵃL[k] P₂) : e.symm.symm = e := by
  ext x
  rfl

theorem symm_symm_apply  (e : P₁ ≃ᵃL[k] P₂) (x : P₁) : e.symm.symm x = e x :=
  rfl

theorem symm_apply_eq  (e : P₁ ≃ᵃL[k] P₂)  {x y} : e.symm x = y ↔ x = e y :=
  e.toAffineEquiv.symm_apply_eq

theorem eq_symm_apply  (e : P₁ ≃ᵃL[k] P₂) {x y} : y = e.symm x ↔ e y = x :=
  e.toAffineEquiv.eq_symm_apply

@[simp]
theorem image_symm (f : P₁ ≃ᵃL[k] P₂) (s : Set P₂) : f.symm '' s = f ⁻¹' s :=
  f.symm.toEquiv.image_eq_preimage _

@[simp]
theorem preimage_symm (f : P₁ ≃ᵃL[k] P₂) (s : Set P₁) : f.symm ⁻¹' s = f '' s :=
  (f.symm.image_symm _).symm

protected theorem image_eq_preimage  (e : P₁ ≃ᵃL[k] P₂) (s : Set P₁) : e '' s = e.symm ⁻¹' s :=
  e.toEquiv.image_eq_preimage s

protected theorem image_symm_eq_preimage (e : P₁ ≃ᵃL[k] P₂) (s : Set P₂) :
    e.symm '' s = e ⁻¹' s := by rw [e.symm.image_eq_preimage, e.symm_symm]

@[simp]
theorem refl_symm : (refl k P₁).symm = refl k P₁ :=
  rfl

@[simp]
theorem symm_refl : (refl k P₁).symm = refl k P₁ :=
  rfl

/-- Composition of two `ContinuousAffineEquiv`alences, applied left to right. -/
@[trans]
def trans (e : P₁ ≃ᵃL[k] P₂) (e' : P₂ ≃ᵃL[k] P₃) : P₁ ≃ᵃL[k] P₃ where
  toAffineEquiv := e.toAffineEquiv.trans e'.toAffineEquiv
  continuous_toFun := sorry
  continuous_invFun := sorry

@[simp]
theorem coe_trans (e : P₁ ≃ᵃL[k] P₂) (e' : P₂ ≃ᵃL[k] P₃) : ⇑(e.trans e') = e' ∘ e :=
  rfl

@[simp]
theorem trans_apply (e : P₁ ≃ᵃL[k] P₂) (e' : P₂ ≃ᵃL[k] P₃) (p : P₁) : e.trans e' p = e' (e p) :=
  rfl

theorem trans_assoc (e₁ : P₁ ≃ᵃL[k] P₂) (e₂ : P₂ ≃ᵃL[k] P₃) (e₃ : P₃ ≃ᵃL[k] P₄) :
    (e₁.trans e₂).trans e₃ = e₁.trans (e₂.trans e₃) :=
  ext fun _ ↦ rfl

@[simp]
theorem trans_refl (e : P₁ ≃ᵃL[k] P₂) : e.trans (refl k P₂) = e :=
  ext fun _ ↦ rfl

@[simp]
theorem refl_trans (e : P₁ ≃ᵃL[k] P₂) : (refl k P₁).trans e = e :=
  ext fun _ ↦ rfl

@[simp]
theorem self_trans_symm (e : P₁ ≃ᵃL[k] P₂) : e.trans e.symm = refl k P₁ :=
  ext e.symm_apply_apply

@[simp]
theorem symm_trans_self (e : P₁ ≃ᵃL[k] P₂) : e.symm.trans e = refl k P₂ :=
  ext e.apply_symm_apply

end ReflSymmTrans

-- TODO: compare with ContinuousLinearEquiv also, add missing lemmas!

-- TODO: should toContinuousLinearEquiv.toHomeomorph re-use this?
/-- A continuous affine equivalence is a homeomorphism. -/
def toHomeomorph (e : P₁ ≃ᵃL[k] P₂) : P₁ ≃ₜ P₂ where
  __ := e

variable (k P₁) in
/- The map `p ↦ v +ᵥ p` as a continuous affine automorphism of an affine space
  on which addition is continuous. -/
def constVAdd /-[AddGroup P₁] [ContinuousAdd P₁]-/ (v : V₁) : P₁ ≃ᵃL[k] P₁ where
  toAffineEquiv := AffineEquiv.constVAdd k P₁ v
  -- can I use the proofs in `Homeomorph.addLeft y`? I haven't managed to...
  continuous_toFun := sorry
  continuous_invFun := sorry

lemma constVAdd_coe /-[AddGroup P₁] [ContinuousAdd P₁]-/ (v : V₁) :
  (constVAdd k P₁ v).toAffineEquiv = .constVAdd k P₁ v := rfl

end ContinuousAffineEquiv

variable [AddCommGroup P₁] [AddCommGroup P₂] [Module k P₂] [Module k P₁]
  [Module k V₂] [Module k V₁]

/-- Reinterpret a `ContinuousLinearEquiv` as a `ContinuousAffineEquiv`. -/
@[coe]
def _root_.ContinuousLinearEquiv.toAffineLinearEquiv [Module k P₁] (e : P₁ ≃L[k] P₂) : P₁ ≃ᵃL[k] P₂ where
  toAffineEquiv := by
    sorry
    --let f := e.toLinearEquiv
    --exact f.toAffineEquiv (k := k) (V₁ := P₁) (V₂ := P₂)--(e.toLinearEquiv).toAffineEquiv (k := k)
  -- __ := e.toAffineEquiv.toLinearEquiv
  continuous_toFun := sorry-- e.continuous_toFun
  continuous_invFun := sorry --e.continuous_invFun

-- conversely, interpret a linear `ContinuousAffineEquiv` as a `ContinuousLinearEquiv`
-- toLinearEquiv := e.toAffineEquiv.toLinearEquiv (linear yada yada)
