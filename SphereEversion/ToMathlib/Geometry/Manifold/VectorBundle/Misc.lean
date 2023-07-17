/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

! This file was ported from Lean 3 source module to_mathlib.geometry.manifold.vector_bundle.misc
-/
import Mathlib.Geometry.Manifold.VectorBundle.Pullback
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import SphereEversion.ToMathlib.Geometry.Manifold.MiscManifold

/-!
# Various operations on and properties of smooth vector bundles
-/


noncomputable section

open Bundle Set TopologicalSpace LocalHomeomorph

open scoped Classical Manifold Bundle

namespace FiberBundle

variable {𝕜 B B' F M : Type _} {E : B → Type _}

variable [TopologicalSpace F] [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)]
  {HB : Type _} [TopologicalSpace HB] [TopologicalSpace B] [ChartedSpace HB B] [FiberBundle F E]

theorem chartedSpace_chartAt_fst' (x y : TotalSpace F E) :
    (chartAt (ModelProd HB F) x y).1 = chartAt HB x.proj (trivializationAt F E x.proj y).1 := by
  rw [charted_space_chart_at]; rfl

theorem chartedSpace_chartAt_fst {x y : TotalSpace F E}
    (hy : y.proj ∈ (trivializationAt F E x.proj).baseSet) :
    (chartAt (ModelProd HB F) x y).1 = chartAt HB x.proj y.proj := by
  rw [charted_space_chart_at_fst', (trivialization_at F E x.proj).coe_fst' hy]

theorem chartedSpace_chartAt_snd (x y : TotalSpace F E) :
    (chartAt (ModelProd HB F) x y).2 = (trivializationAt F E x.proj y).2 := by
  rw [charted_space_chart_at]; rfl

end FiberBundle

section VectorBundle

variable {𝕜 B F F₁ F₂ : Type _} {E : B → Type _} {E₁ : B → Type _} {E₂ : B → Type _}
  [NontriviallyNormedField 𝕜] [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace (TotalSpace F E)]
  [∀ x, TopologicalSpace (E x)] [∀ x, AddCommMonoid (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [TopologicalSpace (TotalSpace F₁ E₁)]
  [∀ x, TopologicalSpace (E₁ x)] [∀ x, AddCommMonoid (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [TopologicalSpace (TotalSpace F₂ E₂)]
  [∀ x, TopologicalSpace (E₂ x)] [TopologicalSpace B] {n : ℕ∞} [FiberBundle F₁ E₁]
  [VectorBundle 𝕜 F₁ E₁] [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  {e₁ e₁' : Trivialization F₁ (π F₁ E₁)} {e₂ e₂' : Trivialization F₂ (π F₂ E₂)}

end VectorBundle

namespace VectorBundleCore

variable {R 𝕜 B F ι : Type _} [NontriviallyNormedField R] [NormedAddCommGroup F] [NormedSpace R F]
  [TopologicalSpace B] (Z : VectorBundleCore R B F ι)

/-- `Z.coord_change j i` is a partial inverse of `Z.coord_change i j`. -/
theorem coordChange_comp_eq_self {i j : ι} {x : B} (hx : x ∈ Z.baseSet i ∩ Z.baseSet j) (v : F) :
    Z.coordChange j i x (Z.coordChange i j x v) = v := by
  rw [Z.coord_change_comp i j i x ⟨hx, hx.1⟩, Z.coord_change_self i x hx.1]

end VectorBundleCore

namespace Bundle.Trivial

open _Root_.Trivialization

variable {𝕜 B F : Type _}

variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace B]

@[simp, mfld_simps]
protected theorem trivializationAt (x : B) :
    trivializationAt F (trivial B F) x = Trivial.trivialization B F :=
  rfl

@[simp, mfld_simps]
theorem trivialization_continuousLinearMapAt (x : B) :
    (Trivial.trivialization B F).continuousLinearMapAt 𝕜 x = ContinuousLinearMap.id 𝕜 F :=
  by
  ext v
  simp_rw [continuous_linear_map_at_apply, coe_linear_map_at]
  rw [if_pos]
  exacts [rfl, mem_univ _]

end Bundle.Trivial

section Hom

variable {𝕜₁ : Type _} [NontriviallyNormedField 𝕜₁] {𝕜₂ : Type _} [NontriviallyNormedField 𝕜₂]
  (σ : 𝕜₁ →+* 𝕜₂) [iσ : RingHomIsometric σ]

variable {B : Type _} [TopologicalSpace B]

variable (F₁ : Type _) [NormedAddCommGroup F₁] [NormedSpace 𝕜₁ F₁] (E₁ : B → Type _)
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜₁ (E₁ x)] [TopologicalSpace (TotalSpace F₁ E₁)]

variable (F₂ : Type _) [NormedAddCommGroup F₂] [NormedSpace 𝕜₂ F₂] (E₂ : B → Type _)
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜₂ (E₂ x)] [TopologicalSpace (TotalSpace F₂ E₂)]

variable (F₁ E₁ F₂ E₂) [RingHomIsometric σ]

variable [∀ x : B, TopologicalSpace (E₁ x)] [FiberBundle F₁ E₁] [VectorBundle 𝕜₁ F₁ E₁]

variable [∀ x : B, TopologicalSpace (E₂ x)] [FiberBundle F₂ E₂] [VectorBundle 𝕜₂ F₂ E₂]

variable [∀ x, TopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜₂ (E₂ x)]

@[simp, mfld_simps]
theorem continuousLinearMap_trivializationAt (x : B) :
    trivializationAt (F₁ →SL[σ] F₂) (Bundle.ContinuousLinearMap σ E₁ E₂) x =
      (trivializationAt F₁ E₁ x).continuousLinearMap σ (trivializationAt F₂ E₂ x) :=
  rfl

-- todo: do in mathlib
instance Bundle.ContinuousLinearMap.addCommGroup (x : B) :
    AddCommGroup (Bundle.ContinuousLinearMap σ E₁ E₂ x) := by
  delta_instance bundle.continuous_linear_map

end Hom

section Pullback

/-- We need some instances like this to work with negation on pullbacks -/
instance {B B'} {E : B → Type _} {f : B' → B} {x : B'} [∀ x', AddCommGroup (E x')] :
    AddCommGroup ((f *ᵖ E) x) := by delta_instance bundle.pullback

instance {B B'} {E : B → Type _} {f : B' → B} {x : B'} [∀ x', Zero (E x')] : Zero ((f *ᵖ E) x) := by
  delta_instance bundle.pullback

variable {B F B' K : Type _} {E : B → Type _} {f : K} [TopologicalSpace B']
  [TopologicalSpace (TotalSpace F E)] [TopologicalSpace F] [TopologicalSpace B] [∀ b, Zero (E b)]
  [ContinuousMapClass K B' B]

namespace Trivialization

-- attribute [simps base_set] trivialization.pullback
theorem pullback_symm (e : Trivialization F (π F E)) (x : B') :
    (e.pullback f).symm x = e.symm (f x) := by
  ext y
  simp_rw [Trivialization.symm, Pretrivialization.symm]
  congr; ext (hx : f x ∈ e.to_pretrivialization.base_set)
  change cast _ (e.symm (f x) y) = cast _ (e.to_local_homeomorph.symm (f x, y)).2
  simp_rw [Trivialization.symm, Pretrivialization.symm, dif_pos hx, cast_cast]
  rfl

end Trivialization

variable [∀ x, TopologicalSpace (E x)] [FiberBundle F E]

theorem pullback_trivializationAt {x : B'} :
    trivializationAt F (f *ᵖ E) x = (trivializationAt F E (f x)).pullback f :=
  rfl

end Pullback

section PullbackVb

variable {R 𝕜 B F B' : Type _} {E : B → Type _}

variable [TopologicalSpace B'] [TopologicalSpace (TotalSpace F E)] [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace B] [∀ x, AddCommMonoid (E x)]
  [∀ x, Module 𝕜 (E x)] [∀ x, TopologicalSpace (E x)] [FiberBundle F E] {K : Type _}
  [ContinuousMapClass K B' B] (f : K)

namespace Trivialization

theorem pullback_symmL (e : Trivialization F (π F E)) [e.isLinear 𝕜] (x : B') :
    (e.pullback f).symmL 𝕜 x = e.symmL 𝕜 (f x) := by ext y; simp_rw [symmL_apply, pullback_symm]

end Trivialization

end PullbackVb

