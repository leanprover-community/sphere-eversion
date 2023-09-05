/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth

! This file was ported from Lean 3 source module to_mathlib.analysis.inner_product_space.cross_product
-/
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Orientation

/-! # The cross-product on an oriented real inner product space of dimension three -/


noncomputable section

open scoped RealInnerProductSpace

open FiniteDimensional

set_option synthInstance.checkSynthOrder false
attribute [local instance] fact_finiteDimensional_of_finrank_eq_succ
set_option synthInstance.checkSynthOrder true

variable (E : Type _) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The identification of a finite-dimensional inner product space with its algebraic dual. -/
private def to_dual [FiniteDimensional ℝ E] : E ≃ₗ[ℝ] E →ₗ[ℝ] ℝ :=
  (InnerProductSpace.toDual ℝ E).toLinearEquiv ≪≫ₗ LinearMap.toContinuousLinearMap.symm

namespace Orientation

variable {E}
variable [Fact (finrank ℝ E = 3)] (ω : Orientation ℝ E (Fin 3))

/-- Linear map from `E` to `E →ₗ[ℝ] E` constructed from a 3-form `Ω` on `E` and an identification of
`E` with its dual.  Effectively, the Hodge star operation.  (Under appropriate hypotheses it turns
out that the image of this map is in `𝔰𝔬(E)`, the skew-symmetric operators, which can be identified
with `Λ²E`.) -/
def crossProduct : E →ₗ[ℝ] E →ₗ[ℝ] E := by
  let z : AlternatingMap ℝ E ℝ (Fin 0) ≃ₗ[ℝ] ℝ :=
    AlternatingMap.constLinearEquivOfIsEmpty.symm
  let y : AlternatingMap ℝ E ℝ (Fin 1) →ₗ[ℝ] E →ₗ[ℝ] ℝ :=
    LinearMap.llcomp ℝ E (AlternatingMap ℝ E ℝ (Fin 0)) ℝ z ∘ₗ AlternatingMap.curryLeftLinearMap
  let y' : AlternatingMap ℝ E ℝ (Fin 1) →ₗ[ℝ] E :=
    (LinearMap.llcomp ℝ (AlternatingMap ℝ E ℝ (Fin 1)) (E →ₗ[ℝ] ℝ) E (to_dual E).symm) y
  let u : AlternatingMap ℝ E ℝ (Fin 2) →ₗ[ℝ] E →ₗ[ℝ] E :=
    LinearMap.llcomp ℝ E (AlternatingMap ℝ E ℝ (Fin 1)) _ y' ∘ₗ AlternatingMap.curryLeftLinearMap
  exact u ∘ₗ AlternatingMap.curryLeftLinearMap (n := 2) ω.volumeForm

local infixl:100 "×₃" => ω.crossProduct

theorem crossProduct_apply_self (v : E) : v×₃v = 0 := by simp [crossProduct]


example {𝕜 : Type u} [NontriviallyNormedField 𝕜] {E : Type v} [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E] [TopologicalAddGroup E] [ContinuousSMul 𝕜 E] {F' : Type x}
  [AddCommGroup F'] [Module 𝕜 F'] [TopologicalSpace F'] [TopologicalAddGroup F']
  [ContinuousSMul 𝕜 F'] [CompleteSpace 𝕜] [T2Space E] [FiniteDimensional 𝕜 E]
  (f : E →ₗ[𝕜] F') : (LinearMap.toContinuousLinearMap f : E → F') = ↑f :=
LinearMap.coe_toContinuousLinearMap' f

#check LinearMap.coe_toContinuousLinearMap'
section
open Lean PrettyPrinter Delaborator SubExpr

def withBetaReduced (d : Delab) : Delab := do
  let e' ← Core.betaReduce (← getExpr)
  withTheReader SubExpr (fun ctx => {ctx with expr := e'}) d

/-- Fail if the arity is less than `n`, and collect arguments if the arity is more than `n`. -/
partial def delabWithArity (n : Nat) (d : Delab) : Delab := do
  if (← getExpr).getAppNumArgs < n then
    failure
  else
    let rec loop (args : Array Term) : Delab := do
      if (← getExpr).getAppNumArgs > n then
        let arg ← withAppArg delab
        withAppFn <| loop (args.push arg)
      else
        let s ← d
        `($s $args*)
    loop #[]

/-- Delaborator for a coercion function of arity `arity` such that
the coerced value is at argument index `coeArg`. -/
def delabCoe (arity coeArg : Nat) : Delab := delabWithArity arity do
  let arg ← withNaryArg coeArg delab
  let ty ← withType <| withBetaReduced delab
  `((↑$arg : $ty))

namespace AnnotateFunLikecoe
@[scoped delab app.FunLike.coe]
def delabFunLikeCoe : Delab := delabCoe 5 4
end AnnotateFunLikecoe
end

set_option quotPrecheck false in
notation "𝒜" => AlternatingMap ℝ E ℝ (Fin 0)
set_option quotPrecheck false in
notation "𝒜'" => AlternatingMap ℝ E ℝ (Fin (Nat.succ 0))

attribute [pp_dot] LinearEquiv.symm

#check (LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] ℝ) → NormedSpace.Dual ℝ E)
--set_option pp.coercions false
--open AnnotateFunLikecoe

#check (↑LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] ℝ) → NormedSpace.Dual ℝ E)

#synth ContinuousSMul ℝ ℝ
#check to_dual.proof_11
#check ContinuousMul.to_continuousSMul

example : to_dual.proof_11 = ContinuousMul.to_continuousSMul := rfl

#check @LinearMap.toContinuousLinearMap ℝ _ E _ _ _ _ _ ℝ _ _ _ _ to_dual.proof_11 _ _ _

lemma foo (φ : E →ₗ[ℝ] ℝ) (w: E) : (↑((LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] ℝ) → NormedSpace.Dual ℝ E) φ) : E → ℝ) w = (↑φ : E → ℝ) w := by
  rfl

lemma bar (φ : E →ₗ[ℝ] ℝ) (w: E) : @FunLike.coe (NormedSpace.Dual ℝ E) E (fun _ ↦ ℝ) ContinuousMapClass.toFunLike
  (@LinearMap.toContinuousLinearMap ℝ _ E _ _ _ _ _ ℝ _ _ _ _ to_dual.proof_11 _ _ _ φ) w = (↑φ : E → ℝ) w := by
  rw [foo]

--set_option pp.explicit true in
theorem inner_crossProduct_apply (u v w : E) : ⟪u×₃v, w⟫ = ω.volumeForm ![u, v, w] := by
  simp only [crossProduct]
  simp only [to_dual]
  simp only [LinearEquiv.trans_symm]
  simp only [LinearEquiv.symm_symm]
  simp only [LinearIsometryEquiv.toLinearEquiv_symm]
  simp only [AlternatingMap.curryLeftLinearMap_apply]
  simp only [LinearMap.coe_comp]
  simp only [Function.comp_apply]
  simp only [LinearMap.llcomp_apply]
  simp only [LinearEquiv.coe_coe]
  simp only [LinearEquiv.trans_apply]
  simp only [LinearIsometryEquiv.coe_toLinearEquiv]
  simp only [AlternatingMap.curryLeftLinearMap_apply]
  simp only [LinearMap.coe_comp]
  rw [InnerProductSpace.toDual_symm_apply]
  set F' : 𝒜' → E →ₗ[ℝ] ℝ := (LinearMap.llcomp ℝ E 𝒜 ℝ ↑(AlternatingMap.constLinearEquivOfIsEmpty.symm : 𝒜 ≃ₗ[ℝ] ℝ)) ∘ AlternatingMap.curryLeftLinearMap
  set K := (AlternatingMap.curryLeft ((AlternatingMap.curryLeft (volumeForm ω)) u)) v
  have := bar (F' K) w
  change (↑(F' K) : E → ℝ) w = _
  --rw [LinearMap.coe_toContinuousLinearMap' (F' K)] -- does nothing
  simp only [Function.comp_apply]
  simp only [LinearMap.llcomp_apply]
  simp only [LinearEquiv.coe_coe]
  simp only [AlternatingMap.constLinearEquivOfIsEmpty_symm_apply]
  simp only [Matrix.zero_empty]
  simp only [AlternatingMap.curryLeftLinearMap_apply]
  simp only [AlternatingMap.curryLeft_apply_apply]

theorem inner_crossProduct_apply_self (u : E) (v : (ℝ ∙ u)ᗮ) : ⟪u×₃v, u⟫ = 0 := by
  rw [ω.inner_crossProduct_apply u v u]
  refine' ω.volumeForm.map_eq_zero_of_eq ![u, v, u] _ (by norm_num : (0 : Fin 3) ≠ 2)
  simp

theorem inner_crossProduct_apply_apply_self (u : E) (v : (ℝ ∙ u)ᗮ) : ⟪u×₃v, v⟫ = 0 := by
  rw [ω.inner_crossProduct_apply u v v]
  refine' ω.volumeForm.map_eq_zero_of_eq ![u, v, v] _ (by norm_num : (1 : Fin 3) ≠ 2)
  simp

/-- The map `cross_product`, upgraded from linear to continuous-linear; useful for calculus. -/
def crossProduct' : E →L[ℝ] E →L[ℝ] E :=
  LinearMap.toContinuousLinearMap
    (↑(LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] E) ≃ₗ[ℝ] E →L[ℝ] E) ∘ₗ ω.crossProduct)

@[simp]
theorem crossProduct'_apply (v : E) :
    ω.crossProduct' v = LinearMap.toContinuousLinearMap (ω.crossProduct v) :=
  rfl

theorem norm_crossProduct (u : E) (v : (ℝ ∙ u)ᗮ) : ‖u×₃v‖ = ‖u‖ * ‖v‖ := by
  classical
  refine' le_antisymm _ _
  · cases' eq_or_lt_of_le (norm_nonneg (u×₃v)) with h h
    · rw [← h]
      positivity
    refine' le_of_mul_le_mul_right _ h
    rw [← real_inner_self_eq_norm_mul_norm]
    simpa only [inner_crossProduct_apply, Fin.mk_zero, Fin.prod_univ_succ, Finset.card_singleton,
      Finset.prod_const, Fintype.univ_ofSubsingleton, Matrix.cons_val_fin_one, Matrix.cons_val_succ,
      Matrix.cons_val_zero, mul_assoc, Nat.zero_eq, pow_one, Submodule.coe_norm] using
      ω.volumeForm_apply_le ![u, v, u×₃v]
  let K : Submodule ℝ E := Submodule.span ℝ ({u, ↑v} : Set E)
  have : Nontrivial Kᗮ :=
    by
    apply @FiniteDimensional.nontrivial_of_finrank_pos ℝ
    have : finrank ℝ K ≤ Finset.card {u, (v : E)} := by
      simpa [Set.toFinset_singleton] using finrank_span_le_card ({u, ↑v} : Set E)
    have : Finset.card {u, (v : E)} ≤ Finset.card {(v : E)} + 1 := Finset.card_insert_le u {↑v}
    have : Finset.card {(v : E)} = 1 := Finset.card_singleton (v : E)
    have : finrank ℝ K + finrank ℝ Kᗮ = finrank ℝ E := K.finrank_add_finrank_orthogonal
    have : finrank ℝ E = 3 := Fact.out
    linarith
  obtain ⟨w, hw⟩ : ∃ w : Kᗮ, w ≠ 0 := exists_ne 0
  have H : Pairwise fun i j => ⟪![u, v, w] i, ![u, v, w] j⟫ = 0 :=
    by
    intro i j hij
    have h1 : ⟪u, v⟫ = 0 := v.2 _ (Submodule.mem_span_singleton_self _)
    have h2 : ⟪(v : E), w⟫ = 0 := w.2 _ (Submodule.subset_span (by simp))
    have h3 : ⟪u, w⟫ = 0 := w.2 _ (Submodule.subset_span (by simp))
    fin_cases i <;> fin_cases j <;> norm_num at hij  <;> simp [h1, h2, h3] <;>
        rw [real_inner_comm] <;>
      assumption
  refine' le_of_mul_le_mul_right _ (by rwa [norm_pos_iff] : 0 < ‖w‖)
  -- Cauchy-Schwarz inequality for `u ×₃ v` and `w`
  simpa only [inner_crossProduct_apply, ω.abs_volumeForm_apply_of_pairwise_orthogonal H,
    inner_crossProduct_apply, Fin.mk_zero, Fin.prod_univ_succ, Finset.card_singleton,
    Finset.prod_const, Fintype.univ_ofSubsingleton, Matrix.cons_val_fin_one, Matrix.cons_val_succ,
    Matrix.cons_val_zero, Nat.zero_eq, pow_one, mul_assoc] using abs_real_inner_le_norm (u×₃v) w

theorem isometry_on_crossProduct (u : Metric.sphere (0 : E) 1) (v : (ℝ ∙ (u : E))ᗮ) :
    ‖u×₃v‖ = ‖v‖ := by simp [norm_crossProduct]

end Orientation
