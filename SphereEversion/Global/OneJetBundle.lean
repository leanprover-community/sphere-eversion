/-
Copyright (c) 2022 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Floris van Doorn

! This file was ported from Lean 3 source module global.one_jet_bundle
-/
import Mathlib.Tactic.Common

import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.Notation
import SphereEversion.ToMathlib.Geometry.Manifold.VectorBundle.Misc
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.Pullback
import Mathlib.Tactic.Monotonicity.Lemmas

/-!
# 1-jet bundles

This file contains the definition of the 1-jet bundle `J¹(M, M')`, also known as
`OneJetBundle I M I' M'`.

We also define
* `OneJetExt I I' f : M → J¹(M, M')`: the 1-jet extension `j¹f` of a map `f : M → M'`

We prove
* If `f` is smooth, `j¹f` is smooth.
* If `x ↦ (f₁ x, f₂ x, ϕ₁ x) : N → J¹(M₁, M₂)` and `x ↦ (f₂ x, f₃ x, ϕ₂ x) : N → J¹(M₂, M₃)`
  are smooth, then so is `x ↦ (f₁ x, f₃ x, ϕ₂ x ∘ ϕ₁ x) : N → J¹(M₁, M₃)`.
-/


noncomputable section

open Filter Set Equiv Bundle ContinuousLinearMap

open scoped Manifold Topology Bundle ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] (I' : ModelWithCorners 𝕜 E' H')
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''}
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H'' M''] [IsManifold I'' ∞ M'']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [TopologicalSpace G] (J : ModelWithCorners 𝕜 F G)
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {G' : Type*} [TopologicalSpace G'] (J' : ModelWithCorners 𝕜 F' G')
  {N' : Type*} [TopologicalSpace N'] [ChartedSpace G' N'] [IsManifold J' ∞ N']
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
  {H₂ : Type*} [TopologicalSpace H₂] {I₂ : ModelWithCorners 𝕜 E₂ H₂}
  {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace H₂ M₂] [IsManifold I₂ ∞ M₂]
  {E₃ : Type*} [NormedAddCommGroup E₃] [NormedSpace 𝕜 E₃]
  {H₃ : Type*} [TopologicalSpace H₃] {I₃ : ModelWithCorners 𝕜 E₃ H₃}
  {M₃ : Type*} [TopologicalSpace M₃] [ChartedSpace H₃ M₃] [IsManifold I₃ ∞ M₃]

@[inherit_doc] local notation "σ" => RingHom.id 𝕜

instance deleteme1 :
    ∀ x : M × M',
      Module 𝕜 (((ContMDiffMap.fst : C^∞⟮I.prod I', M × M'; I, M⟯) *ᵖ (TangentSpace I)) x) := by
        infer_instance

instance deleteme2 :
    ∀ x : M × M',
      Module 𝕜 (((ContMDiffMap.snd : C^∞⟮I.prod I', M × M'; I', M'⟯) *ᵖ (TangentSpace I')) x) := by
        infer_instance

instance deleteme3 :
    VectorBundle 𝕜 E ((ContMDiffMap.fst : C^∞⟮I.prod I', M × M'; I, M⟯) *ᵖ (TangentSpace I)) := by
  infer_instance

instance deleteme4 : VectorBundle 𝕜 E'
    ((ContMDiffMap.snd : C^∞⟮I.prod I', M × M'; I', M'⟯) *ᵖ (TangentSpace I')) := by
  infer_instance

instance deleteme5 : ContMDiffVectorBundle ∞ E
    ((ContMDiffMap.fst : C^∞⟮I.prod I', M × M'; I, M⟯) *ᵖ (TangentSpace I)) (I.prod I') := by
  infer_instance

instance deleteme6 : ContMDiffVectorBundle ∞ E'
    ((ContMDiffMap.snd : C^∞⟮I.prod I', M × M'; I', M'⟯) *ᵖ (TangentSpace I')) (I.prod I') := by
  infer_instance

set_option linter.unusedVariables false in
/-- The fibers of the one jet-bundle. -/
def OneJetSpace (p : M × M') : Type _ :=
  ((ContMDiffMap.fst : C^∞⟮I.prod I', M × M'; I, M⟯) *ᵖ (TangentSpace I)) p →SL[σ]
  ((ContMDiffMap.snd : C^∞⟮I.prod I', M × M'; I', M'⟯) *ᵖ (TangentSpace I')) p

instance (p : M × M') : TopologicalSpace (OneJetSpace I I' p) :=
  inferInstanceAs <| TopologicalSpace (E →L[𝕜] E')

instance (p : M × M') : AddCommGroup (OneJetSpace I I' p) :=
  inferInstanceAs <| AddCommGroup (E →L[𝕜] E')

variable {I I'}

-- what is better notation for this?
/-- Local notation for the `OneJetSpace` on `M × M'`, w.r.t. `I` and `I'` -/
local notation "FJ¹MM'" => (OneJetSpace I I' : M × M' → Type _)

variable (I I')

instance (p : M × M') : FunLike (OneJetSpace I I' p) (TangentSpace I p.1) (TangentSpace I' p.2)
where
  coe := fun φ ↦ φ.toFun
  coe_injective := fun _ _ h ↦ ContinuousLinearMap.ext (congrFun h)

variable (M M')

-- is empty if the base manifold is empty
/-- The space of one jets of maps between two smooth manifolds.
Defined in terms of `Bundle.TotalSpace` to be able to put a suitable topology on it. -/
@[reducible]
def OneJetBundle :=
  TotalSpace (E →L[𝕜] E') (OneJetSpace I I' : M × M' → Type _)

variable {I I' M M'}

@[inherit_doc] local notation "J¹MM'" => OneJetBundle I M I' M'

@[inherit_doc] local notation "HJ" => ModelProd (ModelProd H H') (E →L[𝕜] E')

omit [IsManifold I ∞ M] [IsManifold I' ∞ M'] in
@[ext]
theorem OneJetBundle.ext {x y : J¹MM'} (h : x.1.1 = y.1.1) (h' : x.1.2 = y.1.2) (h'' : x.2 = y.2) :
    x = y := by
  rcases x with ⟨⟨a, b⟩, c⟩
  rcases y with ⟨⟨d, e⟩, f⟩
  dsimp only at h h' h''
  rw [h, h', h'']

variable (I I' M M')

section OneJetBundleInstances

section

variable {M} (p : M × M')

instance (x : M × M') : Module 𝕜 (FJ¹MM' x) :=
  inferInstanceAs <| Module 𝕜 (E →L[𝕜] E')

end

set_option backward.isDefEq.respectTransparency false in
instance : TopologicalSpace J¹MM' := by
  delta OneJetSpace OneJetBundle
  infer_instance

set_option backward.isDefEq.respectTransparency false in
instance : FiberBundle (E →L[𝕜] E') FJ¹MM' := by
  delta OneJetSpace
  infer_instance

set_option backward.isDefEq.respectTransparency false in
instance : VectorBundle 𝕜 (E →L[𝕜] E') FJ¹MM' := by
  delta OneJetSpace
  infer_instance

set_option backward.isDefEq.respectTransparency false in
instance : ContMDiffVectorBundle ∞ (E →L[𝕜] E')
    (OneJetSpace I I' : M × M' → Type _) (I.prod I') := by
  delta OneJetSpace
  infer_instance

set_option backward.isDefEq.respectTransparency false in
instance : ChartedSpace HJ J¹MM' := by
  delta OneJetSpace OneJetBundle
  infer_instance

set_option backward.isDefEq.respectTransparency false in
instance : IsManifold ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) ∞ J¹MM' := by
  apply Bundle.TotalSpace.isManifold

end OneJetBundleInstances

variable {I M I' M' J J'}

/-- The tangent bundle projection on the basis is a continuous map. -/
theorem oneJetBundle_proj_continuous : Continuous (π (E →L[𝕜] E') FJ¹MM') :=
  FiberBundle.continuous_proj (E →L[𝕜] E') FJ¹MM'

-- Porting note: removed next line
-- attribute [simps] ContMDiffMap.fst ContMDiffMap.snd

set_option backward.isDefEq.respectTransparency false in
theorem oneJetBundle_trivializationAt (x₀ x : J¹MM') :
    (trivializationAt (E →L[𝕜] E') (OneJetSpace I I') x₀.proj x).2 =
      inCoordinates E (TangentSpace I) E' (TangentSpace I') x₀.proj.1 x.proj.1 x₀.proj.2 x.proj.2
        x.2 := by
  delta OneJetSpace
  rw [continuousLinearMap_trivializationAt, Trivialization.continuousLinearMap_apply]
  simp only [inCoordinates]
  congr 2
  exact Trivialization.pullback_symmL ContMDiffMap.fst
    (trivializationAt E (TangentSpace I) x₀.1.1) x.proj

theorem trivializationAt_oneJetBundle_source (x₀ : M × M') :
    (trivializationAt (E →L[𝕜] E') FJ¹MM' x₀).source =
      π (E →L[𝕜] E') FJ¹MM' ⁻¹'
        (Prod.fst ⁻¹' (chartAt H x₀.1).source ∩ Prod.snd ⁻¹' (chartAt H' x₀.2).source) :=
  rfl

theorem trivializationAt_oneJetBundle_target (x₀ : M × M') :
    (trivializationAt (E →L[𝕜] E') FJ¹MM' x₀).target =
      (Prod.fst ⁻¹' (trivializationAt E (TangentSpace I) x₀.1).baseSet ∩
          Prod.snd ⁻¹' (trivializationAt E' (TangentSpace I') x₀.2).baseSet) ×ˢ
        Set.univ :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Computing the value of a chart around `v` at point `v'` in `J¹(M, M')`.
  The last component equals the continuous linear map `v'.2`, composed on both sides by an
  appropriate coordinate change function. -/
theorem oneJetBundle_chartAt_apply (v v' : OneJetBundle I M I' M') :
    chartAt HJ v v' =
      ((chartAt H v.1.1 v'.1.1, chartAt H' v.1.2 v'.1.2),
        inCoordinates E (TangentSpace I) E' (TangentSpace I') v.1.1 v'.1.1 v.1.2 v'.1.2 v'.2) := by
  ext1
  · rfl
  rw [FiberBundle.chartedSpace_chartAt_snd]
  exact oneJetBundle_trivializationAt v v'

set_option backward.isDefEq.respectTransparency false in
/-- In `J¹(M, M')`, the source of a chart has a nice formula -/
theorem oneJetBundle_chart_source (x₀ : J¹MM') :
    (chartAt HJ x₀).source =
      π (E →L[𝕜] E') FJ¹MM' ⁻¹' (chartAt (ModelProd H H') x₀.proj).source := by
  -- Porting note: was
  -- simp only [FiberBundle.chartedSpace_chartAt, trivializationAt_oneJetBundle_source, mfld_simps]
  rw [FiberBundle.chartedSpace_chartAt]
  simp_rw [
    OpenPartialHomeomorph.trans_toPartialEquiv,
    PartialEquiv.trans_source,
    OpenPartialHomeomorph.prod_toPartialHomeomorph,
    PartialEquiv.prod_source,
    OpenPartialHomeomorph.coe_toPartialEquiv,
    Trivialization.coe_coe,
    OpenPartialHomeomorph.refl_partialEquiv,
    PartialEquiv.refl_source,
    prodChartedSpace_chartAt,
    OpenPartialHomeomorph.prod_toPartialHomeomorph,
    trivializationAt_oneJetBundle_source,
    PartialEquiv.prod_source,
    Set.preimage_inter,
    prod_univ, ← preimage_inter, ← Set.prod_eq, preimage_preimage, inter_eq_left,
    subset_def, mem_preimage]
  intro x hx
  simpa

section

section

universe u v w₁ w₂ U

variable {B : Type u} {F : Type v} {E : B → Type w₁} {B' : Type w₂}
  [TopologicalSpace B'] [TopologicalSpace (TotalSpace F E)]
  [TopologicalSpace F] [TopologicalSpace B] [(_b : B) → Zero (E _b)]
  {K : Type U} [FunLike K B' B] [ContinuousMapClass K B' B]
  [(x : B) → TopologicalSpace (E x)] [FiberBundle F E]

lemma trivializationAt_pullBack_baseSet (f : K) (x : B') :
    (trivializationAt F ((f : B' → B) *ᵖ E) x).baseSet =
    f ⁻¹' (trivializationAt F E (f x)).baseSet :=
  rfl
end

section
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] {n : ℕ∞}

@[simp]
lemma ContMDiffMap.coe_fst :
    ((ContMDiffMap.fst : C^n⟮I.prod I', M × M'; I, M⟯) : M × M' → M) = Prod.fst :=
  rfl

@[simp]
lemma ContMDiffMap.coe_snd :
    ((ContMDiffMap.snd : C^n⟮I.prod I', M × M'; I', M'⟯) : M × M' → M') = Prod.snd :=
  rfl

@[simp]
lemma ContMDiffMap.fst_apply (x : M) (x' : M') :
    (ContMDiffMap.fst : C^n⟮I.prod I', M × M'; I, M⟯) (x, x') = x := rfl

@[simp]
lemma ContMDiffMap.snd_apply (x : M) (x' : M') :
    (ContMDiffMap.snd : C^n⟮I.prod I', M × M'; I', M'⟯) (x, x') = x' := rfl

end

set_option backward.isDefEq.respectTransparency false in
/-- In `J¹(M, M')`, the target of a chart has a nice formula -/
theorem oneJetBundle_chart_target (x₀ : J¹MM') :
    (chartAt HJ x₀).target = Prod.fst ⁻¹' (chartAt (ModelProd H H') x₀.proj).target := by
  rw [FiberBundle.chartedSpace_chartAt]
  simp only [prodChartedSpace_chartAt,
    OpenPartialHomeomorph.trans_toPartialEquiv, OpenPartialHomeomorph.prod_toPartialHomeomorph,
    OpenPartialHomeomorph.refl_partialEquiv, PartialEquiv.trans_target, PartialEquiv.prod_target,
    PartialEquiv.refl_target]
  erw [hom_trivializationAt_target]
  simp only [trivializationAt_pullBack_baseSet, TangentBundle.trivializationAt_baseSet]
  rcases x₀ with ⟨⟨m, m'⟩, φ⟩
  simp only [ContMDiffMap.coe_fst, ContMDiffMap.fst_apply, ContMDiffMap.coe_snd,
    ContMDiffMap.snd_apply]
  erw [prod_univ, inter_eq_left, prod_univ, PartialEquiv.prod_symm, PartialEquiv.prod_symm]
  rw [preimage_preimage, ← Set.prod_eq, PartialEquiv.refl_symm, PartialEquiv.prod_coe,
      PartialEquiv.refl_coe]
  have : (fun x : ModelProd (ModelProd H H') (E →SL[σ] E') ↦
      ((chartAt H m).toPartialEquiv.symm.prod (chartAt H' m').toPartialEquiv.symm) x.1) =
      (Prod.map (chartAt H m).symm (chartAt H' m').symm) ∘ Prod.fst := by
    ext x <;> rfl
  rw [this, preimage_comp, preimage_prod_map_prod]
  gcongr
  · exact (chartAt H m).target_subset_preimage_source
  · exact (chartAt H' m').target_subset_preimage_source

section Maps

set_option backward.isDefEq.respectTransparency false in
theorem contMDiff_oneJetBundle_proj :
    ContMDiff ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) (I.prod I') ∞ (π (E →L[𝕜] E') FJ¹MM') := by
  apply contMDiff_proj _

theorem ContMDiff.oneJetBundle_proj {f : N → J¹MM'}
    (hf : ContMDiff J ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) ∞ f) :
    ContMDiff J (I.prod I') ∞ fun x ↦ (f x).1 :=
  contMDiff_oneJetBundle_proj.comp hf

theorem ContMDiffAt.oneJetBundle_proj {f : N → J¹MM'} {x₀ : N}
    (hf : ContMDiffAt J ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) ∞ f x₀) :
    ContMDiffAt J (I.prod I') ∞ (fun x ↦ (f x).1) x₀ :=
  (contMDiff_oneJetBundle_proj _).comp x₀ hf

/-- The constructor of `OneJetBundle`, in case `Sigma.mk` will not give the right type. -/
@[simp]
def OneJetBundle.mk (x : M) (y : M') (f : OneJetSpace I I' (x, y)) : J¹MM' :=
  ⟨(x, y), f⟩

omit [IsManifold I ∞ M] [IsManifold I' ∞ M'] in
@[simp, mfld_simps]
theorem oneJetBundle_mk_fst {x : M} {y : M'} {f : OneJetSpace I I' (x, y)} :
    (OneJetBundle.mk x y f).1 = (x, y) :=
  rfl

omit [IsManifold I ∞ M] [IsManifold I' ∞ M'] in
@[simp, mfld_simps]
theorem oneJetBundle_mk_snd {x : M} {y : M'} {f : OneJetSpace I I' (x, y)} :
    (OneJetBundle.mk x y f).2 = f :=
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem contMDiffAt_oneJetBundle {f : N → J¹MM'} {x₀ : N} :
    ContMDiffAt J ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) ∞ f x₀ ↔
      CMDiffAt ∞ (fun x ↦ (f x).1.1) x₀ ∧
        CMDiffAt ∞ (fun x ↦ (f x).1.2) x₀ ∧
          ContMDiffAt J 𝓘(𝕜, E →L[𝕜] E') ∞
            (inTangentCoordinates I I' (fun x ↦ (f x).1.1) (fun x ↦ (f x).1.2) (fun x ↦ (f x).2)
              x₀) x₀ := by
  simp_rw [Bundle.contMDiffAt_totalSpace, contMDiffAt_prod_iff, and_assoc,
    oneJetBundle_trivializationAt]
  rfl

theorem contMDiffAt_oneJetBundle_mk {f : N → M} {g : N → M'} {ϕ : N → E →L[𝕜] E'} {x₀ : N} :
    ContMDiffAt J ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) ∞
        (fun x ↦ OneJetBundle.mk (f x) (g x) (ϕ x) : N → J¹MM') x₀ ↔
      CMDiffAt ∞ f x₀ ∧ CMDiffAt ∞ g x₀ ∧
        ContMDiffAt J 𝓘(𝕜, E →L[𝕜] E') ∞ (inTangentCoordinates I I' f g ϕ x₀) x₀ :=
  contMDiffAt_oneJetBundle

theorem ContMDiffAt.oneJetBundle_mk {f : N → M} {g : N → M'} {ϕ : N → E →L[𝕜] E'} {x₀ : N}
    (hf : CMDiffAt ∞ f x₀) (hg : CMDiffAt ∞ g x₀)
    (hϕ : ContMDiffAt J 𝓘(𝕜, E →L[𝕜] E') ∞ (inTangentCoordinates I I' f g ϕ x₀) x₀) :
    ContMDiffAt J ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) ∞
      (fun x ↦ OneJetBundle.mk (f x) (g x) (ϕ x) : N → J¹MM') x₀ :=
  contMDiffAt_oneJetBundle.mpr ⟨hf, hg, hϕ⟩

variable (I I')

/-- The one-jet extension of a function -/
def oneJetExt (f : M → M') : M → OneJetBundle I M I' M' := fun x ↦
  OneJetBundle.mk x (f x) (mfderiv% f x)

variable {I I'}

theorem ContMDiffAt.oneJetExt {f : M → M'} {x : M} (hf : CMDiffAt ∞ f x) :
    ContMDiffAt I ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) ∞ (oneJetExt I I' f) x :=
  contMDiffAt_id.oneJetBundle_mk hf (hf.mfderiv_const le_rfl)

theorem ContMDiff.oneJetExt {f : M → M'} (hf : CMDiff ∞ f) :
    ContMDiff I ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) ∞ (oneJetExt I I' f) :=
  fun x ↦ ((hf x).contMDiffAt univ_mem).oneJetExt

theorem ContinuousAt.inTangentCoordinates_comp {f : N → M} {g : N → M'} {h : N → N'}
    {ϕ' : N → E' →L[𝕜] F'} {ϕ : N → E →L[𝕜] E'} {x₀ : N} (hg : ContinuousAt g x₀) :
    inTangentCoordinates I J' f h (fun x ↦ ϕ' x ∘L ϕ x) x₀ =ᶠ[𝓝 x₀] fun x ↦
      inTangentCoordinates I' J' g h ϕ' x₀ x ∘L inTangentCoordinates I I' f g ϕ x₀ x := by
  refine eventually_of_mem (hg.preimage_mem_nhds <|
    (achart H' (g x₀)).1.open_source.mem_nhds <| mem_achart_source H' (g x₀))
    fun x hx ↦ ?_
  ext v
  beta_reduce
  simp_rw [inTangentCoordinates, inCoordinates,
    ContinuousLinearMap.comp_apply]
  rw [Trivialization.symmL_continuousLinearMapAt]
  · rfl
  exact hx

theorem ContMDiffAt.clm_comp_inTangentCoordinates {f : N → M} {g : N → M'} {h : N → N'}
    {ϕ' : N → E' →L[𝕜] F'} {ϕ : N → E →L[𝕜] E'} {n : N} (hg : ContinuousAt g n)
    (hϕ' : ContMDiffAt J 𝓘(𝕜, E' →L[𝕜] F') ∞ (inTangentCoordinates I' J' g h ϕ' n) n)
    (hϕ : ContMDiffAt J 𝓘(𝕜, E →L[𝕜] E') ∞ (inTangentCoordinates I I' f g ϕ n) n) :
    ContMDiffAt J 𝓘(𝕜, E →L[𝕜] F') ∞ (inTangentCoordinates I J' f h (fun n ↦ ϕ' n ∘L ϕ n) n) n :=
  (hϕ'.clm_comp hϕ).congr_of_eventuallyEq hg.inTangentCoordinates_comp

variable (I')

variable [IsManifold J ∞ N]

omit [IsManifold J' ∞ N'] in
theorem ContMDiffAt.oneJet_comp {f1 : N' → M} (f2 : N' → M') {f3 : N' → N} {x₀ : N'}
    {h : ∀ x : N', OneJetSpace I' J (f2 x, f3 x)} {g : ∀ x : N', OneJetSpace I I' (f1 x, f2 x)}
    (hh : ContMDiffAt J' ((I'.prod J).prod 𝓘(𝕜, E' →L[𝕜] F)) ∞
      (fun x ↦ OneJetBundle.mk _ _ (h x)) x₀)
    (hg : ContMDiffAt J' ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) ∞
      (fun x ↦ OneJetBundle.mk _ _ (g x)) x₀) :
    ContMDiffAt J' ((I.prod J).prod 𝓘(𝕜, E →L[𝕜] F)) ∞
      (fun x ↦ OneJetBundle.mk (f1 x) (f3 x) (h x ∘L g x) : N' → OneJetBundle I M J N) x₀ := by
  rw [contMDiffAt_oneJetBundle_mk] at hh hg ⊢
  exact ⟨hg.1, hh.2.1, hh.2.2.clm_comp_inTangentCoordinates hg.2.1.continuousAt hg.2.2⟩

omit [IsManifold J' ∞ N'] in
theorem ContMDiff.oneJet_comp {f1 : N' → M} (f2 : N' → M') {f3 : N' → N}
    {h : ∀ x : N', OneJetSpace I' J (f2 x, f3 x)} {g : ∀ x : N', OneJetSpace I I' (f1 x, f2 x)}
    (hh : ContMDiff J' ((I'.prod J).prod 𝓘(𝕜, E' →L[𝕜] F)) ∞ fun x ↦ OneJetBundle.mk _ _ (h x))
    (hg : ContMDiff J' ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) ∞ fun x ↦ OneJetBundle.mk _ _ (g x)) :
    ContMDiff J' ((I.prod J).prod 𝓘(𝕜, E →L[𝕜] F)) ∞
      (fun x ↦ OneJetBundle.mk (f1 x) (f3 x) (h x ∘L g x) : N' → OneJetBundle I M J N) :=
  fun x₀ ↦ hh.contMDiffAt.oneJet_comp I' f2 (hg x₀)

variable {I'}

set_option backward.isDefEq.respectTransparency false in
open Trivialization in
omit [IsManifold J ∞ N] in
theorem ContMDiff.oneJet_add {f : N → M} {g : N → M'} {ϕ ϕ' : ∀ x : N, OneJetSpace I I' (f x, g x)}
    (hϕ : ContMDiff J ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) ∞ fun x ↦ OneJetBundle.mk _ _ (ϕ x))
    (hϕ' : ContMDiff J ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) ∞ fun x ↦ OneJetBundle.mk _ _ (ϕ' x)) :
    ContMDiff J ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) ∞ fun x ↦
      OneJetBundle.mk (f x) (g x) (ϕ x + ϕ' x) := by
  intro x
  specialize hϕ x
  specialize hϕ' x
  rw [contMDiffAt_oneJetBundle_mk] at hϕ hϕ' ⊢
  refine ⟨hϕ.1, hϕ.2.1, ?_⟩
  -- Porting note: next 5 lines should be
  -- `simp_rw [inTangentCoordinates, inCoordinates, ContinuousLinearMap.add_comp,
  --           ContinuousLinearMap.comp_add]
  simp_rw +unfoldPartialApp [inTangentCoordinates, inCoordinates]
  conv =>
    enter [4, x, 2]
    rw [ContinuousLinearMap.add_comp]
  simp only [ContinuousLinearMap.comp_add]
  exact hϕ.2.2.add hϕ'.2.2

variable (I' J')

/-- A useful definition to define maps between two `OneJetBundle`s. -/
protected def OneJetBundle.map (f : M → N) (g : M' → N')
    (Dfinv : ∀ x : M, TangentSpace J (f x) →L[𝕜] TangentSpace I x) :
    OneJetBundle I M I' M' → OneJetBundle J N J' N' := fun p ↦
  OneJetBundle.mk (f p.1.1) (g p.1.2) ((mfderiv% g p.1.2 ∘L p.2) ∘L Dfinv p.1.1)

variable {I' J'}

set_option backward.isDefEq.respectTransparency false in
omit [IsManifold I ∞ M] [IsManifold I' ∞ M']
  [IsManifold I₂ ∞ M₂] [IsManifold I₃ ∞ M₃]
  [IsManifold J' ∞ N'] [IsManifold J ∞ N] in
theorem OneJetBundle.map_map {f₂ : N → M₂} {f : M → N} {g₂ : N' → M₃} {g : M' → N'}
    {Dfinv : ∀ x : M, TangentSpace J (f x) →L[𝕜] TangentSpace I x}
    {Df₂inv : ∀ x : N, TangentSpace I₂ (f₂ x) →L[𝕜] TangentSpace J x} {x : J¹MM'}
    (hg₂ : MDifferentiableAt J' I₃ g₂ (g x.1.2)) (hg : MDifferentiableAt I' J' g x.1.2) :
    OneJetBundle.map J' I₃ f₂ g₂ Df₂inv (OneJetBundle.map I' J' f g Dfinv x) =
      OneJetBundle.map I' I₃ (f₂ ∘ f) (g₂ ∘ g) (fun x ↦ Dfinv x ∘L Df₂inv (f x)) x := by
  ext
  · rfl
  · rfl
  · dsimp only [OneJetBundle.map, OneJetBundle.mk]
    simp_rw [← ContinuousLinearMap.comp_assoc, mfderiv_comp x.1.2 hg₂ hg]

omit [IsManifold I ∞ M] [IsManifold I' ∞ M']
  [IsManifold I₂ ∞ M₂] [IsManifold I₃ ∞ M₃]
  [IsManifold J' ∞ N'] [IsManifold J ∞ N] in
theorem OneJetBundle.map_id (x : J¹MM') :
    OneJetBundle.map I' I' id id (fun x ↦ ContinuousLinearMap.id 𝕜 (TangentSpace I x)) x = x := by
  -- Porting note: was `ext _` in Lean 3
  ext
  · rfl
  · rfl
  dsimp only [OneJetBundle.map, OneJetBundle.mk]
  simp_rw [mfderiv_id]
  -- note: rw fails since we have to unfold the type `Bundle.Pullback`
  erw [ContinuousLinearMap.id_comp]

theorem ContMDiffAt.oneJetBundle_map {f : M'' → M → N} {g : M'' → M' → N'} {x₀ : M''}
    {Dfinv : ∀ (z : M'') (x : M), TangentSpace J (f z x) →L[𝕜] TangentSpace I x} {k : M'' → J¹MM'}
    (hf : ContMDiffAt (I''.prod I) J ∞ f.uncurry (x₀, (k x₀).1.1))
    (hg : ContMDiffAt (I''.prod I') J' ∞ g.uncurry (x₀, (k x₀).1.2))
    (hDfinv :
      ContMDiffAt I'' 𝓘(𝕜, F →L[𝕜] E) ∞
        (inTangentCoordinates J I (fun x ↦ f x (k x).1.1) (fun x ↦ (k x).1.1)
          (fun x ↦ Dfinv x (k x).1.1) x₀)
        x₀)
    (hk : ContMDiffAt I'' ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) ∞ k x₀) :
    ContMDiffAt I'' ((J.prod J').prod 𝓘(𝕜, F →L[𝕜] F')) ∞
      (fun z ↦ OneJetBundle.map I' J' (f z) (g z) (Dfinv z) (k z)) x₀ := by
  rw [contMDiffAt_oneJetBundle] at hk
  refine ContMDiffAt.oneJet_comp _ _ ?_ ?_
  · refine ContMDiffAt.oneJet_comp _ _ ?_ ?_
    · refine hk.2.1.oneJetBundle_mk (hg.comp x₀ (contMDiffAt_id.prodMk hk.2.1)) ?_
      exact ContMDiffAt.mfderiv g (fun x ↦ (k x).1.2) hg hk.2.1 le_rfl
    · exact hk.1.oneJetBundle_mk hk.2.1 hk.2.2
  apply (hf.comp x₀ (contMDiffAt_id.prodMk hk.1)).oneJetBundle_mk hk.1
  apply hDfinv


/-- A useful definition to define maps between two `OneJetBundle`s. -/
def mapLeft (f : M → N) (Dfinv : ∀ x : M, TangentSpace J (f x) →L[𝕜] TangentSpace I x) :
    J¹MM' → OneJetBundle J N I' M' := fun p ↦ OneJetBundle.mk (f p.1.1) p.1.2 (p.2 ∘L Dfinv p.1.1)

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.multiGoal false in
omit [IsManifold I ∞ M] [IsManifold I' ∞ M']
  [IsManifold I₂ ∞ M₂] [IsManifold I₃ ∞ M₃]
  [IsManifold J' ∞ N'] [IsManifold J ∞ N] in
theorem mapLeft_eq_map (f : M → N) (Dfinv : ∀ x : M, TangentSpace J (f x) →L[𝕜] TangentSpace I x) :
    mapLeft f Dfinv = OneJetBundle.map I' I' f (id : M' → M') Dfinv := by
  ext x; rfl; rfl; dsimp only [OneJetBundle.map, mapLeft, oneJetBundle_mk_snd]
  simp_rw [mfderiv_id, ContinuousLinearMap.id_comp]

theorem ContMDiffAt.mapLeft {f : N' → M → N} {x₀ : N'}
    {Dfinv : ∀ (z : N') (x : M), TangentSpace J (f z x) →L[𝕜] TangentSpace I x} {g : N' → J¹MM'}
    (hf : ContMDiffAt (J'.prod I) J ∞ f.uncurry (x₀, (g x₀).1.1))
    (hDfinv :
      ContMDiffAt J' 𝓘(𝕜, F →L[𝕜] E) ∞
        (inTangentCoordinates J I (fun x ↦ f x (g x).1.1) (fun x ↦ (g x).1.1)
          (fun x ↦ Dfinv x (g x).1.1) x₀)
        x₀)
    (hg : ContMDiffAt J' ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) ∞ g x₀) :
    ContMDiffAt J' ((J.prod I').prod 𝓘(𝕜, F →L[𝕜] E')) ∞
      (fun z ↦ mapLeft (f z) (Dfinv z) (g z)) x₀ := by
  simp_rw [mapLeft_eq_map]; exact hf.oneJetBundle_map contMDiffAt_snd hDfinv hg

/-- The projection `J¹(E × P, F) → J¹(E, F)`. Not actually used. -/
def bundleFst : OneJetBundle (J.prod I) (N × M) I' M' → OneJetBundle J N I' M' :=
  mapLeft Prod.fst fun _ ↦ ContinuousLinearMap.inl 𝕜 F E

/-- The projection `J¹(P × E, F) → J¹(E, F)`. -/
def bundleSnd : OneJetBundle (J.prod I) (N × M) I' M' → J¹MM' :=
  mapLeft Prod.snd fun x ↦ mfderiv I (J.prod I) (fun y ↦ (x.1, y)) x.2

omit [IsManifold I ∞ M] [IsManifold I' ∞ M']
  [IsManifold I₂ ∞ M₂] [IsManifold I₃ ∞ M₃]
  [IsManifold J' ∞ N'] [IsManifold J ∞ N] in
theorem bundleSnd_eq (x : OneJetBundle (J.prod I) (N × M) I' M') :
    bundleSnd x = (mapLeft Prod.snd (fun _ ↦ ContinuousLinearMap.inr 𝕜 F E) x : J¹MM') := by
  simp_rw [bundleSnd, mfderiv_prod_right]; rfl

theorem contMDiff_bundleSnd :
    ContMDiff (((J.prod I).prod I').prod 𝓘(𝕜, F × E →L[𝕜] E')) ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E'))
      ∞ (bundleSnd : OneJetBundle (J.prod I) (N × M) I' M' → J¹MM') := by
  intro x₀
  refine ContMDiffAt.mapLeft contMDiffAt_snd.snd ?_ contMDiffAt_id
  have : ContMDiffAt (((J.prod I).prod I').prod 𝓘(𝕜, F × E →L[𝕜] E')) 𝓘(𝕜, E →L[𝕜] F × E) ∞
      (inTangentCoordinates I (J.prod I) _ _ _ x₀) x₀ :=
    ContMDiffAt.mfderiv (n := ∞)
      (fun (x : OneJetBundle (J.prod I) (N × M) I' M') (y : M) ↦ (x.1.1.1, y))
      (fun x : OneJetBundle (J.prod I) (N × M) I' M' ↦ x.1.1.2) ?_ ?_ le_rfl
  · exact this
  · exact (contMDiff_oneJetBundle_proj.fst.fst.prodMap contMDiff_id).contMDiffAt
  · exact contMDiff_oneJetBundle_proj.fst.snd.contMDiffAt

-- slow
end Maps

-- move
theorem partialEquiv_eq_equiv {α β} {f : PartialEquiv α β} {e : α ≃ β} (h1 : ∀ x, f x = e x)
    (h2 : f.source = univ) (h3 : f.target = univ) : f = e.toPartialEquiv := by
  refine PartialEquiv.ext h1 (fun y ↦ ?_) h2
  conv_rhs => rw [← f.right_inv ((Set.ext_iff.mp h3 y).mpr (mem_univ y)), h1]
  exact (e.left_inv _).symm

@[inherit_doc] local notation "𝓜" => ModelProd (ModelProd H H') (E →L[𝕜] E')

/-- In the `OneJetBundle` to the model space, the charts are just the canonical identification
between a product type and a bundle total space type, a.k.a. `Bundle.TotalSpace.toProd`. -/
@[simp, mfld_simps]
theorem oneJetBundle_model_space_chartAt (p : OneJetBundle I H I' H') :
    (chartAt 𝓜 p).toPartialEquiv =
      (Bundle.TotalSpace.toProd (H × H') (E →L[𝕜] E')).toPartialEquiv := by
  apply partialEquiv_eq_equiv
  · intro x
    rw [OpenPartialHomeomorph.coe_toPartialEquiv, oneJetBundle_chartAt_apply p x,
      inCoordinates_tangent_bundle_core_model_space]
    ext <;> rfl
  · simp_rw [oneJetBundle_chart_source, prodChartedSpace_chartAt, chartAt_self_eq,
      OpenPartialHomeomorph.refl_prod_refl]
    rfl
  · simp_rw [oneJetBundle_chart_target, prodChartedSpace_chartAt, chartAt_self_eq,
      OpenPartialHomeomorph.refl_prod_refl]
    rfl

@[simp, mfld_simps]
theorem oneJetBundle_model_space_coe_chartAt (p : OneJetBundle I H I' H') :
    ⇑(chartAt 𝓜 p) = Bundle.TotalSpace.toProd (H × H') (E →L[𝕜] E') := by
  ext q e
  · rfl
  · rfl
  · rw [oneJetBundle_chartAt_apply, TotalSpace.toProd_apply,
        inCoordinates_tangent_bundle_core_model_space]

@[simp, mfld_simps]
theorem oneJetBundle_model_space_coe_chartAt_symm (p : OneJetBundle I H I' H') :
    ((chartAt 𝓜 p).symm : 𝓜 → OneJetBundle I H I' H') =
      (Bundle.TotalSpace.toProd (H × H') (E →L[𝕜] E')).symm := by
  ext x
  · rfl
  · rfl
  · rw [← OpenPartialHomeomorph.coe_toPartialEquiv_symm, oneJetBundle_model_space_chartAt]
    rfl

variable (I I')

-- note: this proof works for all vector bundles where we have proven
-- `∀ p, chartAt _ p = f.toPartialEquiv`
set_option backward.isDefEq.respectTransparency false in
/-- The canonical identification between the one-jet bundle to the model space and the product,
as a homeomorphism -/
def oneJetBundleModelSpaceHomeomorph : OneJetBundle I H I' H' ≃ₜ 𝓜 :=
  { Bundle.TotalSpace.toProd (H × H') (E →L[𝕜] E') with
    continuous_toFun := by
      let p : OneJetBundle I H I' H' := ⟨(I.symm (0 : E), I'.symm (0 : E')), 0⟩
      have : Continuous (chartAt 𝓜 p) := by
        rw [← continuousOn_univ]
        convert OpenPartialHomeomorph.continuousOn _
        simp only [mfld_simps]
      simpa only [mfld_simps] using this
    continuous_invFun := by
      let p : OneJetBundle I H I' H' := ⟨(I.symm (0 : E), I'.symm (0 : E')), 0⟩
      have : Continuous (chartAt 𝓜 p).symm := by
        rw [← continuousOn_univ]
        convert OpenPartialHomeomorph.continuousOn _
        simp only [mfld_simps]
      simpa only [mfld_simps] using this }

-- unused
@[simp, mfld_simps]
theorem oneJetBundleModelSpaceHomeomorph_coe :
    (oneJetBundleModelSpaceHomeomorph I I' : OneJetBundle I H I' H' → 𝓜) =
      Bundle.TotalSpace.toProd (H × H') (E →L[𝕜] E') :=
  rfl

-- unused
@[simp, mfld_simps]
theorem oneJetBundleModelSpaceHomeomorph_coe_symm :
    ((oneJetBundleModelSpaceHomeomorph I I').symm : 𝓜 → OneJetBundle I H I' H') =
      (Bundle.TotalSpace.toProd (H × H') (E →L[𝕜] E')).symm :=
  rfl

end
