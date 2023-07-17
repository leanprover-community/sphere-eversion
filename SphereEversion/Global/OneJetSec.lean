/-
Copyright (c) 2022 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Floris van Doorn

! This file was ported from Lean 3 source module global.one_jet_sec
-/
import SphereEversion.Global.OneJetBundle

/-!
# Sections of 1-jet bundles

In this file we study sections of 1-jet bundles. This is the direct continuation
of `one_jet_bundle.lean` but it imports more files, hence the cut.

## Main definitions

In this file we consider two manifolds `M` and `M'` with models `I` and `I'`

* `one_jet_sec I M I' M'`: smooth sections of `one_jet_bundle I M I' M' → M`
-/


noncomputable section

open Set Function Filter ChartedSpace SmoothManifoldWithCorners

open scoped Topology Manifold

section General

variable {𝕜 : Type _} [NontriviallyNormedField 𝕜]
  -- declare a smooth manifold `M` over the pair `(E, H)`.
  {E : Type _}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type _} [TopologicalSpace H]
  (I : ModelWithCorners 𝕜 E H) {M : Type _} [TopologicalSpace M] [ChartedSpace H M]
  [SmoothManifoldWithCorners I M]
  -- declare a smooth manifold `M'` over the pair `(E', H')`.
  {E' : Type _}
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type _} [TopologicalSpace H']
  (I' : ModelWithCorners 𝕜 E' H') {M' : Type _} [TopologicalSpace M'] [ChartedSpace H' M']
  [SmoothManifoldWithCorners I' M']

variable (I M I' M')

/-- A section of a 1-jet bundle seen as a bundle over the source manifold. -/
@[ext]
structure OneJetSec where
  bs : M → M'
  ϕ : ∀ x : M, TangentSpace I x →L[𝕜] TangentSpace I' (bs x)
  smooth' : Smooth I ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) fun x => OneJetBundle.mk x (bs x) (ϕ x)

instance : CoeFun (OneJetSec I M I' M') fun S => M → OneJetBundle I M I' M' :=
  ⟨fun S x => OneJetBundle.mk x (S.bs x) (S.ϕ x)⟩

variable {I M I' M'}

namespace OneJetSec

protected def mk' (F : M → OneJetBundle I M I' M') (hF : ∀ m, (F m).1.1 = m)
    (h2F : Smooth I ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) F) : OneJetSec I M I' M' :=
  ⟨fun x => (F x).1.2, fun x => (F x).2, by convert h2F; ext m; exact (hF m).symm; rfl; rfl⟩

theorem coe_apply (F : OneJetSec I M I' M') (x : M) : F x = ⟨(x, F.bs x), F.ϕ x⟩ :=
  rfl

theorem fst_eq (F : OneJetSec I M I' M') (x : M) : (F x).1 = (x, F.bs x) :=
  rfl

theorem snd_eq (F : OneJetSec I M I' M') (x : M) : (F x).2 = F.ϕ x :=
  rfl

theorem is_sec (F : OneJetSec I M I' M') (x : M) : (F x).1.1 = x :=
  rfl

theorem bs_eq (F : OneJetSec I M I' M') (x : M) : F.bs x = (F x).1.2 :=
  rfl

protected theorem smooth (F : OneJetSec I M I' M') :
    Smooth I ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) F :=
  F.smooth'

theorem smooth_eta (F : OneJetSec I M I' M') :
    Smooth I ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E'))
      (fun x => OneJetBundle.mk x (F.bs x) (F x).2 : M → OneJetBundle I M I' M') :=
  F.Smooth

theorem smooth_bs (F : OneJetSec I M I' M') : Smooth I I' F.bs :=
  smooth_one_jet_bundle_proj.snd.comp F.smooth

/-- A section of J¹(M, M') is holonomic at (x : M) if its linear map part is the derivative
of its base map at x. -/
def IsHolonomicAt (F : OneJetSec I M I' M') (x : M) : Prop :=
  mfderiv I I' F.bs x = (F x).2

/-- A section of J¹(M, M') is holonomic at (x : M) iff it coincides with the 1-jet extension of
its base map at x. -/
theorem isHolonomicAt_iff {F : OneJetSec I M I' M'} {x : M} :
    F.IsHolonomicAt x ↔ oneJetExt I I' F.bs x = F x := by
  simp_rw [is_holonomic_at, oneJetExt, Bundle.TotalSpace.ext_iff, heq_iff_eq, F.fst_eq,
    one_jet_bundle_mk_fst, eq_self_iff_true, true_and_iff, one_jet_bundle_mk_snd]

theorem isHolonomicAt_congr {F F' : OneJetSec I M I' M'} {x : M} (h : F =ᶠ[𝓝 x] F') :
    F.IsHolonomicAt x ↔ F'.IsHolonomicAt x :=
  by
  simp_rw [is_holonomic_at]
  rw [← h.self_of_nhds]
  congr 2
  exact (h.fun_comp fun x => x.1.2).mfderiv_eq

theorem IsHolonomicAt.congr {F F' : OneJetSec I M I' M'} {x : M} (hF : F.IsHolonomicAt x)
    (h : F =ᶠ[𝓝 x] F') : F'.IsHolonomicAt x :=
  (isHolonomicAt_congr h).mp hF

/-- A map from M to J¹(M, M') is holonomic if its linear map part is the derivative
of its base map at every point. -/
def IsHolonomic (F : OneJetSec I M I' M') : Prop :=
  ∀ x, F.IsHolonomicAt x

end OneJetSec

def IsHolonomicGerm {x : M} (φ : Germ (𝓝 x) (OneJetBundle I M I' M')) : Prop :=
  Quotient.liftOn' φ (fun F => mfderiv I I' (fun x' => (F x').1.2) x = (F x).2)
    (by
      letI : Setoid (M → OneJetBundle I M I' M') := (𝓝 x).germSetoid (OneJetBundle I M I' M')
      have key :
        ∀ f g,
          f ≈ g →
            (fun F : M → OneJetBundle I M I' M' =>
                  mfderiv I I' (fun x' : M => (F x').proj.snd) x = (F x).snd)
                f →
              (fun F : M → OneJetBundle I M I' M' =>
                  mfderiv I I' (fun x' : M => (F x').proj.snd) x = (F x).snd)
                g :=
        by
        intro f g hfg hf
        have hfg' : (fun x' => (f x').1.2) =ᶠ[𝓝 x] fun x' => (g x').1.2 :=
          hfg.fun_comp fun s => s.1.2
        rw [← hfg'.mfderiv_eq, hf, hfg.self_of_nhds]
      exact fun f g H => propext ⟨key f g H, key g f H.symm⟩)

/-- The one-jet extension of a function, seen as a section of the 1-jet bundle. -/
def oneJetExtSec (f : C^∞⟮I, M; I', M'⟯) : OneJetSec I M I' M' :=
  ⟨f, mfderiv I I' f, f.smooth.oneJetExt⟩

end General

section Real

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type _} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) (M : Type _) [TopologicalSpace M] [ChartedSpace H M]
  [SmoothManifoldWithCorners I M] {E' : Type _} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type _} [TopologicalSpace H'] (I' : ModelWithCorners ℝ E' H') (M' : Type _)
  [TopologicalSpace M'] [ChartedSpace H' M'] [SmoothManifoldWithCorners I' M'] {F : Type _}
  [NormedAddCommGroup F] [NormedSpace ℝ F] {G : Type _} [TopologicalSpace G]
  (J : ModelWithCorners ℝ F G) (N : Type _) [TopologicalSpace N] [ChartedSpace G N]
  [SmoothManifoldWithCorners J N] {F' : Type _} [NormedAddCommGroup F'] [NormedSpace ℝ F']
  {G' : Type _} [TopologicalSpace G'] (J' : ModelWithCorners ℝ F' G') (N' : Type _)
  [TopologicalSpace N'] [ChartedSpace G' N'] [SmoothManifoldWithCorners J' N'] {EP : Type _}
  [NormedAddCommGroup EP] [NormedSpace ℝ EP] {HP : Type _} [TopologicalSpace HP]
  {IP : ModelWithCorners ℝ EP HP} {P : Type _} [TopologicalSpace P] [ChartedSpace HP P]
  [SmoothManifoldWithCorners IP P]

/-- A family of jet sections indexed by manifold `N` is a function from `N` into jet sections
  in such a way that the function is smooth as a function of all arguments. -/
structure FamilyOneJetSec where
  bs : N → M → M'
  ϕ : ∀ (n : N) (m : M), TangentSpace I m →L[ℝ] TangentSpace I' (bs n m)
  smooth' :
    Smooth (J.prod I) ((I.prod I').prod 𝓘(ℝ, E →L[ℝ] E')) fun p : N × M =>
      OneJetBundle.mk p.2 (bs p.1 p.2) (ϕ p.1 p.2)

instance : CoeFun (FamilyOneJetSec I M I' M' J N) fun S => N → OneJetSec I M I' M' :=
  ⟨fun S t =>
    { bs := S.bs t
      ϕ := S.ϕ t
      smooth' := fun x => (S.smooth' (t, x)).comp x <| smoothAt_const.prod_mk smoothAt_id }⟩

namespace FamilyOneJetSec

variable {I M I' M' J N J' N'}

protected def mk' (FF : N → M → OneJetBundle I M I' M') (hF : ∀ n m, (FF n m).1.1 = m)
    (h2F : Smooth (J.prod I) ((I.prod I').prod 𝓘(ℝ, E →L[ℝ] E')) (uncurry FF)) :
    FamilyOneJetSec I M I' M' J N :=
  ⟨fun s x => (FF s x).1.2, fun s x => (FF s x).2, by convert h2F; ext ⟨s, m⟩; exact (hF s m).symm;
    rfl; rfl⟩

theorem coe_mk' (FF : N → M → OneJetBundle I M I' M') (hF : ∀ n m, (FF n m).1.1 = m)
    (h2F : Smooth (J.prod I) ((I.prod I').prod 𝓘(ℝ, E →L[ℝ] E')) (uncurry FF)) (x : N) :
    FamilyOneJetSec.mk' FF hF h2F x =
      OneJetSec.mk' (FF x) (hF x) (h2F.comp (smooth_const.prod_mk smooth_id)) :=
  rfl

@[simp]
theorem bs_eq_coe_bs (S : FamilyOneJetSec I M I' M' J N) (s : N) : S.bs s = (S s).bs :=
  rfl

theorem bs_eq (S : FamilyOneJetSec I M I' M' J N) (s : N) (x : M) : S.bs s x = (S s x).1.2 :=
  rfl

@[simp]
theorem coe_ϕ (S : FamilyOneJetSec I M I' M' J N) (s : N) : (S s).ϕ = S.ϕ s :=
  rfl

protected theorem smooth (S : FamilyOneJetSec I M I' M' J N) :
    Smooth (J.prod I) ((I.prod I').prod 𝓘(ℝ, E →L[ℝ] E')) fun p : N × M => S p.1 p.2 :=
  S.smooth'

theorem smooth_bs (S : FamilyOneJetSec I M I' M' J N) :
    Smooth (J.prod I) I' fun p : N × M => S.bs p.1 p.2 :=
  smooth_one_jet_bundle_proj.snd.comp S.smooth

theorem smooth_coe_bs (S : FamilyOneJetSec I M I' M' J N) {p : N} : Smooth I I' (S.bs p) :=
  (S p).smooth_bs

/-- Reindex a family along a smooth function `f`. -/
def reindex (S : FamilyOneJetSec I M I' M' J' N') (f : C^∞⟮J, N; J', N'⟯) :
    FamilyOneJetSec I M I' M' J N where
  bs t := S.bs (f t)
  ϕ t := S.ϕ (f t)
  smooth' x := (S.smooth' (f x.1, x.2)).comp x <| f.smooth.smoothAt.prod_map' smoothAt_id

/-- Turn a family of sections of `J¹(M, M')` parametrized by `N` into a section of `J¹(N × M, M')`.
-/
@[simps]
def uncurry (S : FamilyOneJetSec I M I' M' IP P) : OneJetSec (IP.prod I) (P × M) I' M'
    where
  bs p := S.bs p.1 p.2
  ϕ p :=
    (show EP × E →L[ℝ] E' from mfderiv (IP.prod I) I' (fun z : P × M => S.bs z.1 p.2) p) +
      S.ϕ p.1 p.2 ∘L mfderiv (IP.prod I) I Prod.snd p
  smooth' := by
    refine' Smooth.one_jet_add _ _
    · intro y
      refine' smooth_at_id.one_jet_bundle_mk (S.smooth_bs y) _
      have :
        SmoothAt ((IP.prod I).prod (IP.prod I)) I'
          (Function.uncurry fun x z : P × M => S.bs z.1 x.2) (y, y) :=
        S.smooth_bs.comp (smooth_snd.fst.prod_mk smooth_fst.snd) (y, y)
      apply ContMDiffAt.mfderiv (fun x z : P × M => S.bs z.1 x.2) id this contMDiffAt_id le_top
    · refine' Smooth.one_jet_comp I (fun p => p.2) S.smooth smooth_snd.one_jet_ext

theorem uncurry_ϕ' (S : FamilyOneJetSec I M I' M' IP P) (p : P × M) :
    S.uncurry.ϕ p =
      mfderiv IP I' (fun z => S.bs z p.2) p.1 ∘L ContinuousLinearMap.fst ℝ EP E +
        S.ϕ p.1 p.2 ∘L ContinuousLinearMap.snd ℝ EP E :=
  by
  simp_rw [S.uncurry_ϕ, mfderiv_snd]
  congr 1
  convert
    mfderiv_comp p ((S.smooth_bs.comp (smooth_id.prod_mk smooth_const)).MDifferentiable p.1)
      (smooth_fst.mdifferentiable p)
  simp_rw [mfderiv_fst]
  rfl

theorem is_holonomic_uncurry (S : FamilyOneJetSec I M I' M' IP P) {p : P × M} :
    S.uncurry.IsHolonomicAt p ↔ (S p.1).IsHolonomicAt p.2 :=
  by
  simp_rw [OneJetSec.IsHolonomicAt, OneJetSec.snd_eq, S.uncurry_ϕ]
  rw [show S.uncurry.bs = fun x => S.uncurry.bs x from rfl, funext S.uncurry_bs]
  simp_rw [mfderiv_prod_eq_add _ _ _ (S.smooth_bs.mdifferentiable _), mfderiv_snd, add_right_inj]
  dsimp only
  rw [mfderiv_comp p S.smooth_coe_bs.mdifferentiable_at smooth_snd.mdifferentiable_at, mfderiv_snd]
  exact
    (show surjective (ContinuousLinearMap.snd ℝ EP E) from
          Prod.snd_surjective).clm_comp_injective.eq_iff

end FamilyOneJetSec

/-- A homotopy of 1-jet sections is a family of 1-jet sections indexed by `ℝ` -/
@[reducible]
def HtpyOneJetSec :=
  FamilyOneJetSec I M I' M' 𝓘(ℝ, ℝ) ℝ

example : CoeFun (HtpyOneJetSec I M I' M') fun S => ℝ → OneJetSec I M I' M' := by infer_instance

end Real

