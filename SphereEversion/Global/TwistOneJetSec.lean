/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth

! This file was ported from Lean 3 source module global.twist_one_jet_sec
-/
import SphereEversion.Global.OneJetSec

noncomputable section

open Set Equiv Bundle ContinuousLinearMap

open scoped Manifold Bundle Topology

section ArbitraryField

variable {𝕜 : Type _} [NontriviallyNormedField 𝕜] {E : Type _} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type _} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) (M : Type _)
  [TopologicalSpace M] [ChartedSpace H M] [SmoothManifoldWithCorners I M] {F : Type _}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type _} [TopologicalSpace G]
  {J : ModelWithCorners 𝕜 F G} {N : Type _} [TopologicalSpace N] [ChartedSpace G N]
  [SmoothManifoldWithCorners J N] (V : Type _) [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  (V' : Type _) [NormedAddCommGroup V'] [NormedSpace 𝕜 V']

/- Given a smooth manifold `M` and a normed space `V`, the total space of the bundle Hom(TM, V) of
homomorphisms from TM to V. This is naturally a smooth manifold. -/
local notation "σ" => RingHom.id 𝕜

local notation "FJ¹MV" =>
  Bundle.ContinuousLinearMap σ (TangentSpace I : M → Type _) (Bundle.Trivial M V)

local notation "J¹MV" => TotalSpace (E →L[𝕜] V) FJ¹MV

section Smoothness

variable {I M V} {f : N → J¹MV}

-- todo: remove or use to prove `smooth_at_one_jet_eucl_bundle`
theorem smoothAt_one_jet_eucl_bundle' {x₀ : N} :
    SmoothAt J (I.prod 𝓘(𝕜, E →L[𝕜] V)) f x₀ ↔
      SmoothAt J I (fun x => (f x).1) x₀ ∧
        SmoothAt J 𝓘(𝕜, E →L[𝕜] V)
          (fun x =>
            show E →L[𝕜] V from
              (f x).2 ∘L
                (trivializationAt E (TangentSpace I : M → Type _) (f x₀).1).symmL 𝕜 (f x).1)
          x₀ :=
  by
  simp_rw [smoothAt_hom_bundle, in_coordinates, trivial.trivialization_at,
    trivial.trivialization_continuous_linear_map_at]
  dsimp only [Bundle.Trivial]
  simp_rw [ContinuousLinearMap.id_comp]

theorem smoothAt_one_jet_eucl_bundle {x₀ : N} :
    SmoothAt J (I.prod 𝓘(𝕜, E →L[𝕜] V)) f x₀ ↔
      SmoothAt J I (fun x => (f x).1) x₀ ∧
        SmoothAt J 𝓘(𝕜, E →L[𝕜] V)
          (fun x =>
            show E →L[𝕜] V from
              (f x).2 ∘L (trivializationAt E (TangentSpace I) (f x₀).proj).symmL 𝕜 (f x).proj)
          x₀ :=
  by
  rw [smoothAt_hom_bundle, and_congr_right_iff]
  intro hf
  refine' Filter.EventuallyEq.contMDiffAt_iff _
  have :=
    hf.continuous_at.preimage_mem_nhds
      (((tangentBundleCore I M).isOpen_baseSet (achart H (f x₀).proj)).mem_nhds
        ((tangentBundleCore I M).mem_baseSet_at (f x₀).proj))
  filter_upwards [this] with x hx
  simp_rw [in_coordinates, trivial.trivialization_at,
    trivial.trivialization_continuous_linear_map_at, ← ContinuousLinearMap.comp_assoc]
  dsimp only [Bundle.Trivial]
  simp_rw [ContinuousLinearMap.id_comp]

theorem SmoothAt.one_jet_eucl_bundle_mk' {f : N → M} {ϕ : N → E →L[𝕜] V} {x₀ : N}
    (hf : SmoothAt J I f x₀)
    (hϕ :
      SmoothAt J 𝓘(𝕜, E →L[𝕜] V)
        (fun x =>
          show E →L[𝕜] V from
            ϕ x ∘L (trivializationAt E (TangentSpace I : M → Type _) (f x₀)).symmL 𝕜 (f x))
        x₀) :
    SmoothAt J (I.prod 𝓘(𝕜, E →L[𝕜] V)) (fun x => Bundle.TotalSpace.mk (f x) (ϕ x) : N → J¹MV) x₀ :=
  smoothAt_one_jet_eucl_bundle'.mpr ⟨hf, hϕ⟩

theorem SmoothAt.one_jet_eucl_bundle_mk {f : N → M} {ϕ : N → E →L[𝕜] V} {x₀ : N}
    (hf : SmoothAt J I f x₀)
    (hϕ :
      SmoothAt J 𝓘(𝕜, E →L[𝕜] V)
        (fun x =>
          show E →L[𝕜] V from ϕ x ∘L (trivializationAt E (TangentSpace I) (f x₀)).symmL 𝕜 (f x))
        x₀) :
    SmoothAt J (I.prod 𝓘(𝕜, E →L[𝕜] V)) (fun x => Bundle.TotalSpace.mk (f x) (ϕ x) : N → J¹MV) x₀ :=
  smoothAt_one_jet_eucl_bundle.mpr ⟨hf, hϕ⟩

end Smoothness

section Sections

/-- A section of a 1-jet bundle seen as a bundle over the source manifold. -/
@[ext]
structure OneJetEuclSec where
  toFun : M → J¹MV
  is_sec' : ∀ p, (to_fun p).1 = p
  smooth' : Smooth I (I.prod 𝓘(𝕜, E →L[𝕜] V)) to_fun

variable {I M V}

instance : CoeFun (OneJetEuclSec I M V) fun S => M → J¹MV :=
  ⟨fun S x => S.toFun x⟩

@[simp]
theorem OneJetEuclSec.is_sec (s : OneJetEuclSec I M V) (p : M) : (s p).1 = p :=
  s.is_sec' p

@[simp]
theorem OneJetEuclSec.smooth (s : OneJetEuclSec I M V) : Smooth I (I.prod 𝓘(𝕜, E →L[𝕜] V)) s :=
  s.smooth'

end Sections

section proj

instance piBugInstanceRestatement (x : M) :
    TopologicalSpace (Bundle.ContinuousLinearMap σ (TangentSpace I) (trivial M V) x) := by
  infer_instance

instance piBugInstanceRestatement2 (x : M × V) : TopologicalSpace (OneJetSpace I 𝓘(𝕜, V) x) := by
  infer_instance

/- Given a smooth manifold `M` and a normed space `V`, there is a canonical projection from the
one-jet bundle of maps from `M` to `V` to the bundle of homomorphisms from `TM` to `V`. This is
constructed using the fact that each tangent space to `V` is canonically isomorphic to `V`. -/
def proj (v : OneJetBundle I M 𝓘(𝕜, V) V) : J¹MV :=
  ⟨v.1.1, v.2⟩

theorem smooth_proj :
    Smooth ((I.prod 𝓘(𝕜, V)).prod 𝓘(𝕜, E →L[𝕜] V)) (I.prod 𝓘(𝕜, E →L[𝕜] V)) (proj I M V) :=
  by
  intro x₀
  have : SmoothAt ((I.prod 𝓘(𝕜, V)).prod 𝓘(𝕜, E →L[𝕜] V)) _ id x₀ := smoothAt_id
  simp_rw [smoothAt_oneJetBundle, inTangentCoordinates, in_coordinates, tangentBundleCore_indexAt,
    TangentBundle.continuousLinearMapAt_model_space, ContinuousLinearMap.one_def] at this
  dsimp only [TangentSpace] at this
  simp_rw [ContinuousLinearMap.id_comp] at this
  refine' this.1.one_jet_eucl_bundle_mk this.2.2

variable {I M V}

def drop (s : OneJetSec I M 𝓘(𝕜, V) V) : OneJetEuclSec I M V
    where
  toFun := (proj I M V).comp s
  is_sec' p := rfl
  smooth' := (smooth_proj I M V).comp s.smooth

end proj

section incl

/- Given a smooth manifold `M` and a normed space `V`, there is a canonical map from the
the product with V of the bundle of homomorphisms from `TM` to `V` to the one-jet bundle of maps
from `M` to `V`. In fact this map is a diffeomorphism.  This is constructed using the fact that each
tangent space to `V` is canonically isomorphic to `V`. -/
def incl (v : J¹MV × V) : OneJetBundle I M 𝓘(𝕜, V) V :=
  ⟨(v.1.1, v.2), v.1.2⟩

theorem smooth_incl :
    Smooth ((I.prod 𝓘(𝕜, E →L[𝕜] V)).prod 𝓘(𝕜, V)) ((I.prod 𝓘(𝕜, V)).prod 𝓘(𝕜, E →L[𝕜] V))
      (incl I M V) :=
  by
  intro x₀
  have : SmoothAt ((I.prod 𝓘(𝕜, E →L[𝕜] V)).prod 𝓘(𝕜, V)) _ Prod.fst x₀ := smoothAt_fst
  rw [smoothAt_one_jet_eucl_bundle] at this
  refine' this.1.oneJetBundle_mk smoothAt_snd _
  dsimp only [inTangentCoordinates, in_coordinates, TangentSpace]
  simp_rw [TangentBundle.continuousLinearMapAt_model_space, ContinuousLinearMap.one_def,
    ContinuousLinearMap.id_comp]
  exact this.2

@[simp]
theorem incl_fst_fst (v : J¹MV × V) : (incl I M V v).1.1 = v.1.1 :=
  rfl

@[simp]
theorem incl_snd (v : J¹MV × V) : (incl I M V v).1.2 = v.2 :=
  rfl

end incl

end ArbitraryField

section familyTwist

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type _} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) (M : Type _) [TopologicalSpace M] [ChartedSpace H M]
  [SmoothManifoldWithCorners I M] (V : Type _) [NormedAddCommGroup V] [NormedSpace ℝ V]
  (V' : Type _) [NormedAddCommGroup V'] [NormedSpace ℝ V'] {F : Type _} [NormedAddCommGroup F]
  [NormedSpace ℝ F] {G : Type _} [TopologicalSpace G] (J : ModelWithCorners ℝ F G) (N : Type _)
  [TopologicalSpace N] [ChartedSpace G N] [SmoothManifoldWithCorners J N]

local notation "σ" => RingHom.id ℝ

local notation "FJ¹MV" =>
  Bundle.ContinuousLinearMap σ (TangentSpace I : M → Type _) (Bundle.Trivial M V)

local notation "J¹MV" => TotalSpace (E →L[ℝ] V) FJ¹MV

/-- A section of a 1-jet bundle seen as a bundle over the source manifold. -/
@[ext]
structure FamilyOneJetEuclSec where
  toFun : N × M → J¹MV
  is_sec' : ∀ p, (to_fun p).1 = p.2
  smooth' : Smooth (J.prod I) (I.prod 𝓘(ℝ, E →L[ℝ] V)) to_fun

instance : CoeFun (FamilyOneJetEuclSec I M V J N) fun S => N × M → J¹MV :=
  ⟨fun S x => S.toFun x⟩

variable {I M V J N}

@[simp]
theorem FamilyOneJetEuclSec.is_sec (s : FamilyOneJetEuclSec I M V J N) (p : N × M) :
    (s p).1 = p.2 :=
  s.is_sec' p

@[simp]
theorem FamilyOneJetEuclSec.smooth (s : FamilyOneJetEuclSec I M V J N) :
    Smooth (J.prod I) (I.prod 𝓘(ℝ, E →L[ℝ] V)) s :=
  s.smooth'

variable {I M V J N V'}

def familyJoin {f : N × M → V} (hf : Smooth (J.prod I) 𝓘(ℝ, V) f)
    (s : FamilyOneJetEuclSec I M V J N) : FamilyOneJetSec I M 𝓘(ℝ, V) V J N
    where
  bs n m := (incl I M V (s (n, m), f (n, m))).1.2
  ϕ n m := (incl I M V (s (n, m), f (n, m))).2
  smooth' := by
    convert (smooth_incl I M V).comp (s.smooth.prod_mk hf)
    ext p
    · simp
    · simp
    have : (p.1, p.2) = p := Prod.ext rfl rfl
    rw [this]
    simp

def familyTwist (s : OneJetEuclSec I M V) (i : N × M → V →L[ℝ] V')
    (i_smooth : ∀ x₀ : N × M, SmoothAt (J.prod I) 𝓘(ℝ, V →L[ℝ] V') i x₀) :
    FamilyOneJetEuclSec I M V' J N
    where
  toFun p := ⟨p.2, (i p).comp (s p.2).2⟩
  is_sec' p := rfl
  smooth' := by
    intro x₀
    refine' smooth_at_snd.one_jet_eucl_bundle_mk' _
    simp_rw [ContinuousLinearMap.comp_assoc]
    have : SmoothAt (J.prod I) _ (fun x : N × M => _) x₀ := s.smooth.comp smooth_snd x₀
    simp_rw [smoothAt_one_jet_eucl_bundle', s.is_sec] at this
    refine' (i_smooth x₀).clm_comp _
    convert this.2
    ext z
    rw [s.is_sec]

end familyTwist

