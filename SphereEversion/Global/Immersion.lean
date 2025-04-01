import Mathlib.Analysis.Convex.AmpleSet
import Mathlib.Geometry.Manifold.Instances.Sphere
import SphereEversion.ToMathlib.LinearAlgebra.FiniteDimensional
import SphereEversion.ToMathlib.Geometry.Manifold.Immersion
import SphereEversion.ToMathlib.Analysis.InnerProductSpace.Rotation
import SphereEversion.Global.Gromov
import SphereEversion.Global.TwistOneJetSec

-- set_option trace.filter_inst_type true
noncomputable section

open Metric Module Set Function LinearMap Filter ContinuousLinearMap

open scoped Manifold Topology

-- Can't open ContDiff because `ω` conflicts with the notation for orientation below
local notation "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] (I' : ModelWithCorners ℝ E' H')
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {G : Type*} [TopologicalSpace G]
  (J : ModelWithCorners ℝ F G)
  (N : Type*) [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]

@[inherit_doc] local notation "TM" => TangentSpace I
@[inherit_doc] local notation "TM'" => TangentSpace I'
@[inherit_doc] local notation "HJ" => ModelProd (ModelProd H H') (E →L[ℝ] E')
@[inherit_doc] local notation "ψJ" => chartAt HJ

variable (M M') in
/-- The relation of immersions for maps between two manifolds. -/
def immersionRel : RelMfld I M I' M' :=
  {σ | Injective σ.2}

omit [IsManifold I ∞ M] [IsManifold I' ∞ M'] in
@[simp]
theorem mem_immersionRel_iff {σ : OneJetBundle I M I' M'} :
    σ ∈ immersionRel I M I' M' ↔ Injective (σ.2 : TangentSpace I _ →L[ℝ] TangentSpace I' _) :=
  Iff.rfl

/-- A characterisation of the immersion relation in terms of a local chart. -/
theorem mem_immersionRel_iff' {σ σ' : OneJetBundle I M I' M'} (hσ' : σ' ∈ (ψJ σ).source) :
    σ' ∈ immersionRel I M I' M' ↔ Injective (ψJ σ σ').2 := by
  simp_rw [mem_immersionRel_iff]
  rw [oneJetBundle_chartAt_apply, inCoordinates_eq]
  · simp_rw [ContinuousLinearMap.coe_comp', ContinuousLinearEquiv.coe_coe, EquivLike.comp_injective,
    EquivLike.injective_comp]
  exacts [hσ'.1.1, hσ'.1.2]

theorem chartAt_image_immersionRel_eq {σ : OneJetBundle I M I' M'} :
    ψJ σ '' ((ψJ σ).source ∩ immersionRel I M I' M') = (ψJ σ).target ∩ {q : HJ | Injective q.2} :=
  PartialEquiv.IsImage.image_eq fun _σ' hσ' ↦ (mem_immersionRel_iff' I I' hσ').symm

theorem immersionRel_open [FiniteDimensional ℝ E] : IsOpen (immersionRel I M I' M') := by
  simp_rw [ChartedSpace.isOpen_iff HJ (immersionRel I M I' M'), chartAt_image_immersionRel_eq]
  refine fun σ ↦ (ψJ σ).open_target.inter ?_
  convert isOpen_univ.prod ContinuousLinearMap.isOpen_injective
  · ext x
    -- Porting note: `mem_prod` is a simp lemma, but the next line is still needed.
    rw [mem_prod]
    simp
  · infer_instance
  · infer_instance

omit [IsManifold I ∞ M] [IsManifold I' ∞ M'] in
@[simp]
theorem immersionRel_slice_eq {m : M} {m' : M'} {p : DualPair <| TangentSpace I m}
    {φ : TangentSpace I m →L[ℝ] TangentSpace I' m'} (hφ : Injective φ) :
    (immersionRel I M I' M').slice ⟨(m, m'), φ⟩ p = ((ker p.π).map φ : Set <| TM' m')ᶜ :=
  Set.ext_iff.mpr fun _ ↦ p.injective_update_iff hφ

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']

omit [IsManifold I ∞ M] [IsManifold I' ∞ M'] in
theorem immersionRel_ample (h : finrank ℝ E < finrank ℝ E') : (immersionRel I M I' M').Ample := by
  rw [RelMfld.ample_iff]
  rintro ⟨⟨m, m'⟩, φ : TangentSpace I m →L[ℝ] TangentSpace I' m'⟩ (p : DualPair (TangentSpace I m))
    (hφ : Injective φ)
  haveI : FiniteDimensional ℝ (TangentSpace I m) := (by infer_instance : FiniteDimensional ℝ E)
  have hcodim := one_lt_rank_of_rank_lt_rank p.ker_pi_ne_top h φ.toLinearMap
  rw [immersionRel_slice_eq I I' hφ]
  exact AmpleSet.of_one_lt_codim hcodim

/-- This is lemma `lem:open_ample_immersion` from the blueprint. -/
theorem immersionRel_open_ample (h : finrank ℝ E < finrank ℝ E') :
    IsOpen (immersionRel I M I' M') ∧ (immersionRel I M I' M').Ample :=
  ⟨immersionRel_open I I', immersionRel_ample I I' h⟩

end General

section Generalbis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] (I' : ModelWithCorners ℝ E' H') [I'.Boundaryless]
  {M' : Type*} [MetricSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
  {EP : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP] [FiniteDimensional ℝ EP]
  {HP : Type*} [TopologicalSpace HP] {IP : ModelWithCorners ℝ EP HP} [IP.Boundaryless]
  {P : Type*} [TopologicalSpace P] [ChartedSpace HP P] [IsManifold IP ∞ P]
  {C : Set (P × M)} {ε : M → ℝ}

variable (M M' IP P)

/-- parametric h-principle for immersions. -/
theorem immersionRel_satisfiesHPrincipleWith
    [T2Space P] [SigmaCompactSpace P] [T2Space M] [SigmaCompactSpace M] [SigmaCompactSpace M']
    (h : finrank ℝ E < finrank ℝ E') (hC : IsClosed C) (hε_pos : ∀ x, 0 < ε x)
    (hε_cont : Continuous ε) : (immersionRel I M I' M').SatisfiesHPrincipleWith IP C ε :=
  (immersionRel_ample I I' h).satisfiesHPrincipleWith (immersionRel_open I I') hC hε_pos hε_cont

end Generalbis

/-! The inclusion and antipodal map on a sphere are immersions:
these results are not used directly, but are good sanity checks. -/
section sanitycheck

variable {n : ℕ} (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fact (finrank ℝ E = n + 1)]

/-- The inclusion of `𝕊^n` into `ℝ^{n+1}` is an immersion. -/
theorem immersion_inclusion_sphere : Immersion (𝓡 n) 𝓘(ℝ, E)
    (fun x : sphere (0 : E) 1 ↦ (x : E)) ∞ where
  contMDiff := contMDiff_coe_sphere.of_le le_top
  diff_injective := mfderiv_coe_sphere_injective

/-- The antipodal map on `𝕊^n ⊆ ℝ^{n+1}` is an immersion. -/
theorem immersion_antipodal_sphere : Immersion (𝓡 n) 𝓘(ℝ, E)
    (fun x : sphere (0 : E) 1 ↦ -(x : E)) ∞ where
  contMDiff :=
    -- Write this as the composition of `coe_sphere` and the antipodal map on `E`.
    -- The other direction elaborates much worse.
    (contDiff_neg.contMDiff).comp (contMDiff_coe_sphere.of_le le_top)
  diff_injective x := by
    change Injective (mfderiv (𝓡 n) 𝓘(ℝ, E) (-fun x : sphere (0 : E) 1 ↦ (x : E)) x)
    rw [mfderiv_neg]
    exact neg_injective.comp (mfderiv_coe_sphere_injective x)

end sanitycheck

section sphere_eversion

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fact (finrank ℝ E = 3)]

set_option synthInstance.checkSynthOrder false
attribute [local instance] FiniteDimensional.of_fact_finrank_eq_succ
set_option synthInstance.checkSynthOrder true

@[inherit_doc] local notation "𝕊²" => sphere (0 : E) 1

-- TODO: generalise these statements to `n` dimensions
-- the only obstacle is the construction of rotations requires working on ℝ³.

-- The relation of immersion of a two-sphere into its ambient Euclidean space.
@[inherit_doc] local notation "𝓡_imm" => immersionRel (𝓡 2) 𝕊² 𝓘(ℝ, E) E

variable (ω : Orientation ℝ E (Fin 3))

-- this result holds mutatis mutandis in `ℝ^n`
theorem smooth_bs :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E) ∞
      fun p : ℝ × (sphere (0 : E) 1) ↦ (1 - p.1) • (p.2 : E) + p.1 • -(p.2: E) := by
  refine (ContMDiff.smul ?_ ?_).add (contMDiff_fst.smul ?_)
  · exact (contDiff_const.sub contDiff_id).contMDiff.comp contMDiff_fst
  · exact (contMDiff_coe_sphere.of_le le_top).comp contMDiff_snd
  · exact (contDiff_neg.contMDiff.comp (contMDiff_coe_sphere.of_le le_top)).comp contMDiff_snd

def formalEversionAux : FamilyOneJetSec (𝓡 2) 𝕊² 𝓘(ℝ, E) E 𝓘(ℝ, ℝ) ℝ :=
  familyJoin (smooth_bs E) <|
    familyTwist (drop (oneJetExtSec ⟨((↑) : 𝕊² → E), contMDiff_coe_sphere.of_le le_top⟩))
      (fun p : ℝ × 𝕊² ↦ ω.rot (p.1, p.2))
      (by
        intro p
        have : ContMDiffAt 𝓘(ℝ, ℝ × E) 𝓘(ℝ, E →L[ℝ] E) ∞ ω.rot (p.1, p.2) := by
          refine ((ω.contDiff_rot ?_).of_le le_top).contMDiffAt
          exact ne_zero_of_mem_unit_sphere p.2
        apply this.comp p (f := fun (p : ℝ × sphere 0 1) ↦ (p.1, (p.2 : E)))
        apply contMDiff_fst.prodMk_space ((contMDiff_coe_sphere.of_le le_top).comp contMDiff_snd))

/-- A formal eversion of a two-sphere into its ambient Euclidean space. -/
def formalEversionAux2 : HtpyFormalSol 𝓡_imm :=
  { formalEversionAux E ω with
    is_sol' := fun t x ↦ (ω.isometry_rot t x).injective.comp (mfderiv_coe_sphere_injective x) }

def formalEversion : HtpyFormalSol 𝓡_imm :=
  (formalEversionAux2 E ω).reindex ⟨smoothStep, contMDiff_iff_contDiff.mpr smoothStep.smooth⟩

@[simp]
theorem formalEversion_bs (t : ℝ) :
    (formalEversion E ω t).bs = fun x : 𝕊² ↦
      (1 - smoothStep t : ℝ) • (x : E) + (smoothStep t : ℝ) • (-x : E) :=
  rfl

theorem formalEversion_zero (x : 𝕊²) : (formalEversion E ω 0).bs x = x := by simp

theorem formalEversion_one (x : 𝕊²) : (formalEversion E ω 1).bs x = -x := by simp

theorem formalEversionHolAtZero {t : ℝ} (ht : t < 1 / 4) :
    (formalEversion E ω t).toOneJetSec.IsHolonomic := by
  intro x
  change
    mfderiv (𝓡 2) 𝓘(ℝ, E) (fun y : 𝕊² ↦ ((1 : ℝ) - smoothStep t) • (y : E) +
      smoothStep t • -(y : E)) x =
      (ω.rot (smoothStep t, x)).comp (mfderiv (𝓡 2) 𝓘(ℝ, E) (fun y : 𝕊² ↦ (y : E)) x)
  simp_rw [smoothStep.of_lt ht, ω.rot_zero, ContinuousLinearMap.id_comp]
  congr with y
  simp [smoothStep.of_lt ht]

theorem formalEversionHolAtOne {t : ℝ} (ht : 3 / 4 < t) :
    (formalEversion E ω t).toOneJetSec.IsHolonomic := by
  intro x
  change
    mfderiv (𝓡 2) 𝓘(ℝ, E) (fun y : 𝕊² ↦ ((1 : ℝ) - smoothStep t) • (y : E) +
      smoothStep t • -(y : E)) x =
      (ω.rot (smoothStep t, x)).comp (mfderiv (𝓡 2) 𝓘(ℝ, E) (fun y : 𝕊² ↦ (y : E)) x)
  trans mfderiv (𝓡 2) 𝓘(ℝ, E) (-fun y : 𝕊² ↦ (y : E)) x
  · congr 2 with y
    simp [smoothStep.of_gt ht]
  ext v
  erw [mfderiv_neg, ContinuousLinearMap.coe_comp', Function.comp_apply,
       ContinuousLinearMap.neg_apply, smoothStep.of_gt ht]
  rw [ω.rot_one]; · rfl
  rw [← range_mfderiv_coe_sphere (n := 2) x]
  exact LinearMap.mem_range_self ..

theorem formalEversion_hol_near_zero_one :
    ∀ᶠ s : ℝ × 𝕊² near {0, 1} ×ˢ univ, (formalEversion E ω s.1).toOneJetSec.IsHolonomicAt s.2 := by
  have : (Iio (1 / 4 : ℝ) ∪ Ioi (3 / 4)) ×ˢ (univ : Set 𝕊²) ∈ 𝓝ˢ (({0, 1} : Set ℝ) ×ˢ univ) := by
    refine ((isOpen_Iio.union isOpen_Ioi).prod isOpen_univ).mem_nhdsSet.mpr ?_
    rintro ⟨s, x⟩ ⟨hs, hx⟩
    refine ⟨?_, mem_univ _⟩
    simp_rw [mem_insert_iff, mem_singleton_iff] at hs
    rcases hs with (rfl | rfl)
    · exact Or.inl (show (0 : ℝ) < 1 / 4 by norm_num)
    · exact Or.inr (show (3 / 4 : ℝ) < 1 by norm_num)
  filter_upwards [this]
  rintro ⟨t, x⟩ ⟨ht | ht, _hx⟩
  · exact formalEversionHolAtZero E ω ht x
  · exact formalEversionHolAtOne E ω ht x

-- general helper lemmas, useful for showing smoothness of the formal immersions below
section helper

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F G : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

-- move to Analysis.Calculus.ContDiff.Basic, or so
theorem contDiff_prod_iff (f : E → F × G) (n : ℕ∞) :
    ContDiff 𝕜 n f ↔
      ContDiff 𝕜 n (Prod.fst ∘ f) ∧ ContDiff 𝕜 n (Prod.snd ∘ f) :=
  ⟨fun h ↦ ⟨h.fst, h.snd⟩, fun h ↦ h.1.prodMk h.2⟩

-- move to Analysis.Calculus.ContDiff.Defs, or so
lemma ContDiff.inr (x : E) (n : ℕ∞) : ContDiff 𝕜 n fun p : F ↦ (⟨x, p⟩ : E × F) := by
  rw [contDiff_prod_iff]
  exact ⟨contDiff_const, contDiff_id⟩

-- is this form actually useful, compared to `uncurry_left`?
theorem ContDiff.uncurry_left' (n : ℕ∞) {f : E × F → G}
    (hf : ContDiff 𝕜 n f) (x : E) :
    ContDiff 𝕜 n (fun p : F ↦ f ⟨x, p⟩) :=
  hf.comp (ContDiff.inr x n)

theorem ContDiff.uncurry_left {f : E → F → G} (n : ℕ∞) (hf : ContDiff 𝕜 n ↿f) (x : E) :
    ContDiff 𝕜 n (f x) := by
  have : f x = (uncurry f) ∘ fun p : F ↦ (⟨x, p⟩ : E × F) := by ext; simp
  rw [this]; exact hf.comp (ContDiff.inr x n)

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] (I' : ModelWithCorners 𝕜 E' H')
  {M' : Type*} [MetricSpace M'] [ChartedSpace H' M']
  {EP : Type*} [NormedAddCommGroup EP] [NormedSpace 𝕜 EP]
  {HP : Type*} [TopologicalSpace HP] (IP : ModelWithCorners 𝕜 EP HP)
  {P : Type*} [TopologicalSpace P] [ChartedSpace HP P]

-- move to Mathlib.Geometry.Manifold.ContMDiff.Product
lemma ContMDiff.prod_left {n : ℕ∞} (x : M) :
    ContMDiff I' (I.prod I') n fun p : M' ↦ (⟨x, p⟩ : M × M') := by
  rw [contMDiff_prod_iff]
  exact ⟨contMDiff_const, contMDiff_id⟩

-- move to Mathlib.Geometry.Manifold.ContMDiff.Product
theorem ContMDiff.uncurry_left {n : ℕ∞}
    {f : M → M' → P} (hf : ContMDiff (I.prod I') IP n ↿f) (x : M) :
    ContMDiff I' IP n (f x) := by
  have : f x = (uncurry f) ∘ fun p : M' ↦ ⟨x, p⟩ := by ext; simp
  -- or just `apply hf.comp (ContMDiff.prod_left I I' x)`
  rw [this]; exact hf.comp (ContMDiff.prod_left I I' x)

end helper

theorem sphere_eversion :
    ∃ f : ℝ → 𝕊² → E,
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E) ∞ ↿f ∧
        (f 0 = fun x : 𝕊² ↦ (x : E)) ∧ (f 1 = fun x : 𝕊² ↦ -(x : E)) ∧
        ∀ t, Immersion (𝓡 2) 𝓘(ℝ, E) (f t) ∞ := by
  classical
  let ω : Orientation ℝ E (Fin 3) :=
    ((stdOrthonormalBasis _ _).reindex <|
          finCongr (Fact.out : finrank ℝ E = 3)).toBasis.orientation
  have rankE : finrank ℝ E = 3 := Fact.out
  haveI : FiniteDimensional ℝ E := FiniteDimensional.of_finrank_eq_succ rankE
  have ineq_rank : finrank ℝ (EuclideanSpace ℝ (Fin 2)) < finrank ℝ E := by simp [rankE]
  let ε : 𝕊² → ℝ := fun _ ↦ 1
  have hε_pos : ∀ x, 0 < ε x := fun _ ↦ zero_lt_one
  have hε_cont : Continuous ε := continuous_const
  haveI : Nontrivial E := nontrivial_of_finrank_eq_succ (Fact.out : finrank ℝ E = 3)
  haveI : Nonempty (sphere 0 1 : Set E) :=
    (NormedSpace.sphere_nonempty.mpr zero_le_one).to_subtype
  rcases(immersionRel_satisfiesHPrincipleWith (𝓡 2) 𝕊² 𝓘(ℝ, E) E 𝓘(ℝ, ℝ) ℝ ineq_rank
          ((Finite.isClosed (by simp : ({0, 1} : Set ℝ).Finite)).prod isClosed_univ) hε_pos
          hε_cont).bs
      (formalEversion E ω) (formalEversion_hol_near_zero_one E ω) with
    ⟨f, h₁, h₂, -, h₅⟩
  have := h₂.forall_mem principal_le_nhdsSet
  refine ⟨f, h₁, ?_, ?_, ?_/-h₅-/⟩
  · ext x
    rw [this (0, x) (by simp)]
    convert formalEversion_zero E ω x
  · ext x
    rw [this (1, x) (by simp)]
    convert formalEversion_one E ω x
  · exact fun t ↦ {
      contMDiff := ContMDiff.uncurry_left 𝓘(ℝ, ℝ) (𝓡 2) 𝓘(ℝ, E) h₁ t
      diff_injective := h₅ t
    }

-- The next instance will be used in the main file.
instance (n : ℕ) : Fact (finrank ℝ (EuclideanSpace ℝ <| Fin n) = n) :=
  ⟨finrank_euclideanSpace_fin⟩

-- The next notation will be used in the main file.
notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

end sphere_eversion
