import SphereEversion.Global.Relation
import Mathlib.Analysis.Convex.AmpleSet

noncomputable section

open Set Function

open Filter hiding map_smul

open ChartedSpace SmoothManifoldWithCorners

open LinearMap (ker)

open scoped Topology Manifold Pointwise

section ParameterSpace

/-! ## Fundamental definitions -/


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [SmoothManifoldWithCorners I M] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} {M' : Type*}
  [TopologicalSpace M'] [ChartedSpace H' M'] [SmoothManifoldWithCorners I' M'] {EP : Type*}
  [NormedAddCommGroup EP] [NormedSpace ℝ EP] {HP : Type*} [TopologicalSpace HP]
  {IP : ModelWithCorners ℝ EP HP} {P : Type*} [TopologicalSpace P] [ChartedSpace HP P]
  [SmoothManifoldWithCorners IP P] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G} {N : Type*} [TopologicalSpace N]
  [ChartedSpace G N] [SmoothManifoldWithCorners J N] {EX : Type*} [NormedAddCommGroup EX]
  [NormedSpace ℝ EX] {HX : Type*} [TopologicalSpace HX] {IX : ModelWithCorners ℝ EX HX}
  -- note: X is a metric space
  {X : Type*}
  [MetricSpace X] [ChartedSpace HX X] [SmoothManifoldWithCorners IX X]

variable {R : RelMfld I M I' M'}

variable (IP P)

/-- The relation `𝓡 ^ P` -/
def RelMfld.relativize (R : RelMfld I M I' M') : RelMfld (IP.prod I) (P × M) I' M' :=
  bundleSnd ⁻¹' R

variable {IP P}

theorem RelMfld.mem_relativize (R : RelMfld I M I' M')
    (w : OneJetBundle (IP.prod I) (P × M) I' M') :
    w ∈ R.relativize IP P ↔
      (OneJetBundle.mk w.1.1.2 w.1.2 (w.2.comp (ContinuousLinearMap.inr ℝ EP E)) :
          OneJetBundle I M I' M') ∈ R := by
  simp_rw [RelMfld.relativize, mem_preimage, bundleSnd_eq]; rfl

theorem RelMfld.isOpen_relativize (R : RelMfld I M I' M') (h2 : IsOpen R) :
    IsOpen (R.relativize IP P) :=
  h2.preimage smooth_bundleSnd.continuous

/-
Porting note: the next statement has huge elaboration issue because of defEq abuse.
We force our way using hard type ascription, ie. using `id`.
The following commented out variables and check show the issue.
variable {σ : OneJetBundle (IP.prod I) (P × M) I' M'}
    {p : DualPair <| TangentSpace (IP.prod I) σ.1.1}(q : DualPair <| TangentSpace I σ.1.1.2)

#check  p.v
#check (p.v - (id ((0 : EP), (q.v : E)) : TangentSpace (IP.prod I) σ.proj.1))
#check (R.relativize IP P).slice σ p
#check (R.slice (bundleSnd σ) q : Set <| TangentSpace I' σ.proj.2) -/

theorem relativize_slice {σ : OneJetBundle (IP.prod I) (P × M) I' M'}
    {p : DualPair <| TangentSpace (IP.prod I) σ.1.1} (q : DualPair <| TangentSpace I σ.1.1.2)
    (hpq : p.π.comp (ContinuousLinearMap.inr ℝ EP E) = q.π) :
    (R.relativize IP P).slice σ p =
      σ.2 (p.v - (id (0, (q.v : E)) : TangentSpace (IP.prod I) σ.proj.1)) +ᵥ
      (id (R.slice (bundleSnd σ) q) : Set <| TangentSpace I' σ.proj.2) := by
  set z := (p.v - (id (0, (q.v : E)) : TangentSpace (IP.prod I) σ.proj.1))
  have h2pq : ∀ x : E, p.π ((0 : EP), x) = q.π x := fun x ↦
    congr_arg (fun f : E →L[ℝ] ℝ ↦ f x) hpq
  ext1 w
  have h1 :
    (p.update σ.2 w).comp (ContinuousLinearMap.inr ℝ EP E) =
      q.update (bundleSnd σ).2 (-σ.2 z + w) := by
    ext1 x
    erw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
         ← ContinuousLinearMap.map_neg, neg_sub]
    obtain ⟨u, hu, t, rfl⟩ := q.decomp x
    have hv : (id (0, (q.v : E)) : TangentSpace (IP.prod I) σ.proj.1) - p.v ∈ ker p.π := by
      simp [LinearMap.mem_ker, map_sub, p.pairing, h2pq, q.pairing, sub_self]
    have hup : ((0 : EP), u) ∈ ker p.π := (h2pq u).trans hu
    erw [q.update_apply _ hu, ← Prod.zero_mk_add_zero_mk, map_add, p.update_ker_pi _ _ hup, ←
      Prod.smul_zero_mk, map_smul]
    conv_lhs => rw [← sub_add_cancel (0, q.v) p.v]
    erw [map_add, p.update_ker_pi _ _ hv, p.update_v, bundleSnd_eq]
    rfl
  erw [← preimage_vadd_neg, mem_preimage, mem_slice, R.mem_relativize]
  congr!


theorem relativize_slice_eq_univ {σ : OneJetBundle (IP.prod I) (P × M) I' M'}
    {p : DualPair <| TangentSpace (IP.prod I) σ.1.1}
    (hp : p.π.comp (ContinuousLinearMap.inr ℝ EP E) = 0) :
    ((R.relativize IP P).slice σ p).Nonempty ↔ (R.relativize IP P).slice σ p = univ := by
  rcases σ with ⟨⟨⟨q, m⟩,m'⟩, φ⟩
  have h2p : ∀ x : E, p.π ((0 : EP), x) = 0 := fun x ↦ congr_arg (fun f : E →L[ℝ] ℝ ↦ f x) hp
  have :
    ∀ y : E', (p.update φ y).comp (ContinuousLinearMap.inr ℝ EP E) = φ.comp (ContinuousLinearMap.inr ℝ EP E) := by
    intro y
    ext1 x
    erw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
      p.update_ker_pi _ _ (h2p x)]
    rfl
  simp_rw [Set.Nonempty, eq_univ_iff_forall]
  -- Porting note: those conv were not needed in Lean 3.
  conv_lhs =>
    congr
    ext x
    erw [mem_slice, R.mem_relativize, this]
  conv_rhs =>
    ext
    erw [mem_slice, R.mem_relativize, this]
  dsimp only [oneJetBundle_mk_fst, oneJetBundle_mk_snd]
  simp [this, exists_const, forall_const]

variable (IP P)

theorem RelMfld.Ample.relativize (hR : R.Ample) : (R.relativize IP P).Ample := by
  intro σ p
  let p2 := p.π.comp (ContinuousLinearMap.inr ℝ EP E)
  rcases eq_or_ne p2 0 with (h | h)
  · intro w hw
    rw [(relativize_slice_eq_univ h).mp ⟨w, hw⟩, connectedComponentIn_univ,
      PreconnectedSpace.connectedComponent_eq_univ, convexHull_univ]
  obtain ⟨u', hu'⟩ := ContinuousLinearMap.exists_ne_zero h
  let u := (p2 u')⁻¹ • u'
  let q : DualPair (TangentSpace I σ.1.1.2) :=
    ⟨p2, u, by erw [p2.map_smul, smul_eq_mul, inv_mul_cancel hu']⟩
  rw [relativize_slice q rfl]
  exact (hR q).vadd

variable {IP P}

theorem FamilyOneJetSec.uncurry_mem_relativize (S : FamilyOneJetSec I M I' M' IP P) {s : P}
    {x : M} : S.uncurry (s, x) ∈ R.relativize IP P ↔ S s x ∈ R := by
  simp_rw [RelMfld.relativize, mem_preimage, bundleSnd_eq, OneJetSec.coe_apply, mapLeft]
  dsimp
  congr!
  -- Porting note: the next two let shouldn't be needed.
  let _this₁ :
    Module ℝ (((Prod.fst : M × M' → M) *ᵖ (TangentSpace I)) (x, (S s).bs x)) := by infer_instance
  let _this₂ :
    Module ℝ (((Prod.snd : M × M' → M') *ᵖ (TangentSpace I')) (x, (S s).bs x)) := by infer_instance
  -- Porting note: we are missing an ext lemma here.
  apply ContinuousLinearMap.ext_iff.2 (fun v ↦ ?_)
  change ((S.uncurry.ϕ (s, x)).comp (ContinuousLinearMap.inr ℝ EP E)) v = _
  erw [S.uncurry_ϕ', ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.comp_apply]
  simp [S.coe_ϕ]

def FamilyFormalSol.uncurry (S : FamilyFormalSol IP P R) : FormalSol (R.relativize IP P) := by
  refine ⟨S.toFamilyOneJetSec.uncurry, ?_⟩
  rintro ⟨s, x⟩
  exact S.toFamilyOneJetSec.uncurry_mem_relativize.mpr (S.is_sol' s x)

theorem FamilyFormalSol.uncurry_ϕ' (S : FamilyFormalSol IP P R) (p : P × M) :
    S.uncurry.ϕ p =
      mfderiv IP I' (fun z ↦ S.bs z p.2) p.1 ∘L ContinuousLinearMap.fst ℝ EP E +
        S.ϕ p.1 p.2 ∘L ContinuousLinearMap.snd ℝ EP E :=
  S.toFamilyOneJetSec.uncurry_ϕ' p

def FamilyOneJetSec.curry (S : FamilyOneJetSec (IP.prod I) (P × M) I' M' J N) :
    FamilyOneJetSec I M I' M' (J.prod IP) (N × P)
    where
  bs p x := (S p.1).bs (p.2, x)
  ϕ p x := (S p.1).ϕ (p.2, x) ∘L mfderiv I (IP.prod I) (fun x ↦ (p.2, x)) x
  smooth' := by
    rintro ⟨⟨t, s⟩, x⟩
    refine smoothAt_snd.oneJetBundle_mk (S.smooth_bs.comp smooth_prod_assoc _) ?_
    have h1 :
      SmoothAt ((J.prod IP).prod I) 𝓘(ℝ, EP × E →L[ℝ] E')
        (inTangentCoordinates (IP.prod I) I' (fun p : (N × P) × M ↦ (p.1.2, p.2))
          (fun p : (N × P) × M ↦ (S p.1.1).bs (p.1.2, p.2))
          (fun p : (N × P) × M ↦ (S p.1.1).ϕ (p.1.2, p.2)) ((t, s), x))
        ((t, s), x) := by
      apply
        (smoothAt_oneJetBundle.mp <|
              SmoothAt.comp ((t, s), x) (S.smooth (t, (s, x))) (smooth_prod_assoc ((t, s), x))).2.2
    have h2 :
      SmoothAt ((J.prod IP).prod I) 𝓘(ℝ, E →L[ℝ] EP × E)
        (inTangentCoordinates I (IP.prod I) Prod.snd (fun p : (N × P) × M ↦ (p.1.2, p.2))
          (fun p : (N × P) × M ↦ mfderiv I (IP.prod I) (fun x : M ↦ (p.1.2, x)) p.2) ((t, s), x))
        ((t, s), x) := by
      apply
        ContMDiffAt.mfderiv (fun (p : (N × P) × M) (x : M) ↦ (p.1.2, x)) Prod.snd
          (smoothAt_fst.fst.snd.prod_mk smoothAt_snd :
            SmoothAt (((J.prod IP).prod I).prod I) (IP.prod I) _ (((t, s), x), x))
          (smoothAt_snd : SmoothAt ((J.prod IP).prod I) _ _ _) le_top
    exact h1.clm_comp_inTangentCoordinates (continuousAt_fst.snd.prod continuousAt_snd) h2

theorem FamilyOneJetSec.curry_bs (S : FamilyOneJetSec (IP.prod I) (P × M) I' M' J N) (p : N × P)
    (x : M) : (S.curry p).bs x = (S p.1).bs (p.2, x) :=
  rfl

theorem FamilyOneJetSec.curry_ϕ (S : FamilyOneJetSec (IP.prod I) (P × M) I' M' J N) (p : N × P)
    (x : M) : (S.curry p).ϕ x = (S p.1).ϕ (p.2, x) ∘L mfderiv I (IP.prod I) (fun x ↦ (p.2, x)) x :=
  rfl

theorem FamilyOneJetSec.curry_ϕ' (S : FamilyOneJetSec (IP.prod I) (P × M) I' M' J N) (p : N × P)
    (x : M) : (S.curry p).ϕ x = (S p.1).ϕ (p.2, x) ∘L ContinuousLinearMap.inr ℝ EP E := by
  rw [S.curry_ϕ]
  congr 1
  refine ((mdifferentiableAt_const I IP).mfderiv_prod smooth_id.mdifferentiableAt).trans ?_
  rw [mfderiv_id, mfderiv_const]
  rfl

theorem FormalSol.eq_iff {F₁ F₂ : FormalSol R} {x : M} :
    F₁ x = F₂ x ↔ F₁.bs x = F₂.bs x ∧ F₁.ϕ x = by apply F₂.ϕ x := by
  simp [Bundle.TotalSpace.ext_iff, FormalSol.fst_eq, FormalSol.snd_eq]

theorem FamilyOneJetSec.isHolonomicAt_curry (S : FamilyOneJetSec (IP.prod I) (P × M) I' M' J N)
    {t : N} {s : P} {x : M} (hS : (S t).IsHolonomicAt (s, x)) : (S.curry (t, s)).IsHolonomicAt x := by
  simp_rw [OneJetSec.IsHolonomicAt, (S.curry _).snd_eq, S.curry_ϕ] at hS ⊢
  dsimp only
  rw [show (S.curry (t, s)).bs = fun x ↦ (S.curry (t, s)).bs x from rfl, funext (S.curry_bs _)]
  dsimp only
  refine (mfderiv_comp x (S t).smooth_bs.mdifferentiableAt
    ((mdifferentiableAt_const I IP).prod_mk smooth_id.mdifferentiableAt)).trans
    ?_
  rw [id, hS]
  rfl

theorem FamilyOneJetSec.curry_mem (S : FamilyOneJetSec (IP.prod I) (P × M) I' M' J N) {p : N × P}
    {x : M} (hR : S p.1 (p.2, x) ∈ R.relativize IP P) : S.curry p x ∈ R := by
  simp_rw [RelMfld.relativize, mem_preimage, bundleSnd_eq, OneJetSec.coe_apply, mapLeft] at hR ⊢
  convert hR
  -- Porting note: we are missing an ext lemma here.
  apply ContinuousLinearMap.ext_iff.2 (fun v ↦ ?_)
  simp_rw [S.curry_ϕ']

def FamilyFormalSol.curry (S : FamilyFormalSol J N (R.relativize IP P)) :
    FamilyFormalSol (J.prod IP) (N × P) R :=
  ⟨S.toFamilyOneJetSec.curry, fun _p _x ↦ S.toFamilyOneJetSec.curry_mem S.is_sol⟩

theorem FamilyFormalSol.curry_ϕ' (S : FamilyFormalSol J N (R.relativize IP P)) (p : N × P) (x : M) :
    (S.curry p).ϕ x = (S p.1).ϕ (p.2, x) ∘L ContinuousLinearMap.inr ℝ EP E :=
  S.toFamilyOneJetSec.curry_ϕ' p x

theorem curry_eq_iff_eq_uncurry {𝓕 : FamilyFormalSol J N (R.relativize IP P)}
    {𝓕₀ : FamilyFormalSol IP P R} {t : N} {x : M} {s : P} (h : 𝓕 t (s, x) = 𝓕₀.uncurry (s, x)) :
    (𝓕.curry (t, s)) x = 𝓕₀ s x := by
  simp_rw [FormalSol.eq_iff] at h ⊢
  refine ⟨h.1, ?_⟩
  simp_rw [𝓕.curry_ϕ', h.2, 𝓕₀.uncurry_ϕ']
  ext v
  erw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd', ContinuousLinearMap.map_zero,
    zero_add]

theorem RelMfld.SatisfiesHPrinciple.satisfiesHPrincipleWith (R : RelMfld I M IX X) {C : Set (P × M)}
    (ε : M → ℝ) (h : (R.relativize IP P).SatisfiesHPrinciple C fun x ↦ ε x.2) :
    R.SatisfiesHPrincipleWith IP C ε := by
  intro 𝓕₀ h𝓕₀
  obtain ⟨𝓕, h1𝓕, h2𝓕, h3𝓕, h4𝓕⟩ :=
    h 𝓕₀.uncurry (h𝓕₀.mono fun p hp ↦ 𝓕₀.toFamilyOneJetSec.isHolonomicAt_uncurry.mpr hp)
  refine ⟨𝓕.curry, ?_, ?_, ?_, ?_⟩
  · intro s x; exact curry_eq_iff_eq_uncurry (h1𝓕 (s, x))
  · intro s x; exact 𝓕.toFamilyOneJetSec.isHolonomicAt_curry (h2𝓕 (s, x))
  · refine h3𝓕.mono ?_; rintro ⟨s, x⟩ hp t; exact curry_eq_iff_eq_uncurry (hp t)
  · intro t s x; exact h4𝓕 t (s, x)

end ParameterSpace
