import SphereEversion.Global.Relation

noncomputable section

open Set Function

open Filter hiding map_smul

open ChartedSpace SmoothManifoldWithCorners

open LinearMap (ker)

open scoped Topology Manifold Pointwise

section ParameterSpace

/-! ## Fundamental definitions -/


variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type _} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type _} [TopologicalSpace M] [ChartedSpace H M]
  [SmoothManifoldWithCorners I M] {E' : Type _} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type _} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} {M' : Type _}
  [TopologicalSpace M'] [ChartedSpace H' M'] [SmoothManifoldWithCorners I' M'] {EP : Type _}
  [NormedAddCommGroup EP] [NormedSpace ℝ EP] {HP : Type _} [TopologicalSpace HP]
  {IP : ModelWithCorners ℝ EP HP} {P : Type _} [TopologicalSpace P] [ChartedSpace HP P]
  [SmoothManifoldWithCorners IP P] {F : Type _} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type _} [TopologicalSpace G] {J : ModelWithCorners ℝ F G} {N : Type _} [TopologicalSpace N]
  [ChartedSpace G N] [SmoothManifoldWithCorners J N] {EX : Type _} [NormedAddCommGroup EX]
  [NormedSpace ℝ EX] {HX : Type _} [TopologicalSpace HX] {IX : ModelWithCorners ℝ EX HX}
  -- note: X is a metric space
  {X : Type _}
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
          OneJetBundle I M I' M') ∈
        R :=
  by simp_rw [RelMfld.relativize, mem_preimage, bundleSnd_eq]; rfl

theorem RelMfld.isOpen_relativize (R : RelMfld I M I' M') (h2 : IsOpen R) :
    IsOpen (R.relativize IP P) :=
  h2.preimage smooth_bundleSnd.continuous

theorem relativize_slice {σ : OneJetBundle (IP.prod I) (P × M) I' M'}
    {p : DualPair <| TangentSpace (IP.prod I) σ.1.1} (q : DualPair <| TangentSpace I σ.1.1.2)
    (hpq : p.π.comp (ContinuousLinearMap.inr ℝ EP E) = q.π) :
    (R.relativize IP P).slice σ p = σ.2 (p.V - (0, q.V)) +ᵥ R.slice (bundleSnd σ) q :=
  by
  -- for some reason this is needed
  let this.1 :
    Module ℝ
      (((ContMDiffMap.snd : C^∞⟮(IP.prod I).prod I', (P × M) × M'; I', M'⟯) *ᵖ (TangentSpace I'))
        σ.1) :=
    by infer_instance
  have h2pq : ∀ x : E, p.π ((0 : EP), x) = q.π x := fun x =>
    congr_arg (fun f : E →L[ℝ] ℝ => f x) hpq
  ext1 w
  have h1 :
    (p.update σ.2 w).comp (ContinuousLinearMap.inr ℝ EP E) =
      q.update (bundleSnd σ).2 (-σ.2 (p.v - (0, q.v)) + w) :=
    by
    ext1 x
    simp_rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply, ←
      ContinuousLinearMap.map_neg, neg_sub]
    obtain ⟨u, hu, t, rfl⟩ := q.decomp x
    have hv : (0, q.v) - p.v ∈ ker p.π := by
      rw [LinearMap.mem_ker, map_sub, p.pairing, h2pq, q.pairing, sub_self]
    have hup : ((0 : EP), u) ∈ ker p.π := (h2pq u).trans hu
    rw [q.update_apply _ hu, ← Prod.zero_mk_add_zero_mk, map_add, p.update_ker_pi _ _ hup, ←
      Prod.smul_zero_mk, map_smul]
    nth_rw 1 [← sub_add_cancel (0, q.v) p.v]
    rw [map_add, p.update_ker_pi _ _ hv, p.update_v, bundleSnd_eq]
    rfl
  have :=
    preimage_vadd_neg (show E' from σ.2 (p.v - (0, q.v))) (show Set E' from R.slice (bundleSnd σ) q)
  dsimp only at this
  simp_rw [← this, mem_preimage, mem_slice, R.mem_relativize]
  dsimp only [one_jet_bundle_mk_fst, one_jet_bundle_mk_snd]
  congr

theorem relativize_slice_eq_univ {σ : OneJetBundle (IP.prod I) (P × M) I' M'}
    {p : DualPair <| TangentSpace (IP.prod I) σ.1.1}
    (hp : p.π.comp (ContinuousLinearMap.inr ℝ EP E) = 0) :
    ((R.relativize IP P).slice σ p).Nonempty ↔ (R.relativize IP P).slice σ p = univ :=
  by
  -- for some reason this is needed
  let this.1 :
    Module ℝ
      (((ContMDiffMap.snd : C^∞⟮(IP.prod I).prod I', (P × M) × M'; I', M'⟯) *ᵖ (TangentSpace I'))
        σ.1) :=
    by infer_instance
  have h2p : ∀ x : E, p.π ((0 : EP), x) = 0 := fun x => congr_arg (fun f : E →L[ℝ] ℝ => f x) hp
  have :
    ∀ y : E',
      (p.update σ.snd y).comp (ContinuousLinearMap.inr ℝ EP E) =
        σ.snd.comp (ContinuousLinearMap.inr ℝ EP E) :=
    by
    intro y
    ext1 x
    simp_rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
      p.update_ker_pi _ _ (h2p x)]
  simp_rw [Set.Nonempty, eq_univ_iff_forall, mem_slice, R.mem_relativize]
  dsimp only [one_jet_bundle_mk_fst, one_jet_bundle_mk_snd]
  simp_rw [this, exists_const, forall_const]

variable (IP P)

theorem RelMfld.Ample.relativize (hR : R.Ample) : (R.relativize IP P).Ample :=
  by
  intro σ p
  let p2 := p.π.comp (ContinuousLinearMap.inr ℝ EP E)
  rcases eq_or_ne p2 0 with (h | h)
  · intro w hw
    rw [(relativize_slice_eq_univ h).mp ⟨w, hw⟩, connectedComponentIn_univ,
      PreconnectedSpace.connectedComponent_eq_univ, convexHull_univ]
  obtain ⟨u', hu'⟩ := ContinuousLinearMap.exists_ne_zero h
  let u := (p2 u')⁻¹ • u'
  let q : DualPair (TangentSpace I σ.1.1.2) :=
    ⟨p2, u, by rw [p2.map_smul, smul_eq_mul, inv_mul_cancel hu']⟩
  rw [relativize_slice q rfl]
  refine' (hR q).vadd

variable {IP P}

theorem FamilyOneJetSec.uncurry_mem_relativize (S : FamilyOneJetSec I M I' M' IP P) {s : P}
    {x : M} : S.uncurry (s, x) ∈ R.relativize IP P ↔ S s x ∈ R :=
  by
  simp_rw [RelMfld.relativize, mem_preimage, bundleSnd_eq, OneJetSec.coe_apply, mapLeft]
  congr
  ext v
  simp_rw [S.uncurry_ϕ', ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', ContinuousLinearMap.map_zero, zero_add, S.coe_ϕ]

def FamilyFormalSol.uncurry (S : FamilyFormalSol IP P R) : FormalSol (R.relativize IP P) :=
  by
  refine' ⟨S.to_family_one_jet_sec.uncurry, _⟩
  rintro ⟨s, x⟩
  exact S.to_family_one_jet_sec.uncurry_mem_relativize.mpr (S.is_sol' s x)

theorem FamilyFormalSol.uncurry_ϕ' (S : FamilyFormalSol IP P R) (p : P × M) :
    S.uncurry.ϕ p =
      mfderiv IP I' (fun z => S.bs z p.2) p.1 ∘L ContinuousLinearMap.fst ℝ EP E +
        S.ϕ p.1 p.2 ∘L ContinuousLinearMap.snd ℝ EP E :=
  S.toFamilyOneJetSec.uncurry_ϕ' p

def FamilyOneJetSec.curry (S : FamilyOneJetSec (IP.prod I) (P × M) I' M' J N) :
    FamilyOneJetSec I M I' M' (J.prod IP) (N × P)
    where
  bs p x := (S p.1).bs (p.2, x)
  ϕ p x := (S p.1).ϕ (p.2, x) ∘L mfderiv I (IP.prod I) (fun x => (p.2, x)) x
  smooth' := by
    rintro ⟨⟨t, s⟩, x⟩
    refine' smooth_at_snd.one_jet_bundle_mk (S.smooth_bs.comp smooth_prod_assoc _) _
    have h1 :
      SmoothAt ((J.prod IP).prod I) 𝓘(ℝ, EP × E →L[ℝ] E')
        (inTangentCoordinates (IP.prod I) I' (fun p : (N × P) × M => (p.1.2, p.2))
          (fun p : (N × P) × M => (S p.1.1).bs (p.1.2, p.2))
          (fun p : (N × P) × M => (S p.1.1).ϕ (p.1.2, p.2)) ((t, s), x))
        ((t, s), x) :=
      by
      apply
        (smooth_at_one_jet_bundle.mp <|
              SmoothAt.comp _ (S.smooth (t, (s, x))) (smooth_prod_assoc ((t, s), x))).2.2
    have h2 :
      SmoothAt ((J.prod IP).prod I) 𝓘(ℝ, E →L[ℝ] EP × E)
        (inTangentCoordinates I (IP.prod I) Prod.snd (fun p : (N × P) × M => (p.1.2, p.2))
          (fun p : (N × P) × M => mfderiv I (IP.prod I) (fun x : M => (p.1.2, x)) p.2) ((t, s), x))
        ((t, s), x) :=
      by
      apply
        ContMDiffAt.mfderiv (fun (p : (N × P) × M) (x : M) => (p.1.2, x)) Prod.snd
          (smooth_at_fst.fst.snd.prod_mk smoothAt_snd :
            SmoothAt (((J.prod IP).prod I).prod I) (IP.prod I) _ (((t, s), x), x))
          (smoothAt_snd : SmoothAt ((J.prod IP).prod I) _ _ _) le_top
    exact h1.clm_comp_in_tangent_coordinates (continuous_at_fst.snd.prod continuousAt_snd) h2

theorem FamilyOneJetSec.curry_bs (S : FamilyOneJetSec (IP.prod I) (P × M) I' M' J N) (p : N × P)
    (x : M) : (S.curry p).bs x = (S p.1).bs (p.2, x) :=
  rfl

theorem FamilyOneJetSec.curry_ϕ (S : FamilyOneJetSec (IP.prod I) (P × M) I' M' J N) (p : N × P)
    (x : M) : (S.curry p).ϕ x = (S p.1).ϕ (p.2, x) ∘L mfderiv I (IP.prod I) (fun x => (p.2, x)) x :=
  rfl

theorem FamilyOneJetSec.curry_ϕ' (S : FamilyOneJetSec (IP.prod I) (P × M) I' M' J N) (p : N × P)
    (x : M) : (S.curry p).ϕ x = (S p.1).ϕ (p.2, x) ∘L ContinuousLinearMap.inr ℝ EP E :=
  by
  rw [S.curry_ϕ]
  congr 1
  refine' ((mdifferentiableAt_const I IP).mfderiv_prod smooth_id.mdifferentiable_at).trans _
  rw [mfderiv_id, mfderiv_const]
  rfl

theorem FormalSol.eq_iff {F₁ F₂ : FormalSol R} {x : M} :
    F₁ x = F₂ x ↔ F₁.bs x = F₂.bs x ∧ F₁.ϕ x = by apply F₂.ϕ x :=
  by
  simp_rw [Bundle.TotalSpace.ext_iff, FormalSol.fst_eq, heq_iff_eq, Prod.ext_iff, eq_self_iff_true,
    true_and_iff]
  rfl

theorem FamilyOneJetSec.isHolonomicAtCurry (S : FamilyOneJetSec (IP.prod I) (P × M) I' M' J N)
    {t : N} {s : P} {x : M} (hS : (S t).IsHolonomicAt (s, x)) : (S.curry (t, s)).IsHolonomicAt x :=
  by
  simp_rw [OneJetSec.IsHolonomicAt, (S.curry _).snd_eq, S.curry_ϕ] at hS ⊢
  dsimp only
  rw [show (S.curry (t, s)).bs = fun x => (S.curry (t, s)).bs x from rfl, funext (S.curry_bs _)]
  dsimp only
  refine'
    (mfderiv_comp x (S t).smooth_bs.MDifferentiableAt
          ((mdifferentiableAt_const I IP).prod_mk smooth_id.mdifferentiable_at)).trans
      _
  rw [id, hS]
  rfl

theorem FamilyOneJetSec.curry_mem (S : FamilyOneJetSec (IP.prod I) (P × M) I' M' J N) {p : N × P}
    {x : M} (hR : S p.1 (p.2, x) ∈ R.relativize IP P) : S.curry p x ∈ R :=
  by
  simp_rw [RelMfld.relativize, mem_preimage, bundleSnd_eq, OneJetSec.coe_apply, mapLeft] at hR ⊢
  convert hR
  ext v
  simp_rw [S.curry_ϕ']

def FamilyFormalSol.curry (S : FamilyFormalSol J N (R.relativize IP P)) :
    FamilyFormalSol (J.prod IP) (N × P) R :=
  ⟨S.toFamilyOneJetSec.curry, fun p x => S.toFamilyOneJetSec.curry_mem S.is_sol⟩

theorem FamilyFormalSol.curry_ϕ' (S : FamilyFormalSol J N (R.relativize IP P)) (p : N × P) (x : M) :
    (S.curry p).ϕ x = (S p.1).ϕ (p.2, x) ∘L ContinuousLinearMap.inr ℝ EP E :=
  S.toFamilyOneJetSec.curry_ϕ' p x

theorem curry_eq_iff_eq_uncurry {𝓕 : FamilyFormalSol J N (R.relativize IP P)}
    {𝓕₀ : FamilyFormalSol IP P R} {t : N} {x : M} {s : P} (h : 𝓕 t (s, x) = 𝓕₀.uncurry (s, x)) :
    (𝓕.curry (t, s)) x = 𝓕₀ s x :=
  by
  simp_rw [FormalSol.eq_iff] at h ⊢
  refine' ⟨h.1, _⟩
  simp_rw [𝓕.curry_ϕ', h.2, 𝓕₀.uncurry_ϕ']
  ext v
  simp_rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', ContinuousLinearMap.map_zero, zero_add]
  rfl

theorem RelMfld.SatisfiesHPrinciple.satisfiesHPrincipleWith (R : RelMfld I M IX X) {C : Set (P × M)}
    (ε : M → ℝ) (h : (R.relativize IP P).SatisfiesHPrinciple C fun x => ε x.2) :
    R.SatisfiesHPrincipleWith IP C ε := by
  intro 𝓕₀ h𝓕₀
  obtain ⟨𝓕, h1𝓕, h2𝓕, h3𝓕, h4𝓕⟩ :=
    h 𝓕₀.uncurry (h𝓕₀.mono fun p hp => 𝓕₀.to_family_one_jet_sec.is_holonomic_uncurry.mpr hp)
  refine' ⟨𝓕.curry, _, _, _, _⟩
  · intro s x; exact curry_eq_iff_eq_uncurry (h1𝓕 (s, x))
  · intro s x; exact 𝓕.to_family_one_jet_sec.is_holonomic_at_curry (h2𝓕 (s, x))
  · refine' h3𝓕.mono _; rintro ⟨s, x⟩ hp t; exact curry_eq_iff_eq_uncurry (hp t)
  · intro t s x; exact h4𝓕 t (s, x)

end ParameterSpace

