import SphereEversion.Local.AmpleRelation
import SphereEversion.Global.Relation

/-! # Link with the local story

This file bridges the gap between Chapter 2 and Chapter 3. It builds on
`SmoothEmbedding.lean` but goes all the way to vector spaces (the previous file
is about embedding any manifold into another one).
-/


noncomputable section

open scoped Topology Manifold ContDiff
open Set ContinuousLinearMap

section Loc

/-! ## Localizing relations and 1-jet sections

Now we really bridge the gap all the way to vector spaces.
-/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']

/-- Convert a 1-jet section between vector spaces seen as manifold to a 1-jet section
between those vector spaces. -/
def OneJetSec.loc (F : OneJetSec 𝓘(ℝ, E) E 𝓘(ℝ, E') E') : JetSec E E' where
  f := F.bs
  f_diff := F.contMDiff_bs.contDiff
  φ x := (F x).2
  φ_diff := by
    rw [contDiff_iff_contDiffAt]
    intro x₀
    have : ContMDiffAt _ _ _ _ _ := F.contMDiff x₀
    simp_rw +unfoldPartialApp [contMDiffAt_oneJetBundle, inTangentCoordinates, inCoordinates,
      TangentBundle.symmL_model_space, TangentBundle.continuousLinearMapAt_model_space,
      ContinuousLinearMap.one_def, ContinuousLinearMap.comp_id, TangentSpace,
      ContinuousLinearMap.id_comp] at this
    exact this.2.2.contDiffAt

theorem OneJetSec.loc_hol_at_iff (F : OneJetSec 𝓘(ℝ, E) E 𝓘(ℝ, E') E') (x : E) :
    F.loc.IsHolonomicAt x ↔ F.IsHolonomicAt x := by
  dsimp only [OneJetSec.IsHolonomicAt]
  rw [mfderiv_eq_fderiv]
  exact Iff.rfl

/-- Turns a relation between `E` and `E'` seen as manifolds into a relation between them
seen as vector spaces. One annoying bit is `equiv.prod_assoc E E' (E →L[ℝ] E')` that is needed
to reassociate a product of types. -/
def RelMfld.relLoc (R : RelMfld 𝓘(ℝ, E) E 𝓘(ℝ, E') E') : RelLoc E E' :=
  (Homeomorph.prodAssoc _ _ _).symm ⁻¹'
    ((oneJetBundleModelSpaceHomeomorph 𝓘(ℝ, E) 𝓘(ℝ, E')).symm ⁻¹' R)

theorem ample_of_ample (R : RelMfld 𝓘(ℝ, E) E 𝓘(ℝ, E') E') (hR : R.Ample) : R.relLoc.IsAmple := by
  rintro p ⟨x, y, ϕ⟩; exact @hR ⟨(x, y), ϕ⟩ p

theorem isOpen_of_isOpen (R : RelMfld 𝓘(ℝ, E) E 𝓘(ℝ, E') E') (hR : IsOpen R) : IsOpen R.relLoc :=
  (Homeomorph.isOpen_preimage _).mpr <| (Homeomorph.isOpen_preimage _).mpr hR

end Loc

section Unloc

/-! ## Unlocalizing relations and 1-jet sections
-/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']

/-- Convert a 1-jet section between vector spaces to a 1-jet section
between those vector spaces seen as manifolds. -/
def JetSec.unloc (𝓕 : JetSec E E') : OneJetSec 𝓘(ℝ, E) E 𝓘(ℝ, E') E' where
  bs := 𝓕.f
  ϕ x := (𝓕 x).2
  contMDiff' := by
    refine fun a ↦ contMDiffAt_oneJetBundle.mpr ⟨contMDiffAt_id, 𝓕.f_diff.contMDiff a, ?_⟩
    rw [inTangentCoordinates_model_space]
    exact 𝓕.φ_diff.contMDiff a

theorem JetSec.unloc_hol_at_iff (𝓕 : JetSec E E') (x : E) :
    𝓕.unloc.IsHolonomicAt x ↔ 𝓕.IsHolonomicAt x := by
  dsimp only [OneJetSec.IsHolonomicAt]
  rw [mfderiv_eq_fderiv]
  exact Iff.rfl

def HtpyJetSec.unloc (𝓕 : HtpyJetSec E E') : HtpyOneJetSec 𝓘(ℝ, E) E 𝓘(ℝ, E') E' where
  bs t := (𝓕 t).f
  ϕ t x := (𝓕 t x).2
  contMDiff' := by
    intro a
    refine contMDiffAt_oneJetBundle.mpr ⟨contMDiffAt_snd, ?_, ?_⟩
    · apply (𝓕.f_diff.contMDiff (a.fst, a.snd)).comp a
        (contMDiffAt_fst.prodMk_space contMDiffAt_snd)
    · -- TODO: Investigate why we need so many different tactics before the apply
      unfold inTangentCoordinates
      dsimp [inCoordinates, chartAt]
      simp only [TangentBundle.trivializationAt_baseSet, OpenPartialHomeomorph.refl_partialEquiv,
        PartialEquiv.refl_source, OpenPartialHomeomorph.singletonChartedSpace_chartAt_eq, mem_univ,
        VectorBundleCore.trivializationAt_continuousLinearMapAt, tangentBundleCore_indexAt,
        TangentBundle.coordChange_model_space, one_def, VectorBundleCore.trivializationAt_symmL,
        comp_id]
      exact (𝓕.φ_diff.contMDiff (a.fst, a.snd)).comp a
        (contMDiffAt_fst.prodMk_space contMDiffAt_snd)

end Unloc

universe u₁ u₂ u₃ u₄ u₅ u₆
variable {E : Type u₁} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type u₂} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (M : Type u₃) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type u₄} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type u₅} [TopologicalSpace H'] (I' : ModelWithCorners ℝ E' H')
  (M' : Type u₆) [MetricSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
  {R : RelMfld I M I' M'}

/-- A pair of charts together with a compact subset of the first vector space. -/
structure ChartPair where
  φ : OpenSmoothEmbedding 𝓘(ℝ, E) E I M
  ψ : OpenSmoothEmbedding 𝓘(ℝ, E') E' I' M'
  K₁ : Set E
  hK₁ : IsCompact K₁

variable (p : ChartPair I M I' M') {I M I' M'}

def FormalSol.localize (F : FormalSol R) (hF : range (F.bs ∘ p.φ) ⊆ range p.ψ) :
    (R.localize p.φ p.ψ).relLoc.FormalSol :=
  { (F.toOneJetSec.localize p.φ p.ψ hF).loc with
    is_sol := fun _ ↦ (F.localize_mem_iff p.φ p.ψ hF).mpr (F.is_sol _) }

theorem FormalSol.isHolonomicLocalize (F : FormalSol R) (hF : range (F.bs ∘ p.φ) ⊆ range p.ψ) (x)
    (hx : F.IsHolonomicAt (p.φ x)) : (F.localize p hF).IsHolonomicAt x :=
  (OneJetSec.loc_hol_at_iff _ _).mpr <|
    (isHolonomicAt_localize_iff F.toOneJetSec p.φ p.ψ hF x).mpr hx

variable (F : _root_.HtpyFormalSol R) (𝓕 : (R.localize p.φ p.ψ).relLoc.HtpyFormalSol)

structure ChartPair.compat' (F : FormalSol R) (𝓕 : (R.localize p.φ p.ψ).relLoc.HtpyFormalSol) :
    Prop where
  hF : range (F.bs ∘ p.φ) ⊆ range p.ψ
  hFF : ∀ x ∉ p.K₁, ∀ t, 𝓕 t x = F.localize p hF x

def RelLoc.HtpyFormalSol.unloc : _root_.HtpyFormalSol (RelMfld.localize p.φ p.ψ R) :=
  { 𝓕.toHtpyJetSec.unloc with is_sol' := 𝓕.is_sol }

omit [IsManifold I ∞ M] [IsManifold I' ∞ M'] in
theorem RelLoc.HtpyFormalSol.unloc_congr {𝓕 𝓕' : (R.localize p.φ p.ψ).relLoc.HtpyFormalSol} {t t' x}
    (h : 𝓕 t x = 𝓕' t' x) : 𝓕.unloc p t x = 𝓕'.unloc p t' x := by
  ext1
  · rfl
  · change (𝓕 t x).1 = (𝓕' t' x).1
    rw [h]
  · change (𝓕 t x).2 = (𝓕' t' x).2
    rw [h]

omit [IsManifold I ∞ M] [IsManifold I' ∞ M'] in
theorem RelLoc.HtpyFormalSol.unloc_congr_const {𝓕 : (R.localize p.φ p.ψ).relLoc.HtpyFormalSol}
    {𝓕' : (R.localize p.φ p.ψ).relLoc.FormalSol} {t x} (h : 𝓕 t x = 𝓕' x) :
    𝓕.unloc p t x = 𝓕'.unloc x := by
  ext1
  · rfl
  · change (𝓕 t x).1 = (𝓕' x).1
    rw [h]
  · change (𝓕 t x).2 = (𝓕' x).2
    rw [h]

omit [IsManifold I ∞ M] [IsManifold I' ∞ M'] in
theorem RelLoc.HtpyFormalSol.unloc_congr' {𝓕 𝓕' : (R.localize p.φ p.ψ).relLoc.HtpyFormalSol} {t t'}
    (h : 𝓕 t = 𝓕' t') : 𝓕.unloc p t = 𝓕'.unloc p t' := by
  apply FormalSol.coe_inj fun x ↦ RelLoc.HtpyFormalSol.unloc_congr _ ?_
  rw [h]

@[simp]
theorem FormalSol.transfer_unloc_localize (F : FormalSol R) (hF : range (F.bs ∘ p.φ) ⊆ range p.ψ)
    (x : E) : p.φ.transfer p.ψ ((F.localize p hF).unloc x) = F (p.φ x) :=
  transfer_localize F.toOneJetSec p.φ p.ψ hF x

lemma ChartPair.mkHtpy_aux {F : FormalSol R} {𝓕 : (R.localize p.φ p.ψ).relLoc.HtpyFormalSol}
    (h : p.compat' F 𝓕) (t x) (hx : x ∉ p.K₁) :
    F (p.φ x) = OneJetBundle.embedding p.φ p.ψ (RelLoc.HtpyFormalSol.unloc p 𝓕 t x) := by
  rw [← F.transfer_unloc_localize p h.1, RelLoc.HtpyFormalSol.unloc_congr_const p (h.hFF x hx t)]
  rfl

variable [T2Space M]

def ChartPair.mkHtpy (F : FormalSol R) (𝓕 : (R.localize p.φ p.ψ).relLoc.HtpyFormalSol) :
    HtpyFormalSol R := by
  classical exact if h : p.compat' F 𝓕 then
    p.φ.updateFormalSol p.ψ F (𝓕.unloc p) p.hK₁ (p.mkHtpy_aux h)
  else F.constHtpy

theorem ChartPair.mkHtpy_congr (F : FormalSol R) {𝓕 : (R.localize p.φ p.ψ).relLoc.HtpyFormalSol}
    {t t' : ℝ} (h : 𝓕 t = 𝓕 t') : p.mkHtpy F 𝓕 t = p.mkHtpy F 𝓕 t' := by
  unfold ChartPair.mkHtpy
  by_cases hF : p.compat' F 𝓕
  · simp only [dif_pos hF]
    apply FormalSol.coe_inj fun x ↦ ?_
    rw [p.φ.updateFormalSol_apply, p.φ.updateFormalSol_apply,
      RelLoc.HtpyFormalSol.unloc_congr' p h]
  · simp only [dif_neg hF]; rfl

theorem ChartPair.mkHtpy_eq_self (F : FormalSol R) (𝓕 : (R.localize p.φ p.ψ).relLoc.HtpyFormalSol)
    {t m} (hm : ∀ hF : range (F.bs ∘ p.φ) ⊆ range p.ψ, ∀ x ∈ p.K₁,
    m = p.φ x → 𝓕 t x = F.localize p hF x) : p.mkHtpy F 𝓕 t m = F m := by
  rw [ChartPair.mkHtpy]
  split_ifs with h
  · refine (p.φ.Jupdate_apply p.ψ p.hK₁ (p.mkHtpy_aux h) t m).trans ?_
    unfold OpenSmoothEmbedding.update
    split_ifs with h'
    · obtain ⟨x, rfl⟩ := h'
      rw [OneJetBundle.embedding_toFun, p.φ.left_inv]
      have : (𝓕 t).unloc x = F.toOneJetSec.localize p.φ p.ψ h.hF x := by
        have : 𝓕 t x = F.localize p h.hF x := by
          by_cases h'' : x ∈ p.K₁
          · exact hm h.hF x h'' rfl
          · exact h.hFF x h'' t
        rw [Prod.ext_iff] at this
        ext1
        · rfl
        · exact this.1
        · exact this.2
      change p.φ.transfer p.ψ ((𝓕 t).unloc x) = F (p.φ x)
      rw [this, transfer_localize]
      rfl
    rfl
  rfl

theorem ChartPair.mkHtpy_eq_of_not_mem (F : FormalSol R)
    (𝓕 : (R.localize p.φ p.ψ).relLoc.HtpyFormalSol) {t} {m} (hm : m ∉ p.φ '' p.K₁) :
    p.mkHtpy F 𝓕 t m = F m :=
  ChartPair.mkHtpy_eq_self p F 𝓕 <| by rintro hF x hx rfl; exfalso; exact hm (mem_image_of_mem _ hx)

theorem ChartPair.mkHtpy_eq_of_eq (F : FormalSol R) (𝓕 : (R.localize p.φ p.ψ).relLoc.HtpyFormalSol)
    (h𝓕 : p.compat' F 𝓕) {t x} (h : 𝓕 t x = F.localize p h𝓕.1 x) :
    p.mkHtpy F 𝓕 t (p.φ x) = F (p.φ x) := by
  dsimp only [ChartPair.mkHtpy]
  split_ifs
  simp only [OpenSmoothEmbedding.updateFormalSol_apply_image]
  rw [RelLoc.HtpyFormalSol.unloc_congr_const p, FormalSol.transfer_unloc_localize p F h𝓕.1 x]
  exact h

theorem ChartPair.mkHtpy_eq_of_forall {F : FormalSol R}
    {𝓕 : (R.localize p.φ p.ψ).relLoc.HtpyFormalSol} (h𝓕 : p.compat' F 𝓕) {t}
    (h : 𝓕 t = F.localize p h𝓕.1) : p.mkHtpy F 𝓕 t = F :=
  FormalSol.coe_inj fun m ↦ ChartPair.mkHtpy_eq_self p F 𝓕 <| by rintro hF y _ rfl; · rw [h]; rfl

theorem ChartPair.mkHtpy_localize {F : FormalSol R} {𝓕 : (R.localize p.φ p.ψ).relLoc.HtpyFormalSol}
    {t e} (h : p.compat' F 𝓕) (rg : range ((p.mkHtpy F 𝓕 t).bs ∘ p.φ) ⊆ range p.ψ) :
    (p.mkHtpy F 𝓕 t).toOneJetSec.localize p.φ p.ψ rg e = (𝓕 t).unloc e := by
  simp_rw [ChartPair.mkHtpy, dif_pos h] at rg ⊢
  exact p.φ.Jupdate_localize p.ψ p.hK₁ (p.mkHtpy_aux h) t rg e

theorem ChartPair.mkHtpy_isHolonomicAt_iff {F : FormalSol R}
    {𝓕 : (R.localize p.φ p.ψ).relLoc.HtpyFormalSol} (h : p.compat' F 𝓕) {t e} :
    (p.mkHtpy F 𝓕 t).IsHolonomicAt (p.φ e) ↔ (𝓕 t).IsHolonomicAt e := by
  have rg : range ((p.mkHtpy F 𝓕 t).bs ∘ p.φ) ⊆ range p.ψ := by
    rintro - ⟨e, rfl⟩
    dsimp only [ChartPair.mkHtpy]
    simp only [dif_pos h]
    rw [p.φ.updateFormalSol_bs p.ψ p.hK₁]
    simp only [Function.comp_apply, OpenSmoothEmbedding.update_apply_embedding, mem_range_self]
  rw [← isHolonomicAt_localize_iff _ p.φ p.ψ rg e, ← JetSec.unloc_hol_at_iff]
  exact OneJetSec.isHolonomicAt_congr (Filter.Eventually.of_forall fun e ↦ p.mkHtpy_localize h rg)

theorem ChartPair.dist_update' [FiniteDimensional ℝ E'] {δ : M → ℝ} (hδ_pos : ∀ x, 0 < δ x)
    (hδ_cont : Continuous δ) {F : FormalSol R} (hF : range (F.bs ∘ p.φ) ⊆ range p.ψ) :
    ∃ η > (0 : ℝ),
      ∀ {𝓕 : (R.localize p.φ p.ψ).relLoc.HtpyFormalSol}, p.compat' F 𝓕 →
      ∀ e ∈ p.K₁,∀ t ∈ (Icc 0 1 : Set ℝ), ‖(𝓕 t).f e - (F.localize p hF).f e‖ < η →
      dist (((p.mkHtpy F 𝓕) t).bs <| p.φ e) (F.bs <| p.φ e) < δ (p.φ e) := by
  let bsF m := F.bs m
  have : ∀ 𝓕 : (R.localize p.φ p.ψ).relLoc.HtpyFormalSol, p.compat' F 𝓕 → ∀ t e,
       (p.mkHtpy F 𝓕 t).bs (p.φ e) = p.φ.update p.ψ bsF (fun e ↦ (𝓕.unloc p t).bs e) (p.φ e) := by
    -- TODO: this proof needs more lemmas
    intro 𝓕 h𝓕 t e
    change (p.mkHtpy F 𝓕 t (p.φ e)).1.2 = p.φ.update p.ψ bsF (fun e ↦ (𝓕.unloc p t).bs e) (p.φ e)
    dsimp only [ChartPair.mkHtpy]
    rw [dif_pos h𝓕, OpenSmoothEmbedding.updateFormalSol_apply]
    simp_rw [OpenSmoothEmbedding.update_apply_embedding, OneJetBundle.embedding_toFun,
      OpenSmoothEmbedding.transfer_proj_snd]
    rfl
  rcases p.φ.dist_update p.ψ p.hK₁ (isCompact_Icc : IsCompact (Icc 0 1 : Set ℝ))
      (fun _t m ↦ F.bs m) (F.contMDiff_bs.continuous.comp continuous_snd)
      (fun _t ↦ range_comp bsF p.φ ▸ hF) hδ_pos hδ_cont with
    ⟨η, η_pos, hη⟩
  refine ⟨η, η_pos, ?_⟩
  intro 𝓕 H e he t ht het
  simp only [this 𝓕 H]
  rw [← dist_eq_norm] at het
  exact hη (fun t e ↦ (𝓕.unloc p t).bs e) 1 ⟨zero_le_one, le_rfl⟩ t ht e he het
