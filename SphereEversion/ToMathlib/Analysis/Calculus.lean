import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import SphereEversion.ToMathlib.Topology.Misc

noncomputable section

open Set Function Filter

open scoped Topology ContDiff

namespace Real

theorem smoothTransition_projI {x : ℝ} : smoothTransition (projI x) = smoothTransition x :=
  smoothTransition.projIcc

end Real

section Calculus

open ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] {E₂ : Type*}
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂] {E' : Type*} [NormedAddCommGroup E']
  [NormedSpace 𝕜 E'] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type*}
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] {n : WithTop ℕ∞}

theorem fderiv_prod_left {x₀ : E} {y₀ : F} :
    fderiv 𝕜 (fun x ↦ (x, y₀)) x₀ = ContinuousLinearMap.inl 𝕜 E F :=
  ((hasFDerivAt_id _).prodMk (hasFDerivAt_const _ _)).fderiv

theorem fderiv_prod_right {x₀ : E} {y₀ : F} :
    fderiv 𝕜 (fun y ↦ (x₀, y)) y₀ = ContinuousLinearMap.inr 𝕜 E F :=
  ((hasFDerivAt_const _ _).prodMk (hasFDerivAt_id _)).fderiv

theorem HasFDerivAt.partial_fst {φ : E → F → G} {φ' : E × F →L[𝕜] G} {e₀ : E} {f₀ : F}
    (h : HasFDerivAt (uncurry φ) φ' (e₀, f₀)) :
    HasFDerivAt (fun e ↦ φ e f₀) (φ'.comp (inl 𝕜 E F)) e₀ := by
  exact h.comp e₀ <| hasFDerivAt_prodMk_left (𝕜 := 𝕜) e₀ f₀

theorem HasFDerivAt.partial_snd {φ : E → F → G} {φ' : E × F →L[𝕜] G} {e₀ : E} {f₀ : F}
    (h : HasFDerivAt (uncurry φ) φ' (e₀, f₀)) :
    HasFDerivAt (fun f ↦ φ e₀ f) (φ'.comp (inr 𝕜 E F)) f₀ :=
  h.comp f₀ <| hasFDerivAt_prodMk_right e₀ f₀

theorem fderiv_prod_eq_add {f : E × F → G} {p : E × F} (hf : DifferentiableAt 𝕜 f p) :
    fderiv 𝕜 f p =
      fderiv 𝕜 (fun z : E × F ↦ f (z.1, p.2)) p + fderiv 𝕜 (fun z : E × F ↦ f (p.1, z.2)) p := by
  have H₁ : fderiv 𝕜 (fun z : E × F ↦ f (z.1, p.2)) p =
      (fderiv 𝕜 f p).comp (.comp (.inl 𝕜 E F) (.fst 𝕜 E F)) :=
    (hf.hasFDerivAt.comp p
      ((hasFDerivAt_fst (𝕜 := 𝕜) (E := E) (F := F)).prodMk (hasFDerivAt_const p.2 _))).fderiv
  have H₂ : fderiv 𝕜 (fun z : E × F ↦ f (p.1, z.2)) p =
      (fderiv 𝕜 f p).comp (.comp (.inr 𝕜 E F) (.snd 𝕜 E F)) :=
    (hf.hasFDerivAt.comp _ ((hasFDerivAt_const p.1 _).prodMk
      (hasFDerivAt_snd (𝕜 := 𝕜) (E := E) (F := F)))).fderiv
  rw [H₁, H₂, ← comp_add, comp_fst_add_comp_snd, coprod_inl_inr, ContinuousLinearMap.comp_id]

variable (𝕜)

/-- The first partial derivative of a binary function. -/
def partialFDerivFst {F : Type*} (φ : E → F → G) : E → F → E →L[𝕜] G := fun (e₀ : E) (f₀ : F) ↦
  fderiv 𝕜 (fun e ↦ φ e f₀) e₀

/-- The second partial derivative of a binary function. -/
def partialFDerivSnd {E : Type*} (φ : E → F → G) : E → F → F →L[𝕜] G := fun (e₀ : E) (f₀ : F) ↦
  fderiv 𝕜 (fun f ↦ φ e₀ f) f₀

@[inherit_doc] local notation "∂₁" => partialFDerivFst

@[inherit_doc] local notation "∂₂" => partialFDerivSnd

variable {𝕜}

theorem fderiv_partial_fst {φ : E → F → G} {φ' : E × F →L[𝕜] G} {e₀ : E} {f₀ : F}
    (h : HasFDerivAt (uncurry φ) φ' (e₀, f₀)) : ∂₁ 𝕜 φ e₀ f₀ = φ'.comp (inl 𝕜 E F) :=
  h.partial_fst.fderiv

theorem fderiv_partial_snd {φ : E → F → G} {φ' : E × F →L[𝕜] G} {e₀ : E} {f₀ : F}
    (h : HasFDerivAt (uncurry φ) φ' (e₀, f₀)) : ∂₂ 𝕜 φ e₀ f₀ = φ'.comp (inr 𝕜 E F) :=
  h.partial_snd.fderiv

theorem DifferentiableAt.hasFDerivAt_partial_fst {φ : E → F → G} {e₀ : E} {f₀ : F}
    (h : DifferentiableAt 𝕜 (uncurry φ) (e₀, f₀)) :
    HasFDerivAt (fun e ↦ φ e f₀) (partialFDerivFst 𝕜 φ e₀ f₀) e₀ := by
  apply (h.comp e₀ <| differentiableAt_id.prodMk <| differentiableAt_const f₀).hasFDerivAt (𝕜 := 𝕜)

theorem DifferentiableAt.hasFDerivAt_partial_snd {φ : E → F → G} {e₀ : E} {f₀ : F}
    (h : DifferentiableAt 𝕜 (uncurry φ) (e₀, f₀)) :
    HasFDerivAt (fun f ↦ φ e₀ f) (partialFDerivSnd 𝕜 φ e₀ f₀) f₀ := by
  rw [fderiv_partial_snd h.hasFDerivAt]
  exact h.hasFDerivAt.partial_snd

theorem ContDiff.partial_fst {φ : E → F → G} {n : ℕ∞} (h : ContDiff 𝕜 n <| uncurry φ) (f₀ : F) :
    ContDiff 𝕜 n fun e ↦ φ e f₀ :=
  h.comp <| contDiff_prodMk_left f₀

theorem ContDiff.partial_snd {φ : E → F → G} {n : ℕ∞} (h : ContDiff 𝕜 n <| uncurry φ) (e₀ : E) :
    ContDiff 𝕜 n fun f ↦ φ e₀ f :=
  h.comp <| contDiff_prodMk_right e₀

/-- Precomposition by a continuous linear map as a continuous linear map between spaces of
continuous linear maps. -/
def ContinuousLinearMap.compRightL (φ : E →L[𝕜] F) : (F →L[𝕜] G) →L[𝕜] E →L[𝕜] G :=
  precomp G φ

/-- Postcomposition by a continuous linear map as a continuous linear map between spaces of
continuous linear maps. -/
def ContinuousLinearMap.compLeftL (φ : F →L[𝕜] G) : (E →L[𝕜] F) →L[𝕜] E →L[𝕜] G :=
  postcomp E φ

nonrec theorem Differentiable.fderiv_partial_fst {φ : E → F → G}
    (hF : Differentiable 𝕜 (uncurry φ)) :
    ↿(∂₁ 𝕜 φ) = precomp G (inl 𝕜 E F) ∘ (fderiv 𝕜 <| uncurry φ) := by
  ext1 ⟨y, t⟩; exact fderiv_partial_fst (hF ⟨y, t⟩).hasFDerivAt

nonrec theorem Differentiable.fderiv_partial_snd {φ : E → F → G}
    (hF : Differentiable 𝕜 (uncurry φ)) :
    ↿(∂₂ 𝕜 φ) = precomp G (inr 𝕜 E F) ∘ (fderiv 𝕜 <| uncurry φ) := by
  ext1 ⟨y, t⟩; exact fderiv_partial_snd (hF ⟨y, t⟩).hasFDerivAt

/-- The first partial derivative of `φ : 𝕜 → F → G` seen as a function from `𝕜 → F → G` -/
def partialDerivFst (φ : 𝕜 → F → G) : 𝕜 → F → G := fun k f ↦ ∂₁ 𝕜 φ k f 1

/-- The second partial derivative of `φ : E → 𝕜 → G` seen as a function from `E → 𝕜 → G` -/
def partialDerivSnd (φ : E → 𝕜 → G) : E → 𝕜 → G := fun e k ↦ ∂₂ 𝕜 φ e k 1

omit [NormedAddCommGroup F] [NormedSpace 𝕜 F] in
theorem partialFDerivFst_eq_smulRight (φ : 𝕜 → F → G) (k : 𝕜) (f : F) :
    ∂₁ 𝕜 φ k f = smulRight (1 : 𝕜 →L[𝕜] 𝕜) (partialDerivFst φ k f) :=
  deriv_fderiv.symm

omit [NormedAddCommGroup F] [NormedSpace 𝕜 F] in
@[simp]
theorem partialFDerivFst_one (φ : 𝕜 → F → G) (k : 𝕜) (f : F) :
    ∂₁ 𝕜 φ k f 1 = partialDerivFst φ k f := by
  simp [partialFDerivFst_eq_smulRight]

omit [NormedAddCommGroup E] [NormedSpace 𝕜 E] in
theorem partialFDerivSnd_eq_smulRight (φ : E → 𝕜 → G) (e : E) (k : 𝕜) :
    ∂₂ 𝕜 φ e k = smulRight (1 : 𝕜 →L[𝕜] 𝕜) (partialDerivSnd φ e k) :=
  deriv_fderiv.symm

omit [NormedAddCommGroup E] [NormedSpace 𝕜 E] in
theorem partialFDerivSnd_one (φ : E → 𝕜 → G) (e : E) (k : 𝕜) :
    ∂₂ 𝕜 φ e k 1 = partialDerivSnd φ e k := by
  simp [partialFDerivSnd_eq_smulRight]

@[to_additive]
nonrec theorem WithTop.le_mul_self {α : Type*} [CommMonoid α] [PartialOrder α] [IsOrderedMonoid α]
    [CanonicallyOrderedMul α] (n m : α) :
    (n : WithTop α) ≤ (m * n : α) :=
  WithTop.coe_le_coe.mpr le_mul_self

@[to_additive]
nonrec theorem WithTop.le_self_mul {α : Type*} [CommMonoid α] [PartialOrder α] [IsOrderedMonoid α]
    [CanonicallyOrderedMul α] (n m : α) :
    (n : WithTop α) ≤ (n * m : α) :=
  WithTop.coe_le_coe.mpr le_self_mul

theorem ContDiff.contDiff_partial_fst {φ : E → F → G} {n : ℕ}
    (hF : ContDiff 𝕜 (n + 1) (uncurry φ)) : ContDiff 𝕜 n ↿(∂₁ 𝕜 φ) :=
  ContDiff.fderiv (hF.comp <| contDiff_snd.prodMk contDiff_fst.snd) contDiff_fst le_rfl

theorem ContDiff.contDiff_partial_fst_apply {φ : E → F → G} {n : ℕ}
    (hF : ContDiff 𝕜 (n + 1) (uncurry φ)) {x : E} : ContDiff 𝕜 n ↿fun x' y ↦ ∂₁ 𝕜 φ x' y x :=
  (ContinuousLinearMap.apply 𝕜 G x).contDiff.comp hF.contDiff_partial_fst

theorem ContDiff.continuous_partial_fst {φ : E → F → G} {n : ℕ}
    (h : ContDiff 𝕜 ((n + 1 : ℕ) : ℕ∞) <| uncurry φ) : Continuous ↿(∂₁ 𝕜 φ) :=
  h.contDiff_partial_fst.continuous

-- XXX: fix this!
theorem ContDiff.contDiff_top_partial_fst {φ : E → F → G} (hF : ContDiff 𝕜 ∞ (uncurry φ)) :
    ContDiff 𝕜 ∞ ↿(∂₁ 𝕜 φ) :=
  contDiff_infty.mpr fun n ↦ (contDiff_infty.mp hF (n + 1)).contDiff_partial_fst

theorem ContDiff.contDiff_partial_snd {φ : E → F → G} {n : ℕ}
    (hF : ContDiff 𝕜 (n + 1) (uncurry φ)) : ContDiff 𝕜 n ↿(∂₂ 𝕜 φ) :=
  ContDiff.fderiv (hF.comp <| contDiff_fst.fst.prodMk contDiff_snd) contDiff_snd le_rfl

theorem ContDiff.contDiff_partial_snd_apply {φ : E → F → G} {n : ℕ}
    (hF : ContDiff 𝕜 (n + 1) (uncurry φ)) {y : F} : ContDiff 𝕜 n ↿fun x y' ↦ ∂₂ 𝕜 φ x y' y :=
  (ContinuousLinearMap.apply 𝕜 G y).contDiff.comp hF.contDiff_partial_snd

theorem ContDiff.continuous_partial_snd {φ : E → F → G} {n : ℕ}
    (h : ContDiff 𝕜 ((n + 1 : ℕ) : ℕ∞) <| uncurry φ) : Continuous ↿(∂₂ 𝕜 φ) :=
  h.contDiff_partial_snd.continuous

-- FIXME: upgrade again to include analyticity
theorem ContDiff.contDiff_top_partial_snd {φ : E → F → G} (hF : ContDiff 𝕜 ∞ (uncurry φ)) :
    ContDiff 𝕜 ∞ ↿(∂₂ 𝕜 φ) :=
  contDiff_infty.mpr fun n ↦ (contDiff_infty.mp (hF.of_le (by simp)) (n + 1)).contDiff_partial_snd

end Calculus

section RealCalculus -- PRed in #12673

open ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace ℝ F]

theorem ContDiff.lipschitzOnWith {s : Set E} {f : E → F} {n} (hf : ContDiff ℝ n f) (hn : 1 ≤ n)
    (hs : Convex ℝ s) (hs' : IsCompact s) : ∃ K, LipschitzOnWith K f s := by
  rcases (bddAbove_iff_exists_ge (0 : ℝ)).mp (hs'.image (hf.continuous_fderiv hn).norm).bddAbove
    with ⟨M, M_nonneg, hM⟩
  simp_rw [forall_mem_image] at hM
  use ⟨M, M_nonneg⟩
  exact Convex.lipschitzOnWith_of_nnnorm_fderiv_le (fun x _ ↦ hf.differentiable hn x) hM hs

end RealCalculus

open Filter

theorem const_mul_one_div_lt {ε : ℝ} (ε_pos : 0 < ε) (C : ℝ) : ∀ᶠ N : ℝ in atTop, C * ‖1 / N‖ < ε :=
  have h : Tendsto (fun N : ℝ ↦ C * ‖1 / N‖) atTop (𝓝 (C * ‖(0 : ℝ)‖)) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.div_atTop tendsto_id).norm
  Filter.Tendsto.eventually_lt h tendsto_const_nhds <| by simpa
