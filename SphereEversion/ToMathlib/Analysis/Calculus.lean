import Mathlib.Analysis.Calculus.BumpFunctionInner
import Mathlib.Analysis.Calculus.ContDiff
import SphereEversion.ToMathlib.Topology.Misc
import SphereEversion.ToMathlib.Topology.Algebra.Module

noncomputable section

open Set Function Filter

open scoped Topology

namespace Real

theorem smoothTransition_projI {x : ℝ} : smoothTransition (projI x) = smoothTransition x :=
  by
  cases' le_total (0 : ℝ) x with hx hx
  cases' le_total (1 : ℝ) x with h2x h2x
  · rw [proj_I_eq_one.mpr h2x, smooth_transition.one_of_one_le h2x, smooth_transition.one]
  · rw [proj_I_eq_self.mpr ⟨hx, h2x⟩]
  · rw [proj_I_eq_zero.mpr hx, smooth_transition.zero_of_nonpos hx, smooth_transition.zero]

end Real

section Calculus

open ContinuousLinearMap

variable {𝕜 : Type _} [NontriviallyNormedField 𝕜] {E : Type _} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {E₁ : Type _} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] {E₂ : Type _}
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂] {E' : Type _} [NormedAddCommGroup E']
  [NormedSpace 𝕜 E'] {F : Type _} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type _}
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] {n : ℕ∞}

theorem ContDiffAt.comp₂ {g : E₁ × E₂ → G} {f₁ : F → E₁} {f₂ : F → E₂} {x : F}
    (hg : ContDiffAt 𝕜 n g (f₁ x, f₂ x)) (hf₁ : ContDiffAt 𝕜 n f₁ x) (hf₂ : ContDiffAt 𝕜 n f₂ x) :
    ContDiffAt 𝕜 n (fun x => g (f₁ x, f₂ x)) x :=
  hg.comp x <| hf₁.Prod hf₂

theorem ContDiffAt.clm_comp {g : E' → F →L[𝕜] G} {f : E' → E →L[𝕜] F} {n : ℕ∞} {x : E'}
    (hg : ContDiffAt 𝕜 n g x) (hf : ContDiffAt 𝕜 n f x) : ContDiffAt 𝕜 n (fun x => g x ∘L f x) x :=
  isBoundedBilinearMap_comp.ContDiff.ContDiffAt.comp₂ hg hf

theorem fderiv_comp {g : F → G} {f : E → F} (x : E) (hg : DifferentiableAt 𝕜 g (f x))
    (hf : DifferentiableAt 𝕜 f x) : fderiv 𝕜 (g ∘ f) x = (fderiv 𝕜 g (f x)).comp (fderiv 𝕜 f x) :=
  (hg.HasFDerivAt.comp x hf.HasFDerivAt).fderiv

theorem fderiv_prod_left {x₀ : E} {y₀ : F} :
    fderiv 𝕜 (fun x => (x, y₀)) x₀ = ContinuousLinearMap.inl 𝕜 E F :=
  by
  refine' (differentiable_at_id.fderiv_prod (differentiableAt_const y₀)).trans _
  rw [fderiv_id, fderiv_const]
  rfl

theorem fderiv_prod_right {x₀ : E} {y₀ : F} :
    fderiv 𝕜 (fun y => (x₀, y)) y₀ = ContinuousLinearMap.inr 𝕜 E F :=
  by
  refine' ((differentiableAt_const x₀).fderiv_prod differentiableAt_id).trans _
  rw [fderiv_id, fderiv_const]
  rfl

theorem fderiv_prod_eq_add {f : E × F → G} {p : E × F} (hf : DifferentiableAt 𝕜 f p) :
    fderiv 𝕜 f p =
      fderiv 𝕜 (fun z : E × F => f (z.1, p.2)) p + fderiv 𝕜 (fun z : E × F => f (p.1, z.2)) p :=
  by
  rw [← @Prod.mk.eta _ _ p] at hf 
  rw [fderiv_comp p (by apply hf) (differentiable_at_fst.prod <| differentiableAt_const _),
    fderiv_comp p (by apply hf) ((differentiableAt_const _).Prod differentiableAt_snd), ←
    ContinuousLinearMap.comp_add, differentiable_at_fst.fderiv_prod (differentiableAt_const _),
    (differentiableAt_const _).fderiv_prod differentiableAt_snd, fderiv_fst, fderiv_snd,
    fderiv_const, fderiv_const]
  dsimp only [Pi.zero_apply]
  rw [Prod.mk.eta, ContinuousLinearMap.fst_prod_zero_add_zero_prod_snd, ContinuousLinearMap.comp_id]

theorem HasFDerivAt.partial_fst {φ : E → F → G} {φ' : E × F →L[𝕜] G} {e₀ : E} {f₀ : F}
    (h : HasFDerivAt (uncurry φ) φ' (e₀, f₀)) :
    HasFDerivAt (fun e => φ e f₀) (φ'.comp (inl 𝕜 E F)) e₀ :=
  h.comp e₀ <| hasFDerivAt_prod_mk_left e₀ f₀

theorem HasFDerivAt.partial_snd {φ : E → F → G} {φ' : E × F →L[𝕜] G} {e₀ : E} {f₀ : F}
    (h : HasFDerivAt (uncurry φ) φ' (e₀, f₀)) :
    HasFDerivAt (fun f => φ e₀ f) (φ'.comp (inr 𝕜 E F)) f₀ :=
  h.comp f₀ <| hasFDerivAt_prod_mk_right e₀ f₀

variable (𝕜)

/-- The first partial derivative of a binary function. -/
def partialFDerivFst {F : Type _} (φ : E → F → G) : E → F → E →L[𝕜] G := fun (e₀ : E) (f₀ : F) =>
  fderiv 𝕜 (fun e => φ e f₀) e₀

/-- The second partial derivative of a binary function. -/
def partialFDerivSnd {E : Type _} (φ : E → F → G) : E → F → F →L[𝕜] G := fun (e₀ : E) (f₀ : F) =>
  fderiv 𝕜 (fun f => φ e₀ f) f₀

local notation "∂₁" => partialFDerivFst

local notation "∂₂" => partialFDerivSnd

variable {𝕜}

theorem fderiv_partial_fst {φ : E → F → G} {φ' : E × F →L[𝕜] G} {e₀ : E} {f₀ : F}
    (h : HasFDerivAt (uncurry φ) φ' (e₀, f₀)) : ∂₁ 𝕜 φ e₀ f₀ = φ'.comp (inl 𝕜 E F) :=
  h.partial_fst.fderiv

theorem fderiv_partial_snd {φ : E → F → G} {φ' : E × F →L[𝕜] G} {e₀ : E} {f₀ : F}
    (h : HasFDerivAt (uncurry φ) φ' (e₀, f₀)) : ∂₂ 𝕜 φ e₀ f₀ = φ'.comp (inr 𝕜 E F) :=
  h.partial_snd.fderiv

theorem DifferentiableAt.hasFDerivAt_partial_fst {φ : E → F → G} {e₀ : E} {f₀ : F}
    (h : DifferentiableAt 𝕜 (uncurry φ) (e₀, f₀)) :
    HasFDerivAt (fun e => φ e f₀) (partialFDerivFst 𝕜 φ e₀ f₀) e₀ :=
  (h.comp e₀ <| differentiableAt_id.Prod <| differentiableAt_const f₀).HasFDerivAt

theorem DifferentiableAt.hasFDerivAt_partial_snd {φ : E → F → G} {e₀ : E} {f₀ : F}
    (h : DifferentiableAt 𝕜 (uncurry φ) (e₀, f₀)) :
    HasFDerivAt (fun f => φ e₀ f) (partialFDerivSnd 𝕜 φ e₀ f₀) f₀ :=
  by
  rw [fderiv_partial_snd h.has_fderiv_at]
  exact h.has_fderiv_at.partial_snd

theorem ContDiff.partial_fst {φ : E → F → G} {n : ℕ∞} (h : ContDiff 𝕜 n <| uncurry φ) (f₀ : F) :
    ContDiff 𝕜 n fun e => φ e f₀ :=
  h.comp <| contDiff_prod_mk_left f₀

theorem ContDiff.partial_snd {φ : E → F → G} {n : ℕ∞} (h : ContDiff 𝕜 n <| uncurry φ) (e₀ : E) :
    ContDiff 𝕜 n fun f => φ e₀ f :=
  h.comp <| contDiff_prod_mk_right e₀

/-- Precomposition by a continuous linear map as a continuous linear map between spaces of
continuous linear maps. -/
def ContinuousLinearMap.compRightL (φ : E →L[𝕜] F) : (F →L[𝕜] G) →L[𝕜] E →L[𝕜] G :=
  (compL 𝕜 E F G).flip φ

/-- Postcomposition by a continuous linear map as a continuous linear map between spaces of
continuous linear maps. -/
def ContinuousLinearMap.compLeftL (φ : F →L[𝕜] G) : (E →L[𝕜] F) →L[𝕜] E →L[𝕜] G :=
  compL 𝕜 E F G φ

theorem Differentiable.fderiv_partial_fst {φ : E → F → G} (hF : Differentiable 𝕜 (uncurry φ)) :
    ↿(∂₁ 𝕜 φ) = (fun ψ : E × F →L[𝕜] G => ψ.comp (inl 𝕜 E F)) ∘ (fderiv 𝕜 <| uncurry φ) := by
  ext1 ⟨y, t⟩; exact fderiv_partial_fst (hF ⟨y, t⟩).HasFDerivAt

theorem Differentiable.fderiv_partial_snd {φ : E → F → G} (hF : Differentiable 𝕜 (uncurry φ)) :
    ↿(∂₂ 𝕜 φ) = (fun ψ : E × F →L[𝕜] G => ψ.comp (inr 𝕜 E F)) ∘ (fderiv 𝕜 <| uncurry φ) := by
  ext1 ⟨y, t⟩; exact fderiv_partial_snd (hF ⟨y, t⟩).HasFDerivAt

/-- The first partial derivative of `φ : 𝕜 → F → G` seen as a function from `𝕜 → F → G`-/
def partialDerivFst (φ : 𝕜 → F → G) : 𝕜 → F → G := fun k f => ∂₁ 𝕜 φ k f 1

/-- The second partial derivative of `φ : E → 𝕜 → G` seen as a function from `E → 𝕜 → G`-/
def partialDerivSnd (φ : E → 𝕜 → G) : E → 𝕜 → G := fun e k => ∂₂ 𝕜 φ e k 1

theorem partialFDerivFst_eq_smulRight (φ : 𝕜 → F → G) (k : 𝕜) (f : F) :
    ∂₁ 𝕜 φ k f = smulRight (1 : 𝕜 →L[𝕜] 𝕜) (partialDerivFst φ k f) :=
  deriv_fderiv.symm

@[simp]
theorem partialFDerivFst_one (φ : 𝕜 → F → G) (k : 𝕜) (f : F) :
    ∂₁ 𝕜 φ k f 1 = partialDerivFst φ k f := by
  simp only [partialFDerivFst_eq_smulRight, smul_right_apply, one_apply, one_smul]

theorem partialFDerivSnd_eq_smulRight (φ : E → 𝕜 → G) (e : E) (k : 𝕜) :
    ∂₂ 𝕜 φ e k = smulRight (1 : 𝕜 →L[𝕜] 𝕜) (partialDerivSnd φ e k) :=
  deriv_fderiv.symm

theorem partialFDerivSnd_one (φ : E → 𝕜 → G) (e : E) (k : 𝕜) :
    ∂₂ 𝕜 φ e k 1 = partialDerivSnd φ e k := by
  simp only [partialFDerivSnd_eq_smulRight, smul_right_apply, one_apply, one_smul]

@[to_additive]
theorem WithTop.le_mul_self {α : Type _} [CanonicallyOrderedMonoid α] (n m : α) :
    (n : WithTop α) ≤ (m * n : α) :=
  WithTop.coe_le_coe.mpr le_mul_self

@[to_additive]
theorem WithTop.le_self_mul {α : Type _} [CanonicallyOrderedMonoid α] (n m : α) :
    (n : WithTop α) ≤ (n * m : α) :=
  WithTop.coe_le_coe.mpr le_self_mul

theorem ContDiff.contDiff_partial_fst {φ : E → F → G} {n : ℕ}
    (hF : ContDiff 𝕜 (n + 1) (uncurry φ)) : ContDiff 𝕜 n ↿(∂₁ 𝕜 φ) :=
  ContDiff.fderiv (hF.comp <| contDiff_snd.Prod contDiff_fst.snd) contDiff_fst le_rfl

theorem ContDiff.contDiff_partial_fst_apply {φ : E → F → G} {n : ℕ}
    (hF : ContDiff 𝕜 (n + 1) (uncurry φ)) {x : E} : ContDiff 𝕜 n ↿fun x' y => ∂₁ 𝕜 φ x' y x :=
  (ContinuousLinearMap.apply 𝕜 G x).ContDiff.comp hF.contDiff_partial_fst

theorem ContDiff.continuous_partial_fst {φ : E → F → G} {n : ℕ}
    (h : ContDiff 𝕜 ((n + 1 : ℕ) : ℕ∞) <| uncurry φ) : Continuous ↿(∂₁ 𝕜 φ) :=
  h.contDiff_partial_fst.Continuous

theorem ContDiff.contDiff_top_partial_fst {φ : E → F → G} (hF : ContDiff 𝕜 ⊤ (uncurry φ)) :
    ContDiff 𝕜 ⊤ ↿(∂₁ 𝕜 φ) :=
  contDiff_top.mpr fun n => (contDiff_top.mp hF (n + 1)).contDiff_partial_fst

theorem ContDiff.contDiff_partial_snd {φ : E → F → G} {n : ℕ}
    (hF : ContDiff 𝕜 (n + 1) (uncurry φ)) : ContDiff 𝕜 n ↿(∂₂ 𝕜 φ) :=
  ContDiff.fderiv (hF.comp <| contDiff_fst.fst.Prod contDiff_snd) contDiff_snd le_rfl

theorem ContDiff.contDiff_partial_snd_apply {φ : E → F → G} {n : ℕ}
    (hF : ContDiff 𝕜 (n + 1) (uncurry φ)) {y : F} : ContDiff 𝕜 n ↿fun x y' => ∂₂ 𝕜 φ x y' y :=
  (ContinuousLinearMap.apply 𝕜 G y).ContDiff.comp hF.contDiff_partial_snd

theorem ContDiff.continuous_partial_snd {φ : E → F → G} {n : ℕ}
    (h : ContDiff 𝕜 ((n + 1 : ℕ) : ℕ∞) <| uncurry φ) : Continuous ↿(∂₂ 𝕜 φ) :=
  h.contDiff_partial_snd.Continuous

theorem ContDiff.contDiff_top_partial_snd {φ : E → F → G} (hF : ContDiff 𝕜 ⊤ (uncurry φ)) :
    ContDiff 𝕜 ⊤ ↿(∂₂ 𝕜 φ) :=
  contDiff_top.mpr fun n => (contDiff_top.mp hF (n + 1)).contDiff_partial_snd

end Calculus

section RealCalculus

open ContinuousLinearMap

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : Type _} [NormedAddCommGroup F]
  [NormedSpace ℝ F]

theorem ContDiff.lipschitzOnWith {s : Set E} {f : E → F} {n} (hf : ContDiff ℝ n f) (hn : 1 ≤ n)
    (hs : Convex ℝ s) (hs' : IsCompact s) : ∃ K, LipschitzOnWith K f s :=
  by
  rcases(bddAbove_iff_exists_ge 0).mp (hs'.image (hf.continuous_fderiv hn).norm).BddAbove with
    ⟨M, M_nonneg, hM⟩
  simp_rw [ball_image_iff] at hM 
  use ⟨M, M_nonneg⟩
  exact Convex.lipschitzOnWith_of_nnnorm_fderiv_le (fun x x_in => hf.differentiable hn x) hM hs

end RealCalculus

open Filter

theorem const_mul_one_div_lt {ε : ℝ} (ε_pos : 0 < ε) (C : ℝ) : ∀ᶠ N : ℝ in atTop, C * ‖1 / N‖ < ε :=
  have h : Tendsto (fun N : ℝ => C * ‖1 / N‖) atTop (𝓝 (C * ‖(0 : ℝ)‖)) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.div_atTop tendsto_id).norm
  Filter.Tendsto.eventually_lt h tendsto_const_nhds <| by simpa

