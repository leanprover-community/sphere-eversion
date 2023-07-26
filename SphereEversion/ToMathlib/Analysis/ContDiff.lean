import Mathlib.Analysis.Calculus.Inverse
import Mathlib.Analysis.Calculus.ContDiff
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Dual
import SphereEversion.ToMathlib.Analysis.Calculus
import SphereEversion.ToMathlib.Analysis.NormedSpace.OperatorNorm

noncomputable section

open scoped Topology Filter

open Function

section

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {F : Type _}
  [NormedAddCommGroup F] [NormedSpace ℝ F]

-- Not used here, but should be in mathlib
theorem hasFDerivAt_of_not_mem (𝕜 : Type _) {E : Type _} {F : Type _} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : E → F}
    {x} (hx : x ∉ tsupport f) : HasFDerivAt f (0 : E →L[𝕜] F) x :=
  (hasFDerivAt_const (0 : F) x).congr_of_eventuallyEq (not_mem_tsupport_iff_eventuallyEq.mp hx)

-- Not used here, but should be in mathlib
theorem contDiffAt_of_not_mem (𝕜 : Type _) {E : Type _} {F : Type _} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : E → F}
    {x} (hx : x ∉ tsupport f) (n : ℕ∞) : ContDiffAt 𝕜 n f x :=
  (contDiffAt_const : ContDiffAt 𝕜 n (fun x => (0 : F)) x).congr_of_eventuallyEq
    (not_mem_tsupport_iff_eventuallyEq.mp hx)

end

section

universe u₁ u₂ u₃ u₄ u₅

open ContinuousLinearMap

variable {𝕜 : Type u₁} [NontriviallyNormedField 𝕜] {M₁ : Type u₂} [NormedAddCommGroup M₁]
  [NormedSpace 𝕜 M₁] {M₂ : Type u₃} [NormedAddCommGroup M₂] [NormedSpace 𝕜 M₂] {M₃ : Type u₄}
  [NormedAddCommGroup M₃] [NormedSpace 𝕜 M₃] {M₄ : Type u₅} [NormedAddCommGroup M₄]
  [NormedSpace 𝕜 M₄]

-- The next definition won't be used here, it's practice before the next one.
/-- Defines continuous linear maps between two products by blocks:
given `(A : M₁ →L[𝕜] M₃)`, `(B : M₂ →L[𝕜] M₃)`, `(C : M₁ →L[𝕜] M₄)` and `(D : M₂ →L[𝕜] M₄)`,
construct the continuous linear map with "matrix":
A B
C D. -/
def ContinuousLinearMap.blocks (A : M₁ →L[𝕜] M₃) (B : M₂ →L[𝕜] M₃) (C : M₁ →L[𝕜] M₄)
    (D : M₂ →L[𝕜] M₄) : M₁ × M₂ →L[𝕜] M₃ × M₄ :=
  (A.coprod B).prod (C.coprod D)

/-- Given `(A : M₁ ≃L[𝕜] M₃)`, `(C : M₁ →L[𝕜] M₄)` and `(D : M₂ ≃L[𝕜] M₄)`,
construct the continuous linear equiv with "matrix"
A 0
C D.
  -/
def ContinuousLinearEquiv.lowerTriangular (A : M₁ ≃L[𝕜] M₃) (C : M₁ →L[𝕜] M₄) (D : M₂ ≃L[𝕜] M₄) :
    (M₁ × M₂) ≃L[𝕜] M₃ × M₄ :=
  ContinuousLinearEquiv.equivOfInverse (((A : M₁ →L[𝕜] M₃).comp (fst 𝕜 M₁ M₂)).prod (C.coprod D))
    (((A.symm : M₃ →L[𝕜] M₁).comp (fst 𝕜 M₃ M₄)).prod
      ((-((D.symm : M₄ →L[𝕜] M₂).comp C).comp (A.symm : M₃ →L[𝕜] M₁)).coprod D.symm))
    (fun ⟨x, y⟩ => by
      simp only [prod_apply, coe_comp', ContinuousLinearEquiv.coe_coe, coe_fst', comp_app,
        coprod_apply, ContinuousLinearEquiv.symm_apply_apply, neg_apply,
        ContinuousLinearEquiv.map_add, neg_add_cancel_left])
    fun ⟨x, y⟩ => by
    simp only [prod_apply, coe_comp', ContinuousLinearEquiv.coe_coe, coe_fst', comp_app,
      coprod_apply, neg_apply, ContinuousLinearEquiv.apply_symm_apply,
      ContinuousLinearEquiv.map_add, ContinuousLinearEquiv.map_neg, add_neg_cancel_left]

theorem ContinuousLinearEquiv.continuous_lowerTriangular {X : Type _} [TopologicalSpace X]
    {A : X → M₁ ≃L[𝕜] M₃} {C : X → M₁ →L[𝕜] M₄} {D : X → M₂ ≃L[𝕜] M₄}
    (hA : Continuous fun x => (A x : M₁ →L[𝕜] M₃)) (hC : Continuous C)
    (hD : Continuous fun x => (D x : M₂ →L[𝕜] M₄)) :
    Continuous fun x => ((A x).lowerTriangular (C x) (D x) : M₁ × M₂ →L[𝕜] M₃ × M₄) :=
  (hA.compL continuous_const).prodL (hC.coprodL hD)

end

section

variable (𝕜 : Type _) [NontriviallyNormedField 𝕜] {E : Type _} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type _} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type _}
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] {n : ℕ∞}

-- The next two definitions aren't used in the end, but they may still go to mathlib
/-- The proposition that a function between two normed spaces has a strict derivative at a given
point. -/
def StrictDifferentiableAt (f : E → F) (x) :=
  ∃ φ : E →L[𝕜] F, HasStrictFDerivAt f φ x

/-- The proposition that a function between two normed spaces has a strict derivative at every
point. -/
def StrictDifferentiable (f : E → F) :=
  ∀ x, StrictDifferentiableAt 𝕜 f x

variable {𝕜}

theorem StrictDifferentiableAt.differentiableAt {f : E → F} {x : E}
    (h : StrictDifferentiableAt 𝕜 f x) : DifferentiableAt 𝕜 f x :=
  Exists.elim h fun φ hφ => ⟨φ, hφ.hasFDerivAt⟩

-- PR to linear_algebra.prod
@[simp]
theorem LinearMap.coprod_comp_inl_inr {R : Type _} {M : Type _} {M₂ : Type _} {M₃ : Type _}
    [Semiring R] [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃] [Module R M] [Module R M₂]
    [Module R M₃] (f : M × M₂ →ₗ[R] M₃) :
    (f.comp (LinearMap.inl R M M₂)).coprod (f.comp (LinearMap.inr R M M₂)) = f := by
  rw [← LinearMap.comp_coprod, LinearMap.coprod_inl_inr, LinearMap.comp_id]

-- PR to topology.algebra.module.basic
@[simp]
theorem ContinuousLinearMap.coprod_comp_inl_inr {R₁ : Type _} [Semiring R₁] {M₁ : Type _}
    [TopologicalSpace M₁] [AddCommMonoid M₁] {M₂ : Type _} [TopologicalSpace M₂] [AddCommMonoid M₂]
    {M₃ : Type _} [TopologicalSpace M₃] [AddCommMonoid M₃] [Module R₁ M₁] [Module R₁ M₂]
    [Module R₁ M₃] [ContinuousAdd M₃] (f : M₁ × M₂ →L[R₁] M₃) :
    (f.comp (ContinuousLinearMap.inl R₁ M₁ M₂)).coprod (f.comp (ContinuousLinearMap.inr R₁ M₁ M₂)) =
      f :=
  ContinuousLinearMap.coe_injective (f : M₁ × M₂ →ₗ[R₁] M₃).coprod_comp_inl_inr

theorem DifferentiableAt.hasFDerivAt_coprod_partial {f : E → F → G} {x : E} {y : F}
    (hf : DifferentiableAt 𝕜 (uncurry f) (x, y)) :
    HasFDerivAt (uncurry f) ((partialFDerivFst 𝕜 f x y).coprod (partialFDerivSnd 𝕜 f x y)) (x, y) :=
  by
  rcases hf with ⟨θ, hθ⟩
  rwa [fderiv_partial_fst hθ, fderiv_partial_snd hθ, θ.coprod_comp_inl_inr]

theorem DifferentiableAt.hasFDerivAt_coprod {f : E → F → G} {x : E} {y : F}
    (hf : DifferentiableAt 𝕜 (uncurry f) (x, y)) {φ : E →L[𝕜] G} {ψ : F →L[𝕜] G}
    (hφ : HasFDerivAt (fun p => f p y) φ x) (hψ : HasFDerivAt (f x) ψ y) :
    HasFDerivAt (uncurry f) (φ.coprod ψ) (x, y) :=
  by
  rw [hφ.unique hf.has_fderiv_at_partial_fst, hψ.unique hf.has_fderiv_at_partial_snd]
  exact hf.has_fderiv_at_coprod_partial

variable [CompleteSpace E]

theorem Homeomorph.contDiffAt_symm (f : Homeomorph E F) {f₀' : E ≃L[𝕜] F} {a : F}
    (hf' : HasFDerivAt f (f₀' : E →L[𝕜] F) (f.symm a)) (hf : ContDiffAt 𝕜 n f (f.symm a)) :
    ContDiffAt 𝕜 n f.symm a :=
  f.toLocalHomeomorph.contDiffAt_symm trivial hf' hf

theorem Equiv.continuous_symm_of_contDiff (φ : E ≃ F) {Dφ : E → E ≃L[𝕜] F}
    (hφ : ∀ x, HasStrictFDerivAt φ (Dφ x : E →L[𝕜] F) x) : Continuous φ.symm :=
  by
  rw [continuous_iff_continuousAt]
  intro x
  let y := φ.symm x
  let g := (hφ y).localInverse φ (Dφ y) y
  rw [← φ.apply_symm_apply x]
  have ev_eq : g =ᶠ[𝓝 (φ y)] φ.symm :=
    by
    apply (hφ y).eventually_right_inverse.mono
    rintro x (hx : φ (g x) = x)
    exact (Equiv.eq_symm_apply φ).mpr hx
  apply ContinuousAt.congr _ ev_eq
  apply (hφ y).localInverse_continuousAt

/-- A bijection that is strictly differentiable at every point is a homeomorphism. -/
def Equiv.toHomeomorphOfContDiff (φ : E ≃ F) {Dφ : E → E ≃L[𝕜] F}
    (hφ : ∀ x, HasStrictFDerivAt φ (Dφ x : E →L[𝕜] F) x) : E ≃ₜ F :=
  { φ with
    continuous_toFun := Differentiable.continuous fun x => (hφ x).differentiableAt
    continuous_invFun := φ.continuous_symm_of_contDiff hφ }

end

section

variable {𝕜 : Type _} [IsROrC 𝕜] {E : Type _} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {F : Type _}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type _} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {n : ℕ∞}

local notation "∂₁" => partialFDerivFst 𝕜

local notation "∂₂" => partialFDerivSnd 𝕜

theorem contDiff_parametric_symm [CompleteSpace E] [CompleteSpace F] {f : E → F ≃ G}
    {f' : E → F → F ≃L[𝕜] G} (hf : ContDiff 𝕜 ⊤ fun p : E × F => f p.1 p.2)
    (hf' : ∀ x y, ∂₂ (fun x y => f x y) x y = f' x y) :
    ContDiff 𝕜 ⊤ fun p : E × G => (f p.1).symm p.2 :=
  by
  let φ₀ : E × F ≃ E × G :=
    { toFun := fun p : E × F => (p.1, f p.1 p.2)
      invFun := fun p : E × G => (p.1, (f p.1).symm p.2)
      left_inv := fun x => by simp
      right_inv := fun x => by simp }
  let ff x y := f x y
  have hff : ContDiff 𝕜 ⊤ (uncurry ff) := hf
  let d₁f := ∂₁ ff
  let Dφ : E × F → (E × F) ≃L[𝕜] E × G := fun x =>
    (ContinuousLinearEquiv.refl 𝕜 E).lowerTriangular (d₁f x.1 x.2) (f' x.1 x.2)
  let Dφ' : E × F → E × F →L[𝕜] E × G := fun x => Dφ x
  have hderiv : ∀ x : E × F, HasStrictFDerivAt φ₀ (Dφ' x) x :=
    by
    rintro p
    apply hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt
    · apply Filter.eventually_of_forall
      rintro ⟨x, y⟩
      apply HasFDerivAt.prod
      · simp only [ContinuousLinearEquiv.coe_refl, ContinuousLinearMap.id_comp, hasFDerivAt_fst]
      have diff : Differentiable 𝕜 (uncurry fun x y => f x y) := hf.differentiable le_top
      rw [show (fun x : E × F => (f x.fst) x.snd) = uncurry fun x y => f x y by ext; rfl]
      apply DifferentiableAt.hasFDerivAt_coprod
      · apply hf.differentiable le_top
      · dsimp [d₁f]
        exact diff.differentiable_at.has_fderiv_at_partial_fst
      · rw [← hf' x y]
        dsimp
        exact diff.differentiable_at.has_fderiv_at_partial_snd
    · apply Continuous.continuousAt
      apply ContinuousLinearEquiv.continuous_lowerTriangular
      · exact continuous_const
      · exact hff.contDiff_top_partial_fst.continuous
      · simp_rw [← hf']
        exact hff.contDiff_top_partial_snd.continuous
  let φ := φ₀.to_homeomorph_of_contDiff hderiv
  exact
    contDiff_snd.comp (φ.contDiff_symm (fun x => (hderiv x).hasFDerivAt) (contDiff_fst.prod hf))

end

section

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem contDiff_parametric_symm_of_deriv_pos {f : E → ℝ → ℝ} (hf : ContDiff ℝ ⊤ ↿f)
    (hderiv : ∀ x t, 0 < partialDerivSnd f x t) (hsurj : ∀ x, Surjective <| f x) :
    ContDiff ℝ ⊤ fun p : E × ℝ =>
      (StrictMono.orderIsoOfSurjective (f p.1) (strictMono_of_deriv_pos <| hderiv p.1)
            (hsurj p.1)).symm
        p.2 :=
  by
  have hmono := fun x => strictMono_of_deriv_pos (hderiv x)
  let F x := (StrictMono.orderIsoOfSurjective (f x) (hmono x) <| hsurj x).toEquiv
  change ContDiff ℝ ⊤ fun p : E × ℝ => (F p.1).symm p.snd
  refine' contDiff_parametric_symm hf _
  exact fun x t =>
    ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 (deriv (f x) t) <| ne_of_gt (hderiv x t))
  intro x t
  suffices partialFDerivSnd ℝ f x t 1 = partialDerivSnd f x t
    by
    ext v
    simpa only [RelIso.coe_fn_toEquiv, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.unitsEquivAut_apply, Units.val_mk0, one_mul]
  apply partialFDerivSnd_one

end

section

variable (𝕜 : Type _) [NontriviallyNormedField 𝕜]

theorem contDiff_toSpanSingleton (E : Type _) [NormedAddCommGroup E] [NormedSpace 𝕜 E] :
    ContDiff 𝕜 ⊤ (ContinuousLinearMap.toSpanSingleton 𝕜 : E → 𝕜 →L[𝕜] E) :=
  (ContinuousLinearMap.lsmul 𝕜 𝕜 : 𝕜 →L[𝕜] E →L[𝕜] E).flip.contDiff

end

section

variable {𝕜 : Type _} [IsROrC 𝕜]

variable {E : Type _} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

-- variant of `orthogonal_projection_singleton`
theorem orthogonalProjection_singleton' {v : E} :
    (𝕜 ∙ v).subtypeL.comp (orthogonalProjection (𝕜 ∙ v)) =
      (1 / ‖v‖ ^ 2 : 𝕜) •
        ContinuousLinearMap.toSpanSingleton 𝕜 v ∘L InnerProductSpace.toDual 𝕜 E v :=
  by
  ext w
  simp [ContinuousLinearMap.toSpanSingleton_apply, orthogonalProjection_singleton, ← mul_smul]
  congr 1
  field_simp

end

section

variable {E : Type _} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The orthogonal projection onto a vector in a real inner product space `E`, considered as a map
from `E` to `E →L[ℝ] E`, is smooth away from 0. -/
theorem contDiffAt_orthogonalProjection_singleton {v₀ : E} (hv₀ : v₀ ≠ 0) :
    ContDiffAt ℝ ⊤ (fun v : E => (ℝ ∙ v).subtypeL.comp (orthogonalProjection (ℝ ∙ v))) v₀ :=
  by
  suffices
    ContDiffAt ℝ ⊤
      (fun v : E =>
        (1 / ‖v‖ ^ 2) • ContinuousLinearMap.toSpanSingleton ℝ v ∘L InnerProductSpace.toDual ℝ E v)
      v₀
    by
    refine' this.congr_of_eventually_eq _
    refine' Filter.eventually_of_forall fun v => _
    dsimp
    rw [orthogonalProjection_singleton']
    rfl
  refine' ContDiffAt.smul _ _
  · refine' contDiffAt_const.div (contDiff_norm_sq ℝ).contDiffAt _
    apply pow_ne_zero
    exact norm_ne_zero_iff.mpr hv₀
  exact
    (ContDiff.clm_comp (contDiff_toSpanSingleton ℝ E)
        (InnerProductSpace.toDual ℝ E).contDiff).contDiffAt

end

section Arithmetic

variable {𝕜 : Type _} [NontriviallyNormedField 𝕜] {E : Type _} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {𝔸 : Type _} [NormedRing 𝔸] [NormedAlgebra 𝕜 𝔸] {n : ℕ∞} {f : E → 𝔸} {s : Set E}
  {x : E}

theorem ContDiffWithinAt.mul_const (hf : ContDiffWithinAt 𝕜 n f s x) {c : 𝔸} :
    ContDiffWithinAt 𝕜 n (fun x : E => f x * c) s x :=
  hf.mul contDiffWithinAt_const

theorem ContDiffAt.mul_const (hf : ContDiffAt 𝕜 n f x) {c : 𝔸} :
    ContDiffAt 𝕜 n (fun x : E => f x * c) x :=
  hf.mul contDiffAt_const

theorem ContDiffOn.mul_const (hf : ContDiffOn 𝕜 n f s) {c : 𝔸} :
    ContDiffOn 𝕜 n (fun x : E => f x * c) s :=
  hf.mul contDiffOn_const

theorem ContDiff.mul_const (hf : ContDiff 𝕜 n f) {c : 𝔸} : ContDiff 𝕜 n fun x : E => f x * c :=
  hf.mul contDiff_const

end Arithmetic

section

open scoped BigOperators

variable {𝕜 : Type _} [NontriviallyNormedField 𝕜] {E : Type _} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type _} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem contDiffWithinAt_finsum {ι : Type _} {f : ι → E → F}
    (lf : LocallyFinite fun i => support <| f i) {n : ℕ∞} {s : Set E} {x₀ : E}
    (h : ∀ i, ContDiffWithinAt 𝕜 n (f i) s x₀) : ContDiffWithinAt 𝕜 n (fun x => ∑ᶠ i, f i x) s x₀ :=
  let ⟨I, hI⟩ := finsum_eventually_eq_sum lf x₀
  ContDiffWithinAt.congr_of_eventuallyEq (ContDiffWithinAt.sum fun i hi => h i)
    (eventually_nhdsWithin_of_eventually_nhds hI) hI.self_of_nhds

theorem contDiffAt_finsum {ι : Type _} {f : ι → E → F} (lf : LocallyFinite fun i => support <| f i)
    {n : ℕ∞} {x₀ : E} (h : ∀ i, ContDiffAt 𝕜 n (f i) x₀) :
    ContDiffAt 𝕜 n (fun x => ∑ᶠ i, f i x) x₀ :=
  contDiffWithinAt_finsum lf h

end

