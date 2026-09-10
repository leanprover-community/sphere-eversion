module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Analysis.Normed.Operator.Prod

@[expose] public section

noncomputable section

@[inherit_doc] local notation:70 u " ⬝ " φ:65 =>
  ContinuousLinearMap.comp (ContinuousLinearMap.toSpanSingleton ℝ u) φ

variable {𝕜 E F G Fₗ Gₗ X : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedAddCommGroup Fₗ] [NormedAddCommGroup Gₗ] [NormedAddCommGroup F] [NormedAddCommGroup G]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜 Fₗ] [NormedSpace 𝕜 Gₗ] [NormedSpace 𝕜 F] [NormedSpace 𝕜 G]
  [TopologicalSpace X]

theorem ContinuousLinearMap.le_opNorm_of_le' {𝕜 : Type*} {𝕜₂ : Type*} {E : Type*} {F : Type*}
    [NormedAddCommGroup E] [SeminormedAddCommGroup F] [NontriviallyNormedField 𝕜]
    [NontriviallyNormedField 𝕜₂] [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] {σ₁₂ : 𝕜 →+* 𝕜₂}
    [RingHomIsometric σ₁₂] (f : E →SL[σ₁₂] F) {x : E} (hx : x ≠ 0) {C : ℝ} (h : C * ‖x‖ ≤ ‖f x‖) :
    C ≤ ‖f‖ := by
  apply le_of_mul_le_mul_right (h.trans (f.le_opNorm x))
  rwa [norm_pos_iff]

@[simp]
theorem ContinuousLinearMap.comp_toSpanSingleton_apply {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (φ : E →L[ℝ] ℝ) (v : E)
    (u : F) : (u ⬝ φ) v = φ v • u :=
  rfl

universe u₁ u₂ u₃ u₄

/-- The natural linear map `(M →ₗ[R] M₃) × (M₂ →ₗ[R] M₃) →ₗ[R] M × M₂ →ₗ[R] M₃` for `R`-modules `M`,
`M₂`, `M₃` over a commutative ring `R`.

If `f : M →ₗ[R] M₃` and `g : M₂ →ₗ[R] M₃` then `linear_map.coprodₗ (f, g)` is the map
`(m, n) ↦ f m + g n`. -/
def LinearMap.coprodₗ (R : Type u₁) (M : Type u₂) (M₂ : Type u₃) (M₃ : Type u₄) [CommRing R]
    [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃] [Module R M] [Module R M₂]
    [Module R M₃] : (M →ₗ[R] M₃) × (M₂ →ₗ[R] M₃) →ₗ[R] M × M₂ →ₗ[R] M₃ where
  toFun p := p.1.coprod p.2
  map_add' p q := by
    apply LinearMap.coe_injective
    ext x
    simp only [Prod.fst_add, LinearMap.coprod_apply, LinearMap.add_apply, Prod.snd_add]
    module
  map_smul' r p := by
    apply LinearMap.coe_injective
    ext x
    simp only [Prod.smul_fst, Prod.smul_snd, LinearMap.coprod_apply, LinearMap.smul_apply,
      RingHom.id_apply, smul_add]

theorem isBoundedLinearMap_coprod (𝕜 : Type*) [NontriviallyNormedField 𝕜] (E : Type*)
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (G : Type*) [NormedAddCommGroup G] [NormedSpace 𝕜 G] :
    IsBoundedLinearMap 𝕜 fun p : (E →L[𝕜] G) × (F →L[𝕜] G) ↦ p.1.coprod p.2 :=
  { map_add := by
      intros
      apply ContinuousLinearMap.coeFn_injective
      ext u
      simp only [Prod.fst_add, Prod.snd_add, ContinuousLinearMap.coprod_apply, add_apply]
      ac_rfl
    map_smul := by
      intro r p
      apply ContinuousLinearMap.coeFn_injective
      ext x
      simp
    bound := by
      refine ⟨2, zero_lt_two, fun ⟨φ, ψ⟩ ↦ ?_⟩
      apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
      rintro ⟨e, f⟩
      calc
        ‖φ e + ψ f‖ ≤ ‖φ e‖ + ‖ψ f‖ := norm_add_le _ _
        _ ≤ ‖φ‖ * ‖e‖ + ‖ψ‖ * ‖f‖ := (add_le_add (φ.le_opNorm e) (ψ.le_opNorm f))
        _ ≤ 2 * max ‖φ‖ ‖ψ‖ * max ‖e‖ ‖f‖ := by
          rw [two_mul, add_mul]
          gcongr <;> first | apply le_max_left | apply le_max_right }

/-- The natural continuous linear map `((E →L[𝕜] G) × (F →L[𝕜] G)) →L[𝕜] (E × F →L[𝕜] G)` for
normed spaces `E`, `F`, `G` over a normed field `𝕜`.

If `g₁ : E →L[𝕜] G` and `g₂ : F →L[𝕜] G` then `continuous_linear_map.coprodL (g₁, g₂)` is the map
`(e, f) ↦ g₁ e + g₂ f`. -/
def ContinuousLinearMap.coprodL : (E →L[𝕜] G) × (F →L[𝕜] G) →L[𝕜] E × F →L[𝕜] G :=
  (isBoundedLinearMap_coprod 𝕜 E F G).toContinuousLinearMap

@[continuity, fun_prop]
theorem Continuous.coprodL {f : X → E →L[𝕜] G} {g : X → F →L[𝕜] G} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun x ↦ (f x).coprod (g x) :=
  ContinuousLinearMap.coprodL.continuous.comp₂ hf hg

theorem Continuous.prodL' {𝕜 : Type*} {E : Type*} {Fₗ : Type*} {Gₗ : Type*}
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup Fₗ] [SeminormedAddCommGroup Gₗ]
    [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [NormedSpace 𝕜 Fₗ] [NormedSpace 𝕜 Gₗ]
    {X : Type*} [TopologicalSpace X]
    {f : X → E →L[𝕜] Fₗ} {g : X → E →L[𝕜] Gₗ} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x ↦ (f x).prod (g x) :=
  (ContinuousLinearMap.prodₗᵢ 𝕜).continuous.comp₂ hf hg

@[continuity, fun_prop]
theorem Continuous.prodL {𝕜 : Type*} {E : Type*} {Fₗ : Type*} {Gₗ : Type*}
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup Fₗ] [SeminormedAddCommGroup Gₗ]
    [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [NormedSpace 𝕜 Fₗ] [NormedSpace 𝕜 Gₗ] {X : Type*}
    [TopologicalSpace X] {f : X → E →L[𝕜] Fₗ} {g : X → E →L[𝕜] Gₗ} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun x ↦ (f x).prod (g x) :=
  hf.prodL' hg

@[continuity, fun_prop]
theorem ContinuousAt.compL {f : X → Fₗ →L[𝕜] Gₗ} {g : X → E →L[𝕜] Fₗ} {x₀ : X}
    (hf : ContinuousAt f x₀) (hg : ContinuousAt g x₀) :
    ContinuousAt (fun x ↦ (f x).comp (g x)) x₀ :=
  ((ContinuousLinearMap.compL 𝕜 E Fₗ Gₗ).continuous₂.tendsto (f x₀, g x₀)).comp
    (hf.prodMk_nhds hg)

@[continuity, fun_prop]
theorem Continuous.compL {f : X → Fₗ →L[𝕜] Gₗ} {g : X → E →L[𝕜] Fₗ} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun x ↦ (f x).comp (g x) :=
  (ContinuousLinearMap.compL 𝕜 E Fₗ Gₗ).continuous₂.comp₂ hf hg
