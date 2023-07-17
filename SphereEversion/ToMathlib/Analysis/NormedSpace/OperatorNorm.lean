import Mathbin.Analysis.NormedSpace.BoundedLinearMaps
import Mathbin.Analysis.NormedSpace.FiniteDimension

noncomputable section

local notation:70 u " ⬝ " φ:65 =>
  ContinuousLinearMap.comp (ContinuousLinearMap.toSpanSingleton ℝ u) φ

variable {𝕜 E F G Fₗ Gₗ X : Type _} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedAddCommGroup Fₗ] [NormedAddCommGroup Gₗ] [NormedAddCommGroup F] [NormedAddCommGroup G]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜 Fₗ] [NormedSpace 𝕜 Gₗ] [NormedSpace 𝕜 F] [NormedSpace 𝕜 G]
  [TopologicalSpace X]

theorem ContinuousLinearMap.le_op_norm_of_le' {𝕜 : Type _} {𝕜₂ : Type _} {E : Type _} {F : Type _}
    [NormedAddCommGroup E] [SeminormedAddCommGroup F] [NontriviallyNormedField 𝕜]
    [NontriviallyNormedField 𝕜₂] [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] {σ₁₂ : 𝕜 →+* 𝕜₂}
    [RingHomIsometric σ₁₂] (f : E →SL[σ₁₂] F) {x : E} (hx : x ≠ 0) {C : ℝ} (h : C * ‖x‖ ≤ ‖f x‖) :
    C ≤ ‖f‖ := by
  apply le_of_mul_le_mul_right (h.trans (f.le_op_norm x))
  rwa [norm_pos_iff']

@[simp]
theorem ContinuousLinearMap.toSpanSingleton_zero (𝕜 : Type _) {E : Type _}
    [SeminormedAddCommGroup E] [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] :
    ContinuousLinearMap.toSpanSingleton 𝕜 (0 : E) = 0 :=
  by
  ext u
  simp only [ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearMap.zero_apply,
    LinearMap.toSpanSingleton_apply, LinearMap.mkContinuous_apply, smul_zero]

@[simp]
theorem ContinuousLinearMap.comp_toSpanSingleton_apply {E : Type _} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F : Type _} [NormedAddCommGroup F] [NormedSpace ℝ F] (φ : E →L[ℝ] ℝ) (v : E)
    (u : F) : (u ⬝ φ) v = φ v • u :=
  rfl

universe u₁ u₂ u₃ u₄

/-- The natural linear map `(M →ₗ[R] M₃) × (M₂ →ₗ[R] M₃) →ₗ[R] M × M₂ →ₗ[R] M₃` for `R`-modules `M`,
`M₂`, `M₃` over a commutative ring `R`.

If `f : M →ₗ[R] M₃` and `g : M₂ →ₗ[R] M₃` then `linear_map.coprodₗ (f, g)` is the map
`(m, n) ↦ f m + g n`. -/
def LinearMap.coprodₗ (R : Type u₁) (M : Type u₂) (M₂ : Type u₃) (M₃ : Type u₄) [CommRing R]
    [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃] [Module R M] [Module R M₂]
    [Module R M₃] : (M →ₗ[R] M₃) × (M₂ →ₗ[R] M₃) →ₗ[R] M × M₂ →ₗ[R] M₃
    where
  toFun p := p.1.coprod p.2
  map_add' := by
    intro p q
    apply LinearMap.coe_injective
    ext x
    simp only [Prod.fst_add, LinearMap.coprod_apply, LinearMap.add_apply, Prod.snd_add]
    ac_rfl
  map_smul' := by
    intro r p
    apply LinearMap.coe_injective
    ext x
    simp only [Prod.smul_fst, Prod.smul_snd, LinearMap.coprod_apply, LinearMap.smul_apply,
      RingHom.id_apply, smul_add]

theorem add_le_twice_max (a b : ℝ) : a + b ≤ 2 * max a b :=
  calc
    a + b ≤ max a b + max a b := add_le_add (le_max_left a b) (le_max_right a b)
    _ = _ := by ring

theorem isBoundedLinearMap_coprod (𝕜 : Type _) [NontriviallyNormedField 𝕜] (E : Type _)
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (F : Type _) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (G : Type _) [NormedAddCommGroup G] [NormedSpace 𝕜 G] :
    IsBoundedLinearMap 𝕜 fun p : (E →L[𝕜] G) × (F →L[𝕜] G) => p.1.coprod p.2 :=
  { map_add := by
      intros
      apply ContinuousLinearMap.coeFn_injective
      ext u
      simp only [Prod.fst_add, Prod.snd_add, ContinuousLinearMap.coprod_apply,
        ContinuousLinearMap.add_apply]
      ac_rfl
    map_smul := by
      intro r p
      apply ContinuousLinearMap.coeFn_injective
      ext x
      simp only [Prod.smul_fst, Prod.smul_snd, ContinuousLinearMap.coprod_apply,
        ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_add]
    bound := by
      refine' ⟨2, zero_lt_two, _⟩
      rintro ⟨φ, ψ⟩
      apply ContinuousLinearMap.op_norm_le_bound
      exact mul_nonneg zero_le_two (norm_nonneg _)
      rintro ⟨e, f⟩
      calc
        ‖φ e + ψ f‖ ≤ ‖φ e‖ + ‖ψ f‖ := norm_add_le _ _
        _ ≤ ‖φ‖ * ‖e‖ + ‖ψ‖ * ‖f‖ := (add_le_add (φ.le_op_norm e) (ψ.le_op_norm f))
        _ ≤ max ‖φ‖ ‖ψ‖ * ‖e‖ + max ‖φ‖ ‖ψ‖ * ‖f‖ := _
        _ ≤ 2 * max ‖φ‖ ‖ψ‖ * max ‖e‖ ‖f‖ := _
      apply add_le_add
      exact mul_le_mul_of_nonneg_right (le_max_left ‖φ‖ ‖ψ‖) (norm_nonneg e)
      exact mul_le_mul_of_nonneg_right (le_max_right ‖φ‖ ‖ψ‖) (norm_nonneg f)
      rw [← mul_add, mul_comm (2 : ℝ), mul_assoc]
      apply mul_le_mul_of_nonneg_left (add_le_twice_max _ _) (le_max_of_le_left <| norm_nonneg _) }

/-- The natural continuous linear map `((E →L[𝕜] G) × (F →L[𝕜] G)) →L[𝕜] (E × F →L[𝕜] G)` for
normed spaces `E`, `F`, `G` over a normed field `𝕜`.

If `g₁ : E →L[𝕜] G` and `g₂ : F →L[𝕜] G` then `continuous_linear_map.coprodL (g₁, g₂)` is the map
`(e, f) ↦ g₁ e + g₂ f`. -/
def ContinuousLinearMap.coprodL : (E →L[𝕜] G) × (F →L[𝕜] G) →L[𝕜] E × F →L[𝕜] G :=
  (isBoundedLinearMap_coprod 𝕜 E F G).toContinuousLinearMap

@[continuity]
theorem Continuous.coprodL {f : X → E →L[𝕜] G} {g : X → F →L[𝕜] G} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun x => (f x).coprod (g x) :=
  ContinuousLinearMap.coprodL.Continuous.comp₂ hf hg

theorem Continuous.prodL' {𝕜 : Type _} {E : Type _} {Fₗ : Type _} {Gₗ : Type _}
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup Fₗ] [SeminormedAddCommGroup Gₗ]
    [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [NormedSpace 𝕜 Fₗ] [NormedSpace 𝕜 Gₗ] (R : Type _)
    [Semiring R] [Module R Fₗ] [Module R Gₗ] [ContinuousConstSMul R Fₗ] [ContinuousConstSMul R Gₗ]
    [SMulCommClass 𝕜 R Fₗ] [SMulCommClass 𝕜 R Gₗ] {X : Type _} [TopologicalSpace X]
    {f : X → E →L[𝕜] Fₗ} {g : X → E →L[𝕜] Gₗ} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => (f x).Prod (g x) :=
  (ContinuousLinearMap.prodₗᵢ 𝕜).Continuous.comp₂ hf hg

@[continuity]
theorem Continuous.prodL {𝕜 : Type _} {E : Type _} {Fₗ : Type _} {Gₗ : Type _}
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup Fₗ] [SeminormedAddCommGroup Gₗ]
    [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [NormedSpace 𝕜 Fₗ] [NormedSpace 𝕜 Gₗ] {X : Type _}
    [TopologicalSpace X] {f : X → E →L[𝕜] Fₗ} {g : X → E →L[𝕜] Gₗ} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun x => (f x).Prod (g x) :=
  hf.prodL' 𝕜 hg

@[continuity]
theorem Continuous.compL {f : X → Fₗ →L[𝕜] Gₗ} {g : X → E →L[𝕜] Fₗ} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun x => (f x).comp (g x) :=
  (ContinuousLinearMap.apply 𝕜 (E →L[𝕜] Gₗ) :
              (E →L[𝕜] Fₗ) →L[𝕜]
                ((E →L[𝕜] Fₗ) →L[𝕜] E →L[𝕜] Gₗ) →L[𝕜]
                  E →L[𝕜] Gₗ).IsBoundedBilinearMap.Continuous.comp₂
      hg <|
    (ContinuousLinearMap.compL 𝕜 E Fₗ Gₗ).Continuous.comp hf

@[continuity]
theorem ContinuousAt.compL {f : X → Fₗ →L[𝕜] Gₗ} {g : X → E →L[𝕜] Fₗ} {x₀ : X}
    (hf : ContinuousAt f x₀) (hg : ContinuousAt g x₀) :
    ContinuousAt (fun x => (f x).comp (g x)) x₀ :=
  by
  have cont₁ := (ContinuousLinearMap.compL 𝕜 E Fₗ Gₗ).Continuous.ContinuousAt.comp hf
  have cont₂ :=
    (ContinuousLinearMap.apply 𝕜 (E →L[𝕜] Gₗ) :
          (E →L[𝕜] Fₗ) →L[𝕜]
            ((E →L[𝕜] Fₗ) →L[𝕜] E →L[𝕜] Gₗ) →L[𝕜] E →L[𝕜] Gₗ).IsBoundedBilinearMap.Continuous
  exact cont₂.continuous_at.comp (hg.prod cont₁)

section FiniteDimensional

open Function FiniteDimensional

variable [FiniteDimensional 𝕜 E]

theorem ContinuousLinearMap.inj_iff_antilip [CompleteSpace 𝕜] (φ : E →L[𝕜] F) :
    Injective φ ↔ ∃ K > 0, AntilipschitzWith K φ :=
  by
  change injective φ.to_linear_map ↔ _
  constructor
  · rw [← LinearMap.ker_eq_bot]
    exact φ.exists_antilipschitz_with
  · rintro ⟨K, K_pos, H⟩
    exact H.injective

open scoped Topology NNReal

theorem eventually_nnorm_sub_lt (x₀ : E) {ε : ℝ≥0} {ε_pos : 0 < ε} : ∀ᶠ x in 𝓝 x₀, ‖x - x₀‖₊ < ε :=
  by
  rw [metric.nhds_basis_ball.eventually_iff]
  use ε, ε_pos
  simp [dist_eq_norm]
  exact fun x => id

theorem eventually_norm_sub_lt (x₀ : E) {ε : ℝ} {ε_pos : 0 < ε} : ∀ᶠ x in 𝓝 x₀, ‖x - x₀‖ < ε :=
  by
  rw [metric.nhds_basis_ball.eventually_iff]
  use ε, ε_pos
  simp [dist_eq_norm]

theorem ContinuousLinearMap.isOpen_injective [CompleteSpace 𝕜] :
    IsOpen {L : E →L[𝕜] F | Injective L} :=
  by
  rw [isOpen_iff_eventually]
  rintro φ₀ (hφ₀ : injective φ₀)
  rcases φ₀.inj_iff_antilip.mp hφ₀ with ⟨K, K_pos, H⟩
  have : ∀ᶠ φ in 𝓝 φ₀, ‖φ - φ₀‖₊ < K⁻¹ :=
    by
    apply eventually_nnorm_sub_lt
    apply inv_pos_of_pos K_pos
  apply this.mono; dsimp only [Set.mem_setOf_eq]
  intro φ hφ
  apply φ.inj_iff_antilip.mpr
  refine' ⟨(K⁻¹ - ‖φ - φ₀‖₊)⁻¹, inv_pos_of_pos (tsub_pos_of_lt hφ), _⟩
  exact AntilipschitzWith.add_sub_lipschitzWith H (φ - φ₀).lipschitz hφ

end FiniteDimensional

