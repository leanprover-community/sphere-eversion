import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

noncomputable section

open scoped RealInnerProductSpace Topology

open Submodule Function Set Filter

section GeneralStuff

-- Things in this section go to other files
@[simp]
theorem forall_mem_span_singleton {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (P : M → Prop) (u : M) : (∀ x ∈ span R ({u} : Set M), P x) ↔ ∀ t : R, P (t • u) := by
  simp [mem_span_singleton]

open scoped Pointwise

@[simp]
theorem Field.exists_unit {𝕜 : Type*} [Field 𝕜] (P : 𝕜 → Prop) :
    (∃ u : 𝕜ˣ, P u) ↔ ∃ u : 𝕜, u ≠ 0 ∧ P u := by
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u, u.ne_zero, hu⟩
  · rintro ⟨u, u_ne, hu⟩
    exact ⟨Units.mk0 u u_ne, hu⟩

theorem span_singleton_eq_span_singleton_of_ne {𝕜 : Type*} [Field 𝕜] {M : Type*} [AddCommGroup M]
    [Module 𝕜 M] {u v : M} (hu : u ≠ 0) (hu' : u ∈ span 𝕜 ({v} : Set M)) :
    span 𝕜 ({u} : Set M) = span 𝕜 ({v} : Set M) := by
  rcases mem_span_singleton.mp hu' with ⟨a, rfl⟩
  by_cases hv : v = 0
  · subst hv
    simp
  have : a ≠ 0 := by
    rintro rfl
    exact hu (zero_smul 𝕜 v)
  symm
  erw [Submodule.span_singleton_eq_span_singleton, Field.exists_unit fun z : 𝕜 ↦ z • v = a • v]
  use a, this

end GeneralStuff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] --[CompleteSpace E]

/-- The line (one-dimensional submodule of `E`) spanned by `x : E`. -/
@[reducible] def spanLine (x : E) : Submodule ℝ E := Submodule.span ℝ ({x} : Set E)

@[inherit_doc] local notation "Δ" => spanLine

/-- The orthogonal complement of the line spanned by `x : E`. -/
@[reducible] def spanOrthogonal (x : E) : Submodule ℝ E := (Δ x)ᗮ

/-- The orthogonal projection to the complement of `span x`. -/
@[reducible] def projSpanOrthogonal (x : E) :=
  orthogonalProjectionOnto (Submodule.span ℝ ({x} : Set E))ᗮ

@[inherit_doc] local notation "{." x "}ᗮ" => spanOrthogonal x

@[inherit_doc] local notation "pr[" x "]ᗮ" => projSpanOrthogonal x

variable (u v : E)

theorem orthogonal_line_inf {u v : E} : {.u}ᗮ ⊓ {.v}ᗮ = {.(pr[v]ᗮ u : E)}ᗮ ⊓ {.v}ᗮ := by
  rw [inf_orthogonal, inf_orthogonal]
  refine congr_arg _ (le_antisymm (sup_le ?_ le_sup_right) (sup_le ?_ le_sup_right)) <;>
    rw [span_singleton_le_iff_mem]
  · nth_rw 2 [← starProjection_add_starProjection_orthogonal (K := Δ v) u]
    exact add_mem (mem_sup_right <| coe_mem _) (mem_sup_left <| mem_span_singleton_self _)
  · rw [projSpanOrthogonal, orthogonalProjectionOnto_orthogonal]
    exact sub_mem (mem_sup_left <| mem_span_singleton_self _) (mem_sup_right <| coe_mem _)

theorem orthogonal_line_inf_sup_line (u v : E) : {.u}ᗮ ⊓ {.v}ᗮ ⊔ Δ (pr[v]ᗮ u : E) = {.v}ᗮ := by
  rw [orthogonal_line_inf, sup_comm, sup_orthogonal_inf_of_hasOrthogonalProjection]
  rw [span_singleton_le_iff_mem]
  exact coe_mem _

theorem orthogonalProjection_eq_zero_of_mem {F : Submodule ℝ E} [CompleteSpace F] {x : E}
    (h : x ∈ Fᗮ) : orthogonalProjectionOnto F x = 0 := by
  refine Subtype.coe_injective (eq_starProjection_of_mem_of_inner_eq_zero F.zero_mem ?_)
  simp only [coe_zero, sub_zero]
  exact (mem_orthogonal' F x).mp h

theorem inner_projection_self_eq_zero_iff {F : Submodule ℝ E} [CompleteSpace F] {x : E} :
    ⟪x, orthogonalProjectionOnto F x⟫ = 0 ↔ x ∈ Fᗮ := by
  obtain ⟨y, hy, z, hz, rfl⟩ := F.exists_add_mem_mem_orthogonal x
  rw [inner_add_left, map_add, coe_add, inner_add_right, inner_add_right]
  suffices y = 0 ↔ y + z ∈ Fᗮ by
    simpa [orthogonalProjection_eq_zero_of_mem hz, starProjection_eq_self_iff.mpr hy,
      inner_eq_zero_symm.mp (hz y hy)]
  rw [add_mem_cancel_right hz]
  constructor
  · rintro rfl
    exact Fᗮ.zero_mem
  · exact Submodule.disjoint_def.mp (orthogonal_disjoint F) _ hy

variable {x₀ x : E}

@[simp]
theorem mem_orthogonal_span_singleton_iff {x₀ x : E} : x ∈ {.x₀}ᗮ ↔ ⟪x₀, x⟫ = 0 := by
  simp only [mem_orthogonal, forall_mem_span_singleton, inner_smul_left, RCLike.conj_to_real,
    mul_eq_zero]
  refine ⟨fun h ↦ by simpa using h 1, fun h t ↦ Or.inr h⟩

@[simp]
theorem orthogonalProjection_orthogonal_singleton {x y : E} :
    pr[x]ᗮ y =
      ⟨y - (⟪x, y⟫ / ⟪x, x⟫) • x, by
        rcases eq_or_ne x 0 with (rfl | hx)
        · simp
        simp only [inner_self_eq_norm_sq_to_K, RCLike.ofReal_real_eq_id, id_eq,
          mem_orthogonal_span_singleton_iff]
        rw [inner_sub_right, inner_smul_right]
        simp [norm_ne_zero_iff.mpr hx]⟩ := by
  apply Subtype.ext
  have := starProjection_add_starProjection_orthogonal (K := span ℝ ({x} : Set E)) y
  simp [eq_sub_of_add_eq' this, starProjection_singleton]

theorem coe_orthogonalProjection_orthogonal_singleton {x y : E} :
    (pr[x]ᗮ y : E) = y - (⟪x, y⟫ / ⟪x, x⟫) • x := by
  rw [orthogonalProjection_orthogonal_singleton]

theorem foo {x₀ x : E} (h : ⟪x₀, x⟫ ≠ 0) (y : E) (hy : y ∈ {.x₀}ᗮ) :
    (pr[x]ᗮ y : E) - (⟪x₀, pr[x]ᗮ y⟫ / ⟪x₀, x⟫) • x = y :=  by
  conv_rhs => rw [← starProjection_add_starProjection_orthogonal (K := Δ x) y]
  rw [starProjection_singleton, sub_eq_add_neg, add_comm, ← neg_smul]
  congr 2
  have := starProjection_add_starProjection_orthogonal (K := Δ x) y
  rw [starProjection_singleton] at this
  apply_fun fun z ↦ ⟪x₀, z⟫ at this
  rw [mem_orthogonal_span_singleton_iff.mp hy, inner_add_right, inner_smul_right] at this
  apply (eq_of_sub_eq_zero _).symm
  rw [sub_neg_eq_add]
  apply mul_left_injective₀ h
  dsimp only
  rwa [add_mul, MulZeroClass.zero_mul, div_mul_cancel₀ _ h]

attribute [fun_prop] Continuous.inner

/-- Given two non-orthogonal vectors in an inner product space,
`orthogonal_projection_orthogonal_line_iso` is the continuous linear equivalence between their
orthogonal complements obtained from orthogonal projection. -/
def orthogonalProjectionOrthogonalLineIso {x₀ x : E} (h : ⟪x₀, x⟫ ≠ 0) : {.x₀}ᗮ ≃L[ℝ] {.x}ᗮ :=
  {
    pr[x]ᗮ.comp (subtypeL {.x₀}ᗮ) with
    invFun := fun y ↦
      ⟨y - (⟪x₀, y⟫ / ⟪x₀, x⟫) • x, by
        rw [mem_orthogonal_span_singleton_iff, inner_sub_right, inner_smul_right]
        simp [h]⟩
    left_inv := by
      rintro ⟨y, hy⟩
      ext
      exact foo h y hy
    right_inv := by
      rintro ⟨y, hy⟩
      ext
      dsimp
      rw [map_sub, map_smul, starProjection_apply, starProjection_apply,
        orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero, coe_zero,
        ← starProjection_apply, smul_zero, sub_zero, starProjection_eq_self_iff.mpr hy]
    continuous_toFun := (pr[x]ᗮ.comp (subtypeL {.x₀}ᗮ)).continuous
    continuous_invFun := by fun_prop }

theorem orthogonalProjection_comp_coe (K : Submodule ℝ E) [CompleteSpace K] :
    orthogonalProjectionOnto K ∘ ((↑) : K → E) = id := by
  ext1 x
  exact orthogonalProjectionOnto_mem_subspace_eq_self x

variable (E)

-- Is this really missing??
theorem NormedSpace.continuousAt_iff {E F : Type*} [SeminormedAddCommGroup E]
    [SeminormedAddCommGroup F] (f : E → F) (x : E) :
    ContinuousAt f x ↔ ∀ ε > 0, ∃ δ > 0, ∀ y, ‖y - x‖ < δ → ‖f y - f x‖ < ε := by
  simp_rw [Metric.continuousAt_iff, dist_eq_norm]

theorem NormedSpace.continuousAt_iff' {E F : Type*} [SeminormedAddCommGroup E]
    [SeminormedAddCommGroup F] (f : E → F) (x : E) :
    ContinuousAt f x ↔ ∀ ε > 0, ∃ δ > 0, ∀ y, ‖y - x‖ ≤ δ → ‖f y - f x‖ ≤ ε := by
  rw [NormedSpace.continuousAt_iff]
  constructor <;> intro h ε ε_pos
  · rcases h ε ε_pos with ⟨η, η_pos, hη⟩
    refine ⟨η / 2, half_pos η_pos, fun h hy ↦ le_of_lt (hη  _ ?_)⟩
    linarith
  · rcases h (ε / 2) (half_pos ε_pos) with ⟨δ, δ_pos, hδ⟩
    refine ⟨δ, δ_pos, fun y hy ↦ ?_⟩
    linarith [hδ y (by linarith)]

-- Is this really missing??
theorem NormedSpace.continuous_iff {E F : Type*} [SeminormedAddCommGroup E]
    [SeminormedAddCommGroup F] (f : E → F) :
    Continuous f ↔ ∀ x, ∀ ε > 0, ∃ δ > 0, ∀ y, ‖y - x‖ < δ → ‖f y - f x‖ < ε := by
  simp_rw [Metric.continuous_iff, dist_eq_norm]

theorem NormedSpace.continuous_iff' {E F : Type*} [SeminormedAddCommGroup E]
    [SeminormedAddCommGroup F] (f : E → F) :
    Continuous f ↔ ∀ x, ∀ ε > 0, ∃ δ > 0, ∀ y, ‖y - x‖ ≤ δ → ‖f y - f x‖ ≤ ε := by
  simp_rw [continuous_iff_continuousAt, NormedSpace.continuousAt_iff']

variable {E}

attribute [fun_prop] continuous_norm' continuous_norm

@[continuity, fun_prop]
theorem continuousAt_orthogonalProjection_orthogonal {x₀ : E} (hx₀ : x₀ ≠ 0) :
    ContinuousAt (fun x : E ↦ {.x}ᗮ.subtypeL.comp pr[x]ᗮ) x₀ := by
  rw [NormedSpace.continuousAt_iff']
  intro ε ε_pos
  have hNx₀ : 0 < ‖x₀‖ := norm_pos_iff.mpr hx₀
  have hNx₀2 : 0 < ‖x₀‖ ^ 2 := by apply pow_pos hNx₀
  suffices
    ∃ δ > 0, ∀ y, ‖y - x₀‖ ≤ δ → ∀ x, ‖(⟪x₀, x⟫ / ⟪x₀, x₀⟫) • x₀ - (⟪y, x⟫ / ⟪y, y⟫) • y‖ ≤ ε * ‖x‖
    by
    simpa only [ContinuousLinearMap.opNorm_le_iff (le_of_lt ε_pos),
      orthogonalProjection_orthogonal_singleton, FunLike.coe_sub,
      ContinuousLinearMap.coe_comp, coe_subtypeL, Submodule.coe_subtype, Pi.sub_apply, comp_apply,
      coe_mk, sub_sub_sub_cancel_left]
  let N : E → E := fun x ↦ ⟪x, x⟫⁻¹ • x
  have hNx₀ : 0 < ‖N x₀‖ := by
    -- and now let's suffer
    rw [norm_smul, real_inner_self_eq_norm_sq, norm_inv]
    exact mul_pos (inv_pos_of_pos (norm_pos_iff.mpr hNx₀2.ne')) hNx₀
  have cont : ContinuousAt N x₀ := by
    simp_rw [N, real_inner_self_eq_norm_sq]
    fun_prop (disch := exact hNx₀2.ne')
  have lim : Tendsto (fun y ↦ ‖N x₀ - N y‖ * ‖y‖) (𝓝 x₀) (𝓝 0) := by
    rw [← MulZeroClass.zero_mul ‖x₀‖]
    apply Tendsto.mul
    · rw [← show ‖N x₀ - N x₀‖ = 0 by simp]
      exact (tendsto_const_nhds.sub cont).norm
    exact continuous_norm.continuousAt
  have key :
    ∀ x y,
      (⟪x₀, x⟫ / ⟪x₀, x₀⟫) • x₀ - (⟪y, x⟫ / ⟪y, y⟫) • y =
        ⟪N x₀, x⟫ • (x₀ - y) + ⟪N x₀ - N y, x⟫ • y := by
    intro x y
    simp only [N, inner_smul_left, inner_sub_left, RCLike.conj_to_real, smul_sub, sub_smul,
      sub_add_sub_cancel]
    field_simp
  simp only [key]
  simp_rw [Metric.tendsto_nhds_nhds, Real.dist_0_eq_abs, dist_eq_norm] at lim
  rcases lim (ε / 2) (half_pos ε_pos) with ⟨η, η_pos, hη⟩
  refine ⟨min (ε / 2 / ‖N x₀‖) (η / 2), by positivity, ?_⟩
  intro y hy x
  have hy₁ := hy.trans (min_le_left _ _); have hy₂ := hy.trans (min_le_right _ _); clear hy
  specialize hη (by linarith : ‖y - x₀‖ < η)
  rw [abs_of_nonneg (by positivity)] at hη
  calc ‖⟪N x₀, x⟫ • (x₀ - y) + ⟪N x₀ - N y, x⟫ • y‖
      _ ≤ ‖⟪N x₀, x⟫ • (x₀ - y)‖ + ‖⟪N x₀ - N y, x⟫ • y‖ := norm_add_le _ _
      _ ≤ ‖N x₀‖ * ‖x‖ * ‖x₀ - y‖ + ‖N x₀ - N y‖ * ‖x‖ * ‖y‖ := (add_le_add ?_ ?_)
      _ ≤ ε / 2 * ‖x‖ + ε / 2 * ‖x‖ := (add_le_add ?_ ?_)
      _ = ε * ‖x‖ := by linarith
  · rw [norm_smul]
    gcongr
    exact norm_inner_le_norm _ _
  · rw [norm_smul]
    gcongr
    exact norm_inner_le_norm _ _
  · rw [mul_comm, ← mul_assoc, norm_sub_rev]
    gcongr
    exact (le_div_iff₀ hNx₀).mp hy₁
  · rw [mul_comm, ← mul_assoc, mul_comm ‖y‖]
    gcongr
