import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Algebra.Module.ULift
import SphereEversion.ToMathlib.Analysis.Calculus

import Mathlib.Tactic.FunProp.ContDiff

open TopologicalSpace MeasureTheory Filter FirstCountableTopology Metric Set Function

open scoped Topology Filter NNReal

section -- PRed in #10004

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {H : Type _}
  [NormedAddCommGroup H] [NormedSpace ℝ H] (ν : Measure ℝ)

/-- Interval version of `hasFDerivAt_integral_of_dominated_of_fderiv_le` -/
theorem hasFDerivAt_integral_of_dominated_of_fderiv_le'' {F : H → ℝ → E} {F' : H → ℝ → H →L[ℝ] E} {x₀ : H}
    {a b : ℝ} {bound : ℝ → ℝ} {ε : ℝ} (ε_pos : 0 < ε)
    (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) <| ν.restrict (Ι a b))
    (hF_int : IntervalIntegrable (F x₀) ν a b)
    (hF'_meas : AEStronglyMeasurable (F' x₀) <| ν.restrict (Ι a b))
    (h_bound : ∀ᵐ t ∂ν.restrict (Ι a b), ∀ x ∈ ball x₀ ε, ‖F' x t‖ ≤ bound t)
    (bound_integrable : IntervalIntegrable bound ν a b)
    (h_diff : ∀ᵐ t ∂ν.restrict (Ι a b), ∀ x ∈ ball x₀ ε, HasFDerivAt (fun x ↦ F x t) (F' x t) x) :
    HasFDerivAt (fun x ↦ ∫ t in a..b, F x t ∂ν) (∫ t in a..b, F' x₀ t ∂ν) x₀ := by
  erw [ae_restrict_uIoc_iff] at h_diff h_bound
  simp_rw [AEStronglyMeasurable.aestronglyMeasurable_uIoc_iff, eventually_and] at hF_meas hF'_meas
  exact
    (hasFDerivAt_integral_of_dominated_of_fderiv_le ε_pos hF_meas.1 hF_int.1 hF'_meas.1 h_bound.1
          bound_integrable.1 h_diff.1).sub
      (hasFDerivAt_integral_of_dominated_of_fderiv_le ε_pos hF_meas.2 hF_int.2 hF'_meas.2 h_bound.2
        bound_integrable.2 h_diff.2)

/-- Interval version of `hasFDerivAt_integral_of_dominated_loc_of_lip` -/
theorem hasFDerivAt_integral_of_dominated_loc_of_lip_interval {F : H → ℝ → E} {F' : ℝ → H →L[ℝ] E} {x₀ : H}
    {a b : ℝ} {bound : ℝ → ℝ} {ε : ℝ} (ε_pos : 0 < ε)
    (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) <| ν.restrict (Ι a b))
    (hF_int : IntervalIntegrable (F x₀) ν a b)
    (hF'_meas : AEStronglyMeasurable F' <| ν.restrict (Ι a b))
    (h_lip : ∀ᵐ t ∂ν.restrict (Ι a b),
      LipschitzOnWith (Real.nnabs <| bound t) (fun x ↦ F x t) (ball x₀ ε))
    (bound_integrable : IntervalIntegrable bound ν a b)
    (h_diff : ∀ᵐ t ∂ν.restrict (Ι a b), HasFDerivAt (fun x ↦ F x t) (F' t) x₀) :
    IntervalIntegrable F' ν a b ∧
      HasFDerivAt (fun x ↦ ∫ t in a..b, F x t ∂ν) (∫ t in a..b, F' t ∂ν) x₀ := by
  simp_rw [AEStronglyMeasurable.aestronglyMeasurable_uIoc_iff, eventually_and] at hF_meas hF'_meas
  rw [ae_restrict_uIoc_iff] at h_lip h_diff
  have H₁ :=
    hasFDerivAt_integral_of_dominated_loc_of_lip ε_pos hF_meas.1 hF_int.1 hF'_meas.1 h_lip.1
      bound_integrable.1 h_diff.1
  have H₂ :=
    hasFDerivAt_integral_of_dominated_loc_of_lip ε_pos hF_meas.2 hF_int.2 hF'_meas.2 h_lip.2
      bound_integrable.2 h_diff.2
  exact ⟨⟨H₁.1, H₂.1⟩, H₁.2.sub H₂.2⟩

end

section

open Function

theorem continuous_parametric_integral_of_continuous
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    [SecondCountableTopologyEither α E] {μ : MeasureTheory.Measure α} [IsLocallyFiniteMeasure μ]
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X] [LocallyCompactSpace X]
    {F : X → α → E} (hF : Continuous fun p : X × α ↦ F p.1 p.2) {s : Set α} (hs : IsCompact s) :
    Continuous fun x ↦ ∫ a in s, F x a ∂μ := by
  rw [continuous_iff_continuousAt]
  intro x₀
  rcases exists_compact_mem_nhds x₀ with ⟨U, U_cpct, U_nhds⟩
  rcases(U_cpct.prod hs).bddAbove_image hF.norm.continuousOn with ⟨M, hM⟩
  apply continuousAt_of_dominated
  · exact eventually_of_forall fun x ↦ (hF.comp (Continuous.Prod.mk x)).aestronglyMeasurable
  · refine Eventually.mono U_nhds fun x x_in ↦ ?_
    rw [ae_restrict_iff]
    exact eventually_of_forall fun t t_in ↦ hM (mem_image_of_mem _ <| mk_mem_prod x_in t_in)
    exact (isClosed_le (hF.comp <| Continuous.Prod.mk x).norm continuous_const).measurableSet
  · exact integrableOn_const.mpr (Or.inr hs.measure_lt_top)
  · apply ae_of_all
    intro a
    dsimp -- TODO(funprop): this shouldn't be necessary
    fun_prop

end

section

open MeasureTheory

variable {μ : Measure ℝ} {X : Type _} [TopologicalSpace X] [FirstCountableTopology X] {E : Type _}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem continuousAt_parametric_primitive_of_dominated {F : X → ℝ → E} (bound : ℝ → ℝ) (a b : ℝ)
    {a₀ b₀ : ℝ} {x₀ : X} (hF_meas : ∀ x, AEStronglyMeasurable (F x) (μ.restrict <| Ι a b))
    (h_bound : ∀ᶠ x in 𝓝 x₀, ∀ᵐ t ∂μ.restrict <| Ι a b, ‖F x t‖ ≤ bound t)
    (bound_integrable : IntervalIntegrable bound μ a b)
    (h_cont : ∀ᵐ t ∂μ.restrict <| Ι a b, ContinuousAt (fun x ↦ F x t) x₀) (ha₀ : a₀ ∈ Ioo a b)
    (hb₀ : b₀ ∈ Ioo a b) (hμb₀ : μ {b₀} = 0) :
    ContinuousAt (fun p : X × ℝ ↦ ∫ t : ℝ in a₀..p.2, F p.1 t ∂μ) (x₀, b₀) := by
  have hsub : ∀ {a₀ b₀}, a₀ ∈ Ioo a b → b₀ ∈ Ioo a b → Ι a₀ b₀ ⊆ Ι a b := fun ha₀ hb₀ ↦
    (ordConnected_Ioo.uIoc_subset ha₀ hb₀).trans (Ioo_subset_Ioc_self.trans Ioc_subset_uIoc)
  have Ioo_nhds : Ioo a b ∈ 𝓝 b₀ := Ioo_mem_nhds hb₀.1 hb₀.2
  have Icc_nhds : Icc a b ∈ 𝓝 b₀ := Icc_mem_nhds hb₀.1 hb₀.2
  have hx₀ : ∀ᵐ t : ℝ ∂μ.restrict (Ι a b), ‖F x₀ t‖ ≤ bound t := h_bound.self_of_nhds
  have : ∀ᶠ p : X × ℝ in 𝓝 (x₀, b₀),
      ∫ s in a₀..p.2, F p.1 s ∂μ =
        ∫ s in a₀..b₀, F p.1 s ∂μ + ∫ s in b₀..p.2, F x₀ s ∂μ +
          ∫ s in b₀..p.2, F p.1 s - F x₀ s ∂μ := by
    rw [nhds_prod_eq]
    refine (h_bound.prod_mk Ioo_nhds).mono ?_
    rintro ⟨x, t⟩ ⟨hx : ∀ᵐ t : ℝ ∂μ.restrict (Ι a b), ‖F x t‖ ≤ bound t, ht : t ∈ Ioo a b⟩
    dsimp (config := { eta := false })
    have hiF : ∀ {x a₀ b₀},
        (∀ᵐ t : ℝ ∂μ.restrict (Ι a b), ‖F x t‖ ≤ bound t) → a₀ ∈ Ioo a b → b₀ ∈ Ioo a b →
          IntervalIntegrable (F x) μ a₀ b₀ := fun {x a₀ b₀} hx ha₀ hb₀ ↦
      (bound_integrable.mono_set_ae <| eventually_of_forall <| hsub ha₀ hb₀).mono_fun'
        ((hF_meas x).mono_set <| hsub ha₀ hb₀)
        (ae_restrict_of_ae_restrict_of_subset (hsub ha₀ hb₀) hx)
    rw [intervalIntegral.integral_sub, add_assoc, add_sub_cancel'_right,
      intervalIntegral.integral_add_adjacent_intervals]
    · exact hiF hx ha₀ hb₀
    · exact hiF hx hb₀ ht
    · exact hiF hx hb₀ ht
    · exact hiF hx₀ hb₀ ht
  rw [continuousAt_congr this]; clear this
  refine (ContinuousAt.add ?_ ?_).add ?_
  · exact (intervalIntegral.continuousAt_of_dominated_interval
        (eventually_of_forall fun x ↦ (hF_meas x).mono_set <| hsub ha₀ hb₀)
          (h_bound.mono fun x hx ↦
            ae_imp_of_ae_restrict <| ae_restrict_of_ae_restrict_of_subset (hsub ha₀ hb₀) hx)
          (bound_integrable.mono_set_ae <| eventually_of_forall <| hsub ha₀ hb₀) <|
          ae_imp_of_ae_restrict <| ae_restrict_of_ae_restrict_of_subset (hsub ha₀ hb₀) h_cont).fst'
  · refine (?_ : ContinuousAt (fun t ↦ ∫ s in b₀..t, F x₀ s ∂μ) b₀).snd'
    apply ContinuousWithinAt.continuousAt _ (Icc_mem_nhds hb₀.1 hb₀.2)
    apply intervalIntegral.continuousWithinAt_primitive hμb₀
    rw [min_eq_right hb₀.1.le, max_eq_right hb₀.2.le]
    exact bound_integrable.mono_fun' (hF_meas x₀) hx₀
  · suffices : Tendsto (fun x : X × ℝ ↦ ∫ s in b₀..x.2, F x.1 s - F x₀ s ∂μ) (𝓝 (x₀, b₀)) (𝓝 0)
    · simpa [ContinuousAt]
    have : ∀ᶠ p : X × ℝ in 𝓝 (x₀, b₀),
        ‖∫ s in b₀..p.2, F p.1 s - F x₀ s ∂μ‖ ≤ |∫ s in b₀..p.2, 2 * bound s ∂μ| := by
      rw [nhds_prod_eq]
      refine (h_bound.prod_mk Ioo_nhds).mono ?_
      rintro ⟨x, t⟩ ⟨hx : ∀ᵐ t ∂μ.restrict (Ι a b), ‖F x t‖ ≤ bound t, ht : t ∈ Ioo a b⟩
      have H : ∀ᵐ t : ℝ ∂μ.restrict (Ι b₀ t), ‖F x t - F x₀ t‖ ≤ 2 * bound t := by
        apply (ae_restrict_of_ae_restrict_of_subset (hsub hb₀ ht) (hx.and hx₀)).mono
        rintro s ⟨hs₁, hs₂⟩
        calc
          ‖F x s - F x₀ s‖ ≤ ‖F x s‖ + ‖F x₀ s‖ := norm_sub_le _ _
          _ ≤ 2 * bound s := by linarith only [hs₁, hs₂]
      exact
        intervalIntegral.norm_integral_le_of_norm_le H
          ((bound_integrable.mono_set' <| hsub hb₀ ht).const_mul 2)
    apply squeeze_zero_norm' this
    have : Tendsto (fun t ↦ ∫ s in b₀..t, 2 * bound s ∂μ) (𝓝 b₀) (𝓝 0) := by
      suffices ContinuousAt (fun t ↦ ∫ s in b₀..t, 2 * bound s ∂μ) b₀ by
        simpa [ContinuousAt] using this
      apply ContinuousWithinAt.continuousAt _ Icc_nhds
      apply intervalIntegral.continuousWithinAt_primitive hμb₀
      apply IntervalIntegrable.const_mul
      apply bound_integrable.mono_set'
      rw [min_eq_right hb₀.1.le, max_eq_right hb₀.2.le]
    rw [nhds_prod_eq]
    exact (continuous_abs.tendsto' _ _ abs_zero).comp (this.comp tendsto_snd)

end

section

variable {μ : Measure ℝ} [IsLocallyFiniteMeasure μ] [NoAtoms μ] {X : Type _} [TopologicalSpace X]
  [FirstCountableTopology X] {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem continuous_parametric_primitive_of_continuous [LocallyCompactSpace X] {F : X → ℝ → E}
    {a₀ : ℝ} (hF : Continuous fun p : X × ℝ ↦ F p.1 p.2) :
    Continuous fun p : X × ℝ ↦ ∫ t in a₀..p.2, F p.1 t ∂μ := by
  rw [continuous_iff_continuousAt]
  rintro ⟨x₀, b₀⟩
  rcases exists_compact_mem_nhds x₀ with ⟨U, U_cpct, U_nhds⟩
  cases' exists_lt (min a₀ b₀) with a a_lt
  cases' exists_gt (max a₀ b₀) with b lt_b
  rw [lt_min_iff] at a_lt
  rw [max_lt_iff] at lt_b
  have a₀_in : a₀ ∈ Ioo a b := ⟨a_lt.1, lt_b.1⟩
  have b₀_in : b₀ ∈ Ioo a b := ⟨a_lt.2, lt_b.2⟩
  obtain ⟨M, hM⟩ :=
    (U_cpct.prod (isCompact_Icc (a := a) (b := b))).bddAbove_image hF.norm.continuousOn
  refine continuousAt_parametric_primitive_of_dominated (fun _ ↦ M) a b ?_ ?_ ?_ ?_ a₀_in b₀_in
    (measure_singleton b₀)
  · exact fun x ↦ (hF.comp (Continuous.Prod.mk x)).aestronglyMeasurable
  · refine Eventually.mono U_nhds fun x (x_in : x ∈ U) ↦ ?_
    simp_rw [ae_restrict_iff' measurableSet_uIoc]
    refine eventually_of_forall fun t t_in ↦ ?_
    refine hM (mem_image_of_mem _ <| mk_mem_prod x_in ?_)
    rw [uIoc_of_le (a_lt.1.trans lt_b.1).le] at t_in
    exact mem_Icc_of_Ioc t_in
  · apply intervalIntegrable_const
  · apply ae_of_all
    intro a
    apply (hF.comp₂ continuous_id continuous_const).continuousAt

theorem continuous_parametric_intervalIntegral_of_continuous [LocallyCompactSpace X] {a₀ : ℝ}
    {F : X → ℝ → E} (hF : Continuous fun p : X × ℝ ↦ F p.1 p.2) {s : X → ℝ} (hs : Continuous s) :
    Continuous fun x ↦ ∫ t in a₀..s x, F x t ∂μ :=
  show Continuous ((fun p : X × ℝ ↦ ∫ t in a₀..p.2, F p.1 t ∂μ) ∘ fun x ↦ (x, s x)) from
    (continuous_parametric_primitive_of_continuous hF).comp₂ continuous_id hs

theorem continuous_parametric_intervalIntegral_of_continuous' [LocallyCompactSpace X]
    {F : X → ℝ → E} (hF : Continuous fun p : X × ℝ ↦ F p.1 p.2) (a₀ b₀ : ℝ) :
    Continuous fun x ↦ ∫ t in a₀..b₀, F x t ∂μ :=
  continuous_parametric_intervalIntegral_of_continuous hF continuous_const

end

section

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {H : Type _}
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-!
We could weaken `FiniteDimensional ℝ H` with `SecondCountable (H →L[ℝ] E)` if needed,
but that is less convenient to work with.
-/


open Real ContinuousLinearMap Asymptotics

/-- This statement is a new version using the continuity note in mathlib.
See commit `39e3f3f` for an older version
Maybe todo: let `a` depend on `x`.
-/
theorem hasFDerivAt_parametric_primitive_of_lip' (F : H → ℝ → E) (F' : ℝ → H →L[ℝ] E) {x₀ : H}
    {G' : H →L[ℝ] E} {bound : ℝ → ℝ} {s : H → ℝ} {ε : ℝ} (ε_pos : 0 < ε) {a a₀ b₀ : ℝ}
    {s' : H →L[ℝ] ℝ} (ha : a ∈ Ioo a₀ b₀) (hsx₀ : s x₀ ∈ Ioo a₀ b₀)
    (hF_meas : ∀ x ∈ ball x₀ ε, AEStronglyMeasurable (F x) (volume.restrict (Ioo a₀ b₀)))
    (hF_int : IntegrableOn (F x₀) (Ioo a₀ b₀)) (hF_cont : ContinuousAt (F x₀) (s x₀))
    (hF'_meas : AEStronglyMeasurable F' (volume.restrict <| Ι a (s x₀)))
    (h_lipsch :
      ∀ᵐ t ∂volume.restrict <| Ioo a₀ b₀,
        LipschitzOnWith (nnabs <| bound t) (fun x ↦ F x t) (ball x₀ ε))
    (bound_integrable : IntegrableOn bound (Ioo a₀ b₀)) (bound_cont : ContinuousAt bound (s x₀))
    (bound_nonneg : ∀ t, 0 ≤ bound t)
    -- this is not really needed, but much more convenient
    (h_diff : ∀ᵐ a ∂volume.restrict (Ι a (s x₀)), HasFDerivAt (fun x ↦ F x a) (F' a) x₀)
    (s_diff : HasFDerivAt s s' x₀)
    (hG' : (∫ t in a..s x₀, F' t) + (toSpanSingleton ℝ (F x₀ (s x₀))).comp s' = G') :
    IntervalIntegrable F' volume a (s x₀) ∧
      HasFDerivAt (fun x : H ↦ ∫ t in a..s x, F x t) G' x₀ := by
  subst hG'
  let φ : H → ℝ → E := fun x t ↦ ∫ s in a..t, F x s
  have Ioo_nhds : Ioo a₀ b₀ ∈ 𝓝 (s x₀) := Ioo_mem_nhds hsx₀.1 hsx₀.2
  have bound_int : ∀ {s u}, s ∈ Ioo a₀ b₀ → u ∈ Ioo a₀ b₀ →
      IntervalIntegrable bound volume s u := fun hs hu ↦
    (bound_integrable.mono_set <| ordConnected_Ioo.uIcc_subset hs hu).intervalIntegrable
  have mem_nhds : ball x₀ ε ∩ s ⁻¹' Ioo a₀ b₀ ∈ 𝓝 x₀ :=
    Filter.inter_mem (ball_mem_nhds x₀ ε_pos) (s_diff.continuousAt.preimage_mem_nhds Ioo_nhds)
  have x₀_in : x₀ ∈ ball x₀ ε := mem_ball_self ε_pos
  have hF_meas_ball : ∀ {x}, x ∈ ball x₀ ε → ∀ {s u}, s ∈ Ioo a₀ b₀ → u ∈ Ioo a₀ b₀ →
      AEStronglyMeasurable (F x) (volume.restrict <| Ι s u) := fun hx s u hs hu ↦
    (hF_meas _ hx).mono_set (ordConnected_Ioo.uIoc_subset hs hu)
  have hF_int_ball : ∀ x ∈ ball x₀ ε, ∀ {s u}, s ∈ Ioo a₀ b₀ → u ∈ Ioo a₀ b₀ →
      IntervalIntegrable (F x) volume s u := fun x hx s u hs hu ↦ by
    have : IntegrableOn (F x) (Ioo a₀ b₀) := by
      apply integrable_of_norm_sub_le (hF_meas x hx) hF_int (bound_integrable.mul_const ‖x - x₀‖)
      apply h_lipsch.mono
      intro t ht
      rw [norm_sub_rev]
      rw [lipschitzOnWith_iff_norm_sub_le] at ht
      simpa [bound_nonneg t] using ht hx x₀_in
    exact (this.mono_set <| ordConnected_Ioo.uIcc_subset hs hu).intervalIntegrable
  constructor
  · apply (bound_int ha hsx₀).mono_fun' hF'_meas _
    replace h_lipsch :
      ∀ᵐ t ∂volume.restrict (Ι a (s x₀)),
        LipschitzOnWith (nnabs (bound t)) (fun x : H ↦ F x t) (ball x₀ ε)
    exact ae_restrict_of_ae_restrict_of_subset (ordConnected_Ioo.uIoc_subset ha hsx₀) h_lipsch
    filter_upwards [h_lipsch, h_diff]
    intro t ht_lip ht_diff
    rw [show bound t = nnabs (bound t) by simp [bound_nonneg t] ]
    exact ht_diff.le_of_lipschitzOn (ball_mem_nhds x₀ ε_pos) ht_lip
  · have D₁ : HasFDerivAt (fun x ↦ φ x (s x₀)) (∫ t in a..s x₀, F' t) x₀ := by
      replace hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) (volume.restrict (Ι a (s x₀)))
      exact Eventually.mono (ball_mem_nhds x₀ ε_pos) fun x hx ↦ hF_meas_ball hx ha hsx₀
      replace hF_int : IntervalIntegrable (F x₀) volume a (s x₀) := hF_int_ball x₀ x₀_in ha hsx₀
      exact (hasFDerivAt_integral_of_dominated_loc_of_lip_interval _ ε_pos hF_meas hF_int hF'_meas
        (ae_restrict_of_ae_restrict_of_subset (ordConnected_Ioo.uIoc_subset ha hsx₀) h_lipsch)
        (bound_int ha hsx₀) h_diff).2
    have D₂ : HasFDerivAt (fun x ↦ φ x₀ (s x)) ((toSpanSingleton ℝ (F x₀ (s x₀))).comp s') x₀ := by
      suffices HasFDerivAt (φ x₀) (toSpanSingleton ℝ (F x₀ (s x₀))) (s x₀) from this.comp _ s_diff
      rw [hasFDerivAt_iff_hasDerivAt, toSpanSingleton_apply, one_smul]
      exact intervalIntegral.integral_hasDerivAt_right (hF_int_ball x₀ x₀_in ha hsx₀)
        ⟨Ioo a₀ b₀, Ioo_nhds, hF_meas x₀ x₀_in⟩ hF_cont
    have D₃ : HasFDerivAt (fun x ↦ ∫ t in s x₀..s x, F x t - F x₀ t) 0 x₀ := by
      refine IsBigO.hasFDerivAt (𝕜 := ℝ) ?_ one_lt_two
      have O₁ : (fun x ↦ ∫ s in s x₀..s x, bound s) =O[𝓝 x₀] fun x ↦ ‖x - x₀‖ := by
        have : (fun x ↦ s x - s x₀) =O[𝓝 x₀] fun x ↦ ‖x - x₀‖ := s_diff.isBigO_sub.norm_right
        refine IsBigO.trans ?_ this
        show ((fun t ↦ ∫ s in s x₀..t, bound s) ∘ s) =O[𝓝 x₀] ((fun t ↦ t - s x₀) ∘ s)
        refine IsBigO.comp_tendsto ?_ s_diff.continuousAt
        have M : StronglyMeasurableAtFilter bound (𝓝 (s x₀)) volume :=
          ⟨Ioo a₀ b₀, Ioo_nhds, bound_integrable.1⟩
        sorry /- TODO-BUMP refine' (intervalIntegral.integral_hasDerivAt_right (bound_int ha hsx₀)
          M bound_cont).hasFDerivAt.isBigO.congr' _ EventuallyEq.rfl
        apply Eventually.mono Ioo_nhds
        rintro t ht
        dsimp only
        rw [intervalIntegral.integral_interval_sub_left (bound_int ha ht) (bound_int ha hsx₀)] -/
      have O₂ : (fun x ↦ ‖x - x₀‖) =O[𝓝 x₀] fun x ↦ ‖x - x₀‖ := isBigO_refl _ _
      have O₃ : (fun x ↦ ∫ t : ℝ in s x₀..s x, F x t - F x₀ t) =O[𝓝 x₀] fun x ↦
          (∫ t' in s x₀..s x, bound t') * ‖x - x₀‖ := by
        have bdd : ∀ᶠ x in 𝓝 x₀,
            ‖∫ s in s x₀..s x, F x s - F x₀ s‖ ≤ |∫ s in s x₀..s x, bound s| * ‖x - x₀‖ := by
          apply Eventually.mono mem_nhds
          rintro x ⟨hx : x ∈ ball x₀ ε, hsx : s x ∈ Ioo a₀ b₀⟩
          rw [← abs_of_nonneg (norm_nonneg <| x - x₀), ← abs_mul, ←
            intervalIntegral.integral_mul_const]
          apply intervalIntegral.norm_integral_le_of_norm_le _ ((bound_int hsx₀ hsx).mul_const _)
          apply ae_restrict_of_ae_restrict_of_subset (ordConnected_Ioo.uIoc_subset hsx₀ hsx)
          apply h_lipsch.mono
          intro t ht
          rw [lipschitzOnWith_iff_norm_sub_le] at ht
          simp only [coe_nnabs] at ht
          rw [← abs_of_nonneg (bound_nonneg t)]
          exact ht hx (mem_ball_self ε_pos)
        rw [← isBigO_norm_right]
        simp only [norm_eq_abs, abs_mul, abs_norm]
        exact bdd.isBigO
      simp_rw [pow_two]
      exact O₃.trans (O₁.mul O₂)
    have : ∀ᶠ x in 𝓝 x₀,
        ∫ t in a..s x, F x t =
          (φ x (s x₀) + φ x₀ (s x) + ∫ t in s x₀..s x, F x t - F x₀ t) - φ x₀ (s x₀) := by
      apply Eventually.mono mem_nhds
      rintro x ⟨hx : x ∈ ball x₀ ε, hsx : s x ∈ Ioo a₀ b₀⟩
      have int₁ : IntervalIntegrable (F x₀) volume a (s x₀) := hF_int_ball x₀ x₀_in ha hsx₀
      have int₂ : IntervalIntegrable (F x₀) volume (s x₀) (s x) := hF_int_ball x₀ x₀_in hsx₀ hsx
      have int₃ : IntervalIntegrable (F x) volume a (s x₀) := hF_int_ball x hx ha hsx₀
      have int₄ : IntervalIntegrable (F x) volume (s x₀) (s x) := hF_int_ball x hx hsx₀ hsx
      dsimp
      rw [intervalIntegral.integral_sub int₄ int₂, add_sub, add_right_comm, sub_sub,
        intervalIntegral.integral_add_adjacent_intervals int₃ int₄,
        ← intervalIntegral.integral_add_adjacent_intervals int₁ int₂]
      abel
    apply HasFDerivAt.congr_of_eventuallyEq _ this
    simpa using ((D₁.add D₂).add D₃).sub (hasFDerivAt_const (φ x₀ (s x₀)) x₀)

local notation:70 u " ⬝ " φ => ContinuousLinearMap.comp (ContinuousLinearMap.toSpanSingleton ℝ u) φ

variable [FiniteDimensional ℝ H]

/-
A version of the above lemma using Floris' style statement.
This does not reuse the above lemma, but copies the proof.
-/
set_option synthInstance.maxHeartbeats 100000
theorem hasFDerivAt_parametric_primitive_of_contDiff' {F : H → ℝ → E} (hF : ContDiff ℝ 1 ↿F)
    {s : H → ℝ} (hs : ContDiff ℝ 1 s) (x₀ : H) (a : ℝ) :
    (IntervalIntegrable (fun t ↦ fderiv ℝ (fun x ↦ F x t) x₀) volume a <| s x₀) ∧
      HasFDerivAt (fun x : H ↦ ∫ t in a..s x, F x t)
        ((∫ t in a..s x₀, fderiv ℝ (fun x ↦ F x t) x₀) + F x₀ (s x₀) ⬝ fderiv ℝ s x₀) x₀ := by
  set a₀ := min a (s x₀) - 1
  set b₀ := max a (s x₀) + 1
  have ha : a ∈ Ioo a₀ b₀ := by
    dsimp
    constructor
    linarith [min_le_left a (s x₀)]
    linarith [le_max_left a (s x₀)]
  have ht₀ : s x₀ ∈ Ioo a₀ b₀ := by
    dsimp
    constructor
    linarith [min_le_right a (s x₀)]
    linarith [le_max_right a (s x₀)]
  have cpct : IsCompact (closedBall x₀ 1 ×ˢ Icc a₀ b₀) :=
    (ProperSpace.isCompact_closedBall x₀ 1).prod isCompact_Icc
  obtain ⟨K, F_lip⟩ : ∃ K, ∀ t ∈ Ioo a₀ b₀, LipschitzOnWith K (fun x ↦ F x t) (ball x₀ 1) := by
    have conv : Convex ℝ (closedBall x₀ 1 ×ˢ Icc a₀ b₀) :=
      (convex_closedBall x₀ 1).prod (convex_Icc a₀ b₀)
    rcases hF.lipschitzOnWith le_rfl conv cpct with ⟨K, hK⟩
    use K
    intro t t_in
    rw [show (fun x : H ↦ F x t) = uncurry F ∘ fun x : H ↦ (x, t) by ext; simp, ← mul_one K]
    apply hK.comp ((LipschitzWith.prod_mk_right t).lipschitzOnWith <| ball x₀ 1)
    rw [mapsTo']
    rintro ⟨x, s⟩ ⟨x', hx, h⟩; cases h
    exact ⟨ball_subset_closedBall hx, mem_Icc_of_Ioo t_in⟩
  have cont_x : ∀ x, Continuous (F x) := fun x ↦ hF.continuous.comp (Continuous.Prod.mk x)
  have int_Icc : ∀ x, IntegrableOn (F x) (Icc a₀ b₀) := fun x ↦
    (cont_x x).continuousOn.integrableOn_Icc
  have int_Ioo : ∀ x, IntegrableOn (F x) (Ioo a₀ b₀)
  · exact fun x ↦ (int_Icc x).mono_set Ioo_subset_Icc_self
  save
  apply
    hasFDerivAt_parametric_primitive_of_lip' _ _ zero_lt_one ha ht₀
      (fun x _hx ↦ (cont_x x).aestronglyMeasurable) (int_Ioo x₀) (cont_x x₀).continuousAt _ _ _
      (continuousAt_const : (ContinuousAt fun _ : ℝ ↦ (K : ℝ)) <| s x₀) fun _t ↦
      NNReal.coe_nonneg K
  · apply ae_of_all
    intro t
    apply (ContDiff.hasStrictFDerivAt _ le_rfl).hasFDerivAt
    rw [show (fun x ↦ F x t) = uncurry F ∘ fun x ↦ (x, t) by ext; simp]
    exact hF.comp ((contDiff_prod_mk_left t).of_le le_top)
  · exact (ContDiff.hasStrictFDerivAt hs le_rfl).hasFDerivAt
  · rfl
  · apply Continuous.aestronglyMeasurable
    have :
      (fun t ↦ fderiv ℝ (fun x : H ↦ F x t) x₀) =
        (fun φ : H × ℝ →L[ℝ] E ↦ φ.comp (inl ℝ H ℝ)) ∘
          (fderiv ℝ <| uncurry F) ∘ fun t ↦ (x₀, t) := by
      ext t
      have : HasFDerivAt (fun e ↦ F e t) ((fderiv ℝ (uncurry F) (x₀, t)).comp (inl ℝ H ℝ)) x₀ :=
        (hF.hasStrictFDerivAt le_rfl).hasFDerivAt.comp _ (hasFDerivAt_prod_mk_left _ _)
      rw [this.fderiv]
      rfl
    rw [this]; clear this
    exact
      (inl ℝ H ℝ).compRightL.continuous.comp
        ((hF.continuous_fderiv le_rfl).comp <| Continuous.Prod.mk x₀)
  · simp_rw [ae_restrict_iff' measurableSet_Ioo]
    refine eventually_of_forall fun t t_in ↦ ?_
    rw [nnabs_coe K]
    exact F_lip t t_in
  · exact integrableOn_const.mpr (Or.inr measure_Ioo_lt_top)

end

section

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {H : Type _}
  [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]

open Real ContinuousLinearMap Asymptotics

local notation:70 u " ⬝ " φ => ContinuousLinearMap.comp (ContinuousLinearMap.toSpanSingleton ℝ u) φ

theorem contDiff_parametric_primitive_of_contDiff' {F : H → ℝ → E} {n : ℕ} (hF : ContDiff ℝ n ↿F)
    {s : H → ℝ} (hs : ContDiff ℝ n s) (a : ℝ) : ContDiff ℝ n fun x : H ↦ ∫ t in a..s x, F x t := by
  induction' n with n ih generalizing F
  · rw [Nat.cast_zero, contDiff_zero] at *
    exact continuous_parametric_intervalIntegral_of_continuous hF hs
  · have hF₁ : ContDiff ℝ 1 ↿F := hF.one_of_succ
    have hs₁ : ContDiff ℝ 1 s := hs.one_of_succ
    have h :
      ∀ x,
        HasFDerivAt (fun x ↦ ∫ t in a..s x, F x t)
          ((∫ t in a..s x, fderiv ℝ (fun x' ↦ F x' t) x) + F x (s x) ⬝ fderiv ℝ s x) x :=
      fun x ↦ (hasFDerivAt_parametric_primitive_of_contDiff' hF₁ hs₁ x a).2
    rw [contDiff_succ_iff_fderiv_apply]
    constructor
    · exact fun x₀ ↦ ⟨_, h x₀⟩
    · intro x
      rw [fderiv_eq h]
      apply ContDiff.add
      · simp only [ContinuousLinearMap.coe_coe]
        have hD' : ContDiff ℝ n ↿fun x₀ t ↦ fderiv ℝ (fun x ↦ F x t) x₀ :=
          ContDiff.fderiv (hF.comp₂ contDiff_snd contDiff_fst.snd) contDiff_fst le_rfl
        have hD : ContDiff ℝ n ↿fun x' a ↦ (fderiv ℝ (fun e ↦ F e a) x') x :=
          hD'.clm_apply contDiff_const
        convert ih hD hs.of_succ with x'
        refine ContinuousLinearMap.intervalIntegral_apply ?_ x
        exact (continuous_curry x' hD'.continuous).intervalIntegrable _ _
      · exact ((contDiff_succ_iff_fderiv.mp hs).2.smulRight
          (hF.of_succ.comp <| contDiff_id.prod hs.of_succ)).clm_apply contDiff_const

end

section

universe v u

variable {E : Type u}

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {H : Type v}
  [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]

-- Should we directly prove the version below?
@[fun_prop]
theorem contDiff_parametric_primitive_of_contDiff {F : H → ℝ → E} {n : ℕ∞} (hF : ContDiff ℝ n (fun (x,y) => F x y))
    {s : H → ℝ} (hs : ContDiff ℝ n s) (a : ℝ) : ContDiff ℝ n fun x : H ↦ ∫ t in a..s x, F x t := by
  induction n using WithTop.recTopCoe
  · rw [contDiff_top] at *
    exact fun n ↦ contDiff_parametric_primitive_of_contDiff' (hF n) (hs n) a
  · exact contDiff_parametric_primitive_of_contDiff' hF hs a

theorem contDiff_parametric_primitive_of_contDiff'' {F : H → ℝ → E} {n : ℕ∞} (hF : ContDiff ℝ n ↿F)
    (a : ℝ) : ContDiff ℝ n fun x : H × ℝ ↦ ∫ t in a..x.2, F x.1 t :=
  have cd : ContDiff ℝ n ↿fun (x : H × ℝ) (t : ℝ) ↦ F x.1 t :=
    hF.comp (contDiff_fst.prod_map contDiff_id)
  contDiff_parametric_primitive_of_contDiff cd contDiff_snd a

theorem contDiff_parametric_integral_of_contDiff {F : H → ℝ → E} {n : ℕ∞} (hF : ContDiff ℝ n ↿F)
    (a b : ℝ) : ContDiff ℝ n fun x : H ↦ ∫ t in a..b, F x t :=
  contDiff_parametric_primitive_of_contDiff hF contDiff_const a

theorem ContDiff.fderiv_parametric_integral {F : H → ℝ → E} (hF : ContDiff ℝ 1 ↿F) (a b : ℝ) :
    (fderiv ℝ fun x : H ↦ ∫ t in a..b, F x t) = fun x : H ↦
      ∫ t in a..b, fderiv ℝ (fun x' ↦ F x' t) x := by
  ext x₀
  cases' hasFDerivAt_parametric_primitive_of_contDiff' hF contDiff_const x₀ a with int h
  rw [h.fderiv, fderiv_const]
  simp only [ContinuousLinearMap.comp_zero, add_zero, Pi.zero_apply]

end
