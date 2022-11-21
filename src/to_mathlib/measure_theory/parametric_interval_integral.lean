import measure_theory.integral.interval_integral
import analysis.calculus.parametric_integral
import algebra.module.ulift

import to_mathlib.analysis.calculus

open topological_space measure_theory filter first_countable_topology metric set function
open_locale topological_space filter nnreal big_operators interval

lemma ae_strongly_measurable_interval_oc_iff {α β : Type*} [measurable_space α] [linear_order α]
  [topological_space β] [metrizable_space β] {μ : measure α}
  {f : α → β} {a b : α} :
  (ae_strongly_measurable f $ μ.restrict $ Ι a b) ↔
    (ae_strongly_measurable f $ μ.restrict $ Ioc a b)
      ∧ (ae_strongly_measurable f $ μ.restrict $ Ioc b a) :=
by rw [interval_oc_eq_union, ae_strongly_measurable_union_iff]

section
variables {E : Type*} [normed_add_comm_group E] [normed_space ℝ E] [complete_space E]
  {H : Type*} [normed_add_comm_group H] [normed_space ℝ H]
  (ν : measure ℝ)

/-- Interval version of `has_fderiv_at_of_dominated_of_fderiv_le` -/
lemma has_fderiv_at_of_dominated_of_fderiv_le'' {F : H → ℝ → E} {F' : H → ℝ → (H →L[ℝ] E)} {x₀ : H}
  {a b : ℝ}
  {bound : ℝ → ℝ}
  {ε : ℝ}
  (ε_pos : 0 < ε)
  (hF_meas : ∀ᶠ x in 𝓝 x₀, ae_strongly_measurable (F x) $ ν.restrict (Ι a b))
  (hF_int : interval_integrable (F x₀) ν a b)
  (hF'_meas : ae_strongly_measurable (F' x₀) $ ν.restrict (Ι a b))
  (h_bound : ∀ᵐ t ∂ν.restrict (Ι a b), ∀ x ∈ ball x₀ ε, ‖F' x t‖ ≤ bound t)
  (bound_integrable : interval_integrable bound ν a b)
  (h_diff : ∀ᵐ t ∂ν.restrict (Ι a b), ∀ x ∈ ball x₀ ε, has_fderiv_at (λ x, F x t) (F' x t) x) :
  has_fderiv_at (λ x, ∫ t in a..b, F x t ∂ν) (∫ t in a..b, F' x₀ t ∂ν) x₀ :=
begin
  erw ae_restrict_interval_oc_iff at h_diff h_bound,
  simp_rw [ae_strongly_measurable_interval_oc_iff, eventually_and] at hF_meas hF'_meas,
  exact (has_fderiv_at_integral_of_dominated_of_fderiv_le ε_pos
          hF_meas.1 hF_int.1 hF'_meas.1 h_bound.1 bound_integrable.1 h_diff.1).sub
        (has_fderiv_at_integral_of_dominated_of_fderiv_le ε_pos
          hF_meas.2 hF_int.2 hF'_meas.2 h_bound.2 bound_integrable.2 h_diff.2)
end

/-- Interval version of `has_fderiv_at_of_dominated_loc_of_lip` -/
lemma has_fderiv_at_of_dominated_loc_of_lip_interval {F : H → ℝ → E} {F' : ℝ → (H →L[ℝ] E)} {x₀ : H}
  {a b : ℝ}
  {bound : ℝ → ℝ}
  {ε : ℝ} (ε_pos : 0 < ε)
  (hF_meas : ∀ᶠ x in 𝓝 x₀, ae_strongly_measurable (F x) $ ν.restrict (Ι a b))
  (hF_int : interval_integrable (F x₀) ν a b)
  (hF'_meas : ae_strongly_measurable F' $ ν.restrict (Ι a b))
  (h_lip : ∀ᵐ t ∂(ν.restrict (Ι a b)),
    lipschitz_on_with (real.nnabs $ bound t) (λ x, F x t) (ball x₀ ε))
  (bound_integrable : interval_integrable bound ν a b)
  (h_diff : ∀ᵐ t ∂(ν.restrict (Ι a b)), has_fderiv_at (λ x, F x t) (F' t) x₀) :
  interval_integrable F' ν a b ∧
  has_fderiv_at (λ x, ∫ t in a..b, F x t ∂ν) (∫ t in a..b, F' t ∂ν) x₀ :=
begin
  simp_rw [ae_strongly_measurable_interval_oc_iff, eventually_and] at hF_meas hF'_meas,
  rw ae_restrict_interval_oc_iff at h_lip h_diff,
  have H₁ := has_fderiv_at_integral_of_dominated_loc_of_lip ε_pos hF_meas.1 hF_int.1 hF'_meas.1
    h_lip.1 bound_integrable.1 h_diff.1,
  have H₂ := has_fderiv_at_integral_of_dominated_loc_of_lip ε_pos hF_meas.2 hF_int.2 hF'_meas.2
    h_lip.2 bound_integrable.2 h_diff.2,
  exact ⟨⟨H₁.1, H₂.1⟩, H₁.2.sub H₂.2⟩
end

end

section

open function

theorem continuous_parametric_integral_of_continuous
  {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
  [complete_space E]
  {α : Type*} [topological_space α] [measurable_space α] [opens_measurable_space α]
  [second_countable_topology_either α E]
  {μ : measure_theory.measure α} [is_locally_finite_measure μ]
  {X : Type*} [topological_space X] [first_countable_topology X] [locally_compact_space X]
  {F : X → α → E} (hF : continuous (λ p : X × α, F p.1 p.2))
  {s : set α} (hs : is_compact s) :
  continuous (λ x, ∫ a in s, F x a ∂μ) :=
begin
  rw continuous_iff_continuous_at,
  intros x₀,
  rcases exists_compact_mem_nhds x₀ with ⟨U, U_cpct, U_nhds⟩,
  rcases (U_cpct.prod hs).bdd_above_image hF.norm.continuous_on with ⟨M, hM⟩,
  apply continuous_at_of_dominated,
  { exact eventually_of_forall (λ x, (hF.comp (continuous.prod.mk x)).ae_strongly_measurable) },
  { apply eventually.mono U_nhds (λ x x_in, _),
    rw [ae_restrict_iff],
    exact eventually_of_forall (λ t t_in, hM (mem_image_of_mem _ $ mk_mem_prod x_in t_in)),
    exact (is_closed_le (hF.comp $ continuous.prod.mk x).norm continuous_const).measurable_set },
  { exact integrable_on_const.mpr (or.inr hs.measure_lt_top), },
  { apply ae_of_all,
    intros a,
    apply (hF.comp₂ continuous_id continuous_const).continuous_at }
end

end


section

open measure_theory

variables {μ : measure ℝ}
          {X : Type*} [topological_space X] [first_countable_topology X]
          {E : Type*} [normed_add_comm_group E] [normed_space ℝ E] [complete_space E]

lemma continuous_at_parametric_primitive_of_dominated
  {F : X → ℝ → E} (bound : ℝ → ℝ) (a b : ℝ) {a₀ b₀ : ℝ} {x₀ : X}
  (hF_meas : ∀ x, ae_strongly_measurable (F x) (μ.restrict $ Ι a b))
  (h_bound : ∀ᶠ x in 𝓝 x₀, ∀ᵐ t ∂(μ.restrict $ Ι a b), ‖F x t‖ ≤ bound t)
  (bound_integrable : interval_integrable bound μ a b)
  (h_cont : ∀ᵐ t ∂(μ.restrict $ Ι a b), continuous_at (λ x, F x t) x₀)
  (ha₀ : a₀ ∈ Ioo a b) (hb₀ : b₀ ∈ Ioo a b) (hμb₀ : μ {b₀} = 0) :
  continuous_at (λ p : X × ℝ, ∫ (t : ℝ) in a₀..p.2, F p.1 t ∂μ) (x₀, b₀) :=
begin
  have hsub : ∀ {a₀ b₀}, a₀ ∈ Ioo a b → b₀ ∈ Ioo a b → Ι a₀ b₀ ⊆ Ι a b :=
    λ a₀ b₀ ha₀ hb₀, (ord_connected_Ioo.interval_oc_subset ha₀ hb₀).trans
      (Ioo_subset_Ioc_self.trans Ioc_subset_interval_oc),
  have Ioo_nhds : Ioo a b ∈ 𝓝 b₀ := Ioo_mem_nhds hb₀.1 hb₀.2,
  have Icc_nhds : Icc a b ∈ 𝓝 b₀ := Icc_mem_nhds hb₀.1 hb₀.2,
  have hx₀ : ∀ᵐ (t : ℝ) ∂μ.restrict (Ι a b), ‖F x₀ t‖ ≤ bound t := h_bound.self_of_nhds,
  have : ∀ᶠ (p : X × ℝ) in 𝓝 (x₀, b₀),
    ∫ s in a₀..p.2, F p.1 s ∂μ = ∫ s in a₀..b₀, F p.1 s ∂μ + ∫ s in b₀..p.2, F x₀ s ∂μ +
                                 ∫ s in b₀..p.2, (F p.1 s - F x₀ s) ∂μ,
  { rw nhds_prod_eq,
    refine (h_bound.prod_mk Ioo_nhds).mono _,
    rintros ⟨x, t⟩ ⟨hx : ∀ᵐ (t : ℝ) ∂μ.restrict (Ι a b), ‖F x t‖ ≤ bound t, ht : t ∈ Ioo a b⟩,
    dsimp {eta := ff},
    have hiF : ∀ {x a₀ b₀}, (∀ᵐ (t : ℝ) ∂μ.restrict (Ι a b), ‖F x t‖ ≤ bound t) →
      a₀ ∈ Ioo a b → b₀ ∈ Ioo a b → interval_integrable (F x) μ a₀ b₀ :=
    λ x a₀ b₀ hx ha₀ hb₀,
      (bound_integrable.mono_set_ae $ eventually_of_forall $ hsub ha₀ hb₀).mono_fun'
        ((hF_meas x).mono_set $ hsub ha₀ hb₀)
        (ae_restrict_of_ae_restrict_of_subset (hsub ha₀ hb₀) hx),
    rw [interval_integral.integral_sub, add_assoc, add_sub_cancel'_right,
        interval_integral.integral_add_adjacent_intervals],
    { exact hiF hx ha₀ hb₀ },
    { exact hiF hx hb₀ ht },
    { exact hiF hx hb₀ ht },
    { exact hiF hx₀ hb₀ ht } },
  rw continuous_at_congr this, clear this,
  refine (continuous_at.add _ _).add _,
  { exact (interval_integral.continuous_at_of_dominated_interval
            (eventually_of_forall $ λ x, (hF_meas x).mono_set $ hsub ha₀ hb₀)
            (h_bound.mono $ λ x hx,
              ae_imp_of_ae_restrict $ ae_restrict_of_ae_restrict_of_subset (hsub ha₀ hb₀) hx)
            (bound_integrable.mono_set_ae $ eventually_of_forall $ hsub ha₀ hb₀) $
            ae_imp_of_ae_restrict $ ae_restrict_of_ae_restrict_of_subset (hsub ha₀ hb₀) h_cont).fst' },
  { refine (_ : continuous_at (λ t, ∫ s in b₀..t, F x₀ s ∂μ) b₀).snd',
    apply continuous_within_at.continuous_at _ (Icc_mem_nhds hb₀.1 hb₀.2),
    apply interval_integral.continuous_within_at_primitive hμb₀,
    rw [min_eq_right hb₀.1.le, max_eq_right hb₀.2.le],
    exact bound_integrable.mono_fun' (hF_meas x₀) hx₀ },
  { suffices : tendsto (λ (x : X × ℝ), ∫ s in b₀..x.2, F x.1 s - F x₀ s ∂μ) (𝓝 (x₀, b₀)) (𝓝 0),
      by simpa [continuous_at],
    have : ∀ᶠ p : X × ℝ in 𝓝 (x₀, b₀),
      ‖∫ s in b₀..p.2, F p.1 s - F x₀ s ∂μ‖ ≤ |∫ s in b₀..p.2, 2 * bound s ∂μ|,
    { rw nhds_prod_eq,
      refine (h_bound.prod_mk Ioo_nhds).mono _,
      rintros ⟨x, t⟩ ⟨hx : ∀ᵐ t ∂μ.restrict (Ι a b), ‖F x t‖ ≤ bound t, ht : t ∈ Ioo a b⟩,
      have H : ∀ᵐ (t : ℝ) ∂μ.restrict (Ι b₀ t), ‖F x t - F x₀ t‖ ≤ 2 * bound t,
      { apply (ae_restrict_of_ae_restrict_of_subset (hsub hb₀ ht) (hx.and hx₀)).mono,
        rintros s ⟨hs₁, hs₂⟩,
        calc ‖F x s - F x₀ s‖ ≤ ‖F x s‖ + ‖F x₀ s‖ : norm_sub_le _ _
          ... ≤ 2 * bound s : by linarith only [hs₁, hs₂] },
      exact interval_integral.norm_integral_le_of_norm_le H
        ((bound_integrable.mono_set' $ hsub hb₀ ht).const_mul 2) },
    apply squeeze_zero_norm' this,
    have : tendsto (λ t, ∫ s in b₀..t, 2 * bound s ∂μ) (𝓝 b₀) (𝓝 0),
    { suffices : continuous_at (λ t, ∫ s in b₀..t, 2 * bound s ∂μ) b₀,
      { convert this, simp },
      apply continuous_within_at.continuous_at _ Icc_nhds,
      apply interval_integral.continuous_within_at_primitive hμb₀,
      apply interval_integrable.const_mul,
      apply bound_integrable.mono_set',
      rw [min_eq_right hb₀.1.le, max_eq_right hb₀.2.le] },
    rw nhds_prod_eq,
    exact (continuous_abs.tendsto' _ _ abs_zero).comp (this.comp tendsto_snd) },
end
end

section
variables {μ : measure ℝ}
          [is_locally_finite_measure μ] [has_no_atoms μ]
          {X : Type*} [topological_space X] [first_countable_topology X]
          {E : Type*} [normed_add_comm_group E] [normed_space ℝ E] [complete_space E]

lemma continuous_parametric_primitive_of_continuous
  [locally_compact_space X]
  {F : X → ℝ → E} {a₀ : ℝ}
  (hF : continuous (λ p : X × ℝ, F p.1 p.2)) :
  continuous (λ p : X × ℝ, ∫ t in a₀..p.2, F p.1 t ∂μ) :=
begin
  rw continuous_iff_continuous_at,
  rintros ⟨x₀, b₀⟩,
  rcases exists_compact_mem_nhds x₀ with ⟨U, U_cpct, U_nhds⟩,
  cases exists_lt (min a₀ b₀) with a a_lt,
  cases exists_gt (max a₀ b₀) with b lt_b,
  rw lt_min_iff at a_lt,
  rw max_lt_iff at lt_b,
  have a₀_in : a₀ ∈ Ioo a b := ⟨a_lt.1, lt_b.1⟩,
  have b₀_in : b₀ ∈ Ioo a b := ⟨a_lt.2, lt_b.2⟩,
  obtain ⟨M, hM⟩ :=
    (U_cpct.prod (is_compact_Icc : is_compact $ Icc a b)).bdd_above_image hF.norm.continuous_on,
  refine continuous_at_parametric_primitive_of_dominated (λ t, M) a b _ _ _ _ a₀_in b₀_in
    (measure_singleton b₀),
  { exact λ x, (hF.comp (continuous.prod.mk x)).ae_strongly_measurable },
  { apply eventually.mono U_nhds (λ x (x_in : x ∈ U), _),
    simp_rw [ae_restrict_iff' measurable_set_interval_oc],
    refine eventually_of_forall (λ t t_in, _),
    refine hM (mem_image_of_mem _ $ mk_mem_prod x_in _),
    rw interval_oc_of_le (a_lt.1.trans lt_b.1).le at t_in,
    exact mem_Icc_of_Ioc t_in },
  { apply interval_integrable_const },
  { apply ae_of_all,
    intros a,
    apply (hF.comp₂ continuous_id continuous_const).continuous_at }
end

theorem continuous_parametric_interval_integral_of_continuous
  [locally_compact_space X] {a₀ : ℝ}
  {F : X → ℝ → E} (hF : continuous (λ p : X × ℝ, F p.1 p.2))
  {s : X → ℝ} (hs : continuous s) :
  continuous (λ x, ∫ t in a₀..s x, F x t ∂μ) :=
show continuous ((λ p : X × ℝ, ∫ t in a₀..p.2, F p.1 t ∂μ) ∘ (λ x, (x, s x))),
from (continuous_parametric_primitive_of_continuous hF).comp₂ continuous_id hs

theorem continuous_parametric_interval_integral_of_continuous'
  [locally_compact_space X]
  {F : X → ℝ → E} (hF : continuous (λ p : X × ℝ, F p.1 p.2)) (a₀ b₀ : ℝ) :
  continuous (λ x, ∫ t in a₀..b₀, F x t ∂μ) :=
continuous_parametric_interval_integral_of_continuous hF continuous_const


end


section
variables {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
          [complete_space E]
          {H : Type*} [normed_add_comm_group H] [normed_space ℝ H]

/-!
We could weaken `finite_dimensional ℝ H` with `second_countable (H →L[ℝ] E)` if needed,
but that is less convenient to work with.
-/

open real continuous_linear_map asymptotics

/--
This statement is a new version using the continuity note in mathlib.
See commit `39e3f3f` for an older version
Maybe todo: let `a` depend on `x`.
-/
lemma has_fderiv_at_parametric_primitive_of_lip' (F : H → ℝ → E) (F' : ℝ → (H →L[ℝ] E)) {x₀ : H}
  {G' : H →L[ℝ] E}
  {bound : ℝ → ℝ}
  {s : H → ℝ}
  {ε : ℝ} (ε_pos : 0 < ε)
  {a a₀ b₀ : ℝ}
  {s' : H →L[ℝ] ℝ}
  (ha :  a ∈ Ioo a₀ b₀)
  (hsx₀ : s x₀ ∈ Ioo a₀ b₀)
  (hF_meas : ∀ x ∈ ball x₀ ε, ae_strongly_measurable (F x) (volume.restrict (Ioo a₀ b₀)))
  (hF_int : integrable_on (F x₀) (Ioo a₀ b₀))
  (hF_cont : continuous_at (F x₀) (s x₀))
  (hF'_meas : ae_strongly_measurable F' (volume.restrict $ Ι a (s x₀)))
  (h_lipsch : ∀ᵐ t ∂(volume.restrict $ Ioo a₀ b₀),
    lipschitz_on_with (nnabs $ bound t) (λ x, F x t) (ball x₀ ε))
  (bound_integrable : integrable_on bound (Ioo a₀ b₀))
  (bound_cont : continuous_at bound (s x₀))
  (bound_nonneg : ∀ t, 0 ≤ bound t) -- this is not really needed, but much more convenient
  (h_diff : ∀ᵐ a ∂volume.restrict (Ι a (s x₀)), has_fderiv_at (λ x, F x a) (F' a) x₀)
  (s_diff : has_fderiv_at s s' x₀)
  (hG' : (∫ t in a..s x₀, F' t) + (to_span_singleton ℝ (F x₀ (s x₀))).comp s' = G') :
  interval_integrable F' volume a (s x₀) ∧
  has_fderiv_at (λ x : H, ∫ t in a..s x, F x t) G' x₀ :=
begin
  subst hG',
  let φ : H → ℝ → E := λ x t, ∫ s in a..t, F x s,
  let ψ : H →L[ℝ] E := ∫ t in a..s x₀, F' t,
  have Ioo_nhds : Ioo a₀ b₀ ∈ 𝓝 (s x₀) := Ioo_mem_nhds hsx₀.1 hsx₀.2,
  have bound_int : ∀ {s u}, s ∈ Ioo a₀ b₀ → u ∈ Ioo a₀ b₀ → interval_integrable bound volume s u,
  { intros s u hs hu,
    exact (bound_integrable.mono_set $ ord_connected_Ioo.interval_subset hs hu).interval_integrable },
  have mem_nhds : ball x₀ ε ∩ (s ⁻¹' Ioo a₀ b₀) ∈ 𝓝 x₀ :=
  filter.inter_mem (ball_mem_nhds x₀ ε_pos) (s_diff.continuous_at.preimage_mem_nhds Ioo_nhds),
  have x₀_in : x₀ ∈ ball x₀ ε := mem_ball_self ε_pos,
  have hF_meas_ball : ∀ {x}, x ∈ ball x₀ ε → ∀ {s u}, s ∈ Ioo a₀ b₀ → u ∈ Ioo a₀ b₀ →
    ae_strongly_measurable (F x) (volume.restrict $ Ι s u),
  { intros x hx s u hs hu,
    exact (hF_meas x hx).mono_set (ord_connected_Ioo.interval_oc_subset hs hu) },
  have hF_int_ball : ∀ x ∈ ball x₀ ε, ∀ {s u}, s ∈ Ioo a₀ b₀ → u ∈ Ioo a₀ b₀ →
    interval_integrable (F x) volume s u,
  { intros x hx s u hs hu,
    have : integrable_on (F x) (Ioo a₀ b₀),
    { apply integrable_of_norm_sub_le (hF_meas x hx) hF_int (bound_integrable.mul_const (‖x - x₀‖)),
      apply h_lipsch.mono,
      intros t ht,
      rw norm_sub_rev,
      rw lipschitz_on_with_iff_norm_sub_le at ht,
      simpa [bound_nonneg t] using ht hx x₀_in },
    exact (this.mono_set $ ord_connected_Ioo.interval_subset hs hu).interval_integrable },
  split,
  { apply (bound_int ha hsx₀).mono_fun' hF'_meas _,
    replace h_lipsch : ∀ᵐ t ∂volume.restrict (Ι a (s x₀)),
      lipschitz_on_with (nnabs (bound t)) (λ (x : H), F x t) (ball x₀ ε),
      from ae_restrict_of_ae_restrict_of_subset
        (ord_connected_Ioo.interval_oc_subset ha hsx₀) h_lipsch,
    filter_upwards [h_lipsch, h_diff],
    intros t ht_lip ht_diff,
    rw show bound t = nnabs (bound t), by simp [bound_nonneg t],
    exact ht_diff.le_of_lip (ball_mem_nhds x₀ ε_pos) ht_lip },
  { have D₁ : has_fderiv_at (λ x, φ x (s x₀)) (∫ t in a..s x₀, F' t) x₀,
    { replace hF_meas : ∀ᶠ x in 𝓝 x₀, ae_strongly_measurable (F x) (volume.restrict (Ι a (s x₀))),
        from eventually.mono (ball_mem_nhds x₀ ε_pos) (λ x hx, hF_meas_ball hx ha hsx₀),
      replace hF_int : interval_integrable (F x₀) volume a (s x₀) := hF_int_ball x₀ x₀_in ha hsx₀,
      exact (has_fderiv_at_of_dominated_loc_of_lip_interval _ ε_pos hF_meas hF_int hF'_meas
        (ae_restrict_of_ae_restrict_of_subset (ord_connected_Ioo.interval_oc_subset ha hsx₀) h_lipsch)
        (bound_int ha hsx₀) h_diff).2 },
    have D₂ : has_fderiv_at (λ x, φ x₀ (s x)) ((to_span_singleton ℝ (F x₀ (s x₀))).comp s') x₀,
    { refine has_fderiv_at.comp _ _ s_diff,
      rw [has_fderiv_at_iff_has_deriv_at, to_span_singleton_apply, one_smul],
      exact interval_integral.integral_has_deriv_at_right (hF_int_ball x₀ x₀_in ha hsx₀)
        ⟨Ioo a₀ b₀, Ioo_nhds, (hF_meas x₀ x₀_in)⟩ hF_cont },
    have D₃ : has_fderiv_at (λ x, ∫ t in s x₀..s x, F x t - F x₀ t) 0 x₀,
    { apply is_O.has_fderiv_at _ one_lt_two,
      have O₁ : (λ x, ∫ s in s x₀..s x, bound s) =O[𝓝 x₀] λ x, ‖x - x₀‖,
      { have : (λ x, s x - s x₀) =O[𝓝 x₀] λ x, ‖x - x₀‖ := s_diff.is_O_sub.norm_right,
        refine is_O.trans _ this,
        show ((λ t, ∫ s in s x₀..t, bound s) ∘ s) =O[𝓝 x₀] ((λ t, t - s x₀) ∘ s),
        refine is_O.comp_tendsto _ s_diff.continuous_at,
        have M : strongly_measurable_at_filter bound (𝓝 (s x₀)) volume,
        { use [Ioo a₀ b₀, Ioo_nhds, bound_integrable.1] },
        refine (interval_integral.integral_has_deriv_at_right (bound_int ha hsx₀) M bound_cont)
          .has_fderiv_at.is_O.congr' _ eventually_eq.rfl,
        apply eventually.mono Ioo_nhds,
        rintros t ht,
        dsimp only {eta := false},
        rw interval_integral.integral_interval_sub_left (bound_int ha ht) (bound_int ha hsx₀) },
      have O₂ : (λ x, ‖x - x₀‖) =O[𝓝 x₀] λ x, ‖x - x₀‖ := is_O_refl _ _,
      have O₃ : (λ x, ∫ (t : ℝ) in s x₀..s x, F x t - F x₀ t) =O[𝓝 x₀]
             λ x, (∫ t' in s x₀..s x, bound t') * ‖x - x₀‖,
      { have bdd : ∀ᶠ x in 𝓝 x₀,
          ‖∫ s in s x₀..s x, F x s - F x₀ s‖ ≤ |∫ s in s x₀..s x, bound s |* ‖x - x₀‖,
        { apply eventually.mono mem_nhds,
          rintros x ⟨hx : x ∈ ball x₀ ε, hsx : s x ∈ Ioo a₀ b₀⟩,
          rw [← abs_of_nonneg (norm_nonneg $ x - x₀), ← abs_mul,
            ← interval_integral.integral_mul_const],
          apply interval_integral.norm_integral_le_of_norm_le _ ((bound_int hsx₀ hsx).mul_const _),
          apply ae_restrict_of_ae_restrict_of_subset (ord_connected_Ioo.interval_oc_subset hsx₀ hsx),
          apply h_lipsch.mono,
          intros t ht,
          rw lipschitz_on_with_iff_norm_sub_le at ht,
          simp only [coe_nnabs] at ht,
          rw ← abs_of_nonneg (bound_nonneg t),
          exact ht hx (mem_ball_self ε_pos) },
        rw ← is_O_norm_right,
        simp only [norm_eq_abs, abs_mul, abs_norm_eq_norm],
        exact bdd.is_O },
      simp_rw pow_two,
      exact O₃.trans (O₁.mul O₂) },
    have : ∀ᶠ x in 𝓝 x₀, ∫ t in a..s x, F x t =
      φ x (s x₀) + φ x₀ (s x) + (∫ t in s x₀..s x, F x t - F x₀ t) - φ x₀ (s x₀),
    { apply eventually.mono mem_nhds,
      rintros x ⟨hx : x ∈ ball x₀ ε, hsx : s x ∈ Ioo a₀ b₀⟩,
      have int₁ : interval_integrable (F x₀) volume a (s x₀) := hF_int_ball x₀ x₀_in ha hsx₀,
      have int₂ : interval_integrable (F x₀) volume (s x₀) (s x) := hF_int_ball x₀ x₀_in hsx₀ hsx,
      have int₃ : interval_integrable (F x) volume a (s x₀) := hF_int_ball x hx ha hsx₀,
      have int₄ : interval_integrable (F x) volume (s x₀) (s x) := hF_int_ball x hx hsx₀ hsx,
      dsimp [φ] {eta := ff},
      rw [interval_integral.integral_sub int₄ int₂, add_sub,
          add_right_comm, sub_sub, interval_integral.integral_add_adjacent_intervals int₃ int₄],
      conv_rhs { congr, skip, rw add_comm },
      rw interval_integral.integral_add_adjacent_intervals int₁ int₂,
      abel },
    apply has_fderiv_at.congr_of_eventually_eq _ this,
    simpa using ((D₁.add D₂).add D₃).sub (has_fderiv_at_const (φ x₀ (s x₀)) x₀) }
end

local notation u ` ⬝ `:70 φ :=  continuous_linear_map.comp (continuous_linear_map.to_span_singleton ℝ u) φ

variable [finite_dimensional ℝ H]

/-
A version of the above lemma using Floris' style statement. This does not reuse the above lemma, but copies the proof.
-/

lemma has_fderiv_at_parametric_primitive_of_cont_diff' {F : H → ℝ → E} (hF : cont_diff ℝ 1 ↿F)
  {s : H → ℝ} (hs : cont_diff ℝ 1 s)
  (x₀ : H) (a : ℝ) :
  (interval_integrable (λ t, fderiv ℝ (λ x, F x t) x₀) volume a $ s x₀) ∧
  has_fderiv_at (λ x : H, ∫ t in a..s x, F x t)
    ((∫ t in a..s x₀, fderiv ℝ (λ x, F x t) x₀) + F x₀ (s x₀) ⬝ fderiv ℝ s x₀)
    x₀ :=
begin
  set a₀ :=  min a (s x₀) - 1,
  set b₀ :=  max a (s x₀) + 1,
  have ha : a ∈ Ioo a₀ b₀,
  { dsimp [a₀, b₀],
    split,
    linarith [min_le_left a (s x₀)],
    linarith [le_max_left a (s x₀)] },
  have ht₀ : s x₀ ∈ Ioo a₀ b₀,
  { dsimp [a₀, b₀],
    split,
    linarith [min_le_right a (s x₀)],
    linarith [le_max_right a (s x₀)] },
  have cpct : is_compact (closed_ball x₀ 1 ×ˢ Icc a₀ b₀),
      from (proper_space.is_compact_closed_ball x₀ 1).prod is_compact_Icc,
  obtain ⟨M, F_bound⟩ : ∃ M : ℝ, ∀ x ∈ ball x₀ 1, ∀ t ∈ Ioo a₀ b₀, ‖F x t‖ ≤ M,
  { rcases cpct.bdd_above_image hF.continuous.norm.continuous_on with ⟨M, hM⟩,
    refine ⟨M, _⟩,
    exact λ x x_in t t_in, hM (mem_image_of_mem _ $ mk_mem_prod (ball_subset_closed_ball x_in) $
      mem_Icc_of_Ioo t_in) },
  obtain ⟨K, F_lip⟩ : ∃ K, ∀ t ∈ Ioo a₀ b₀, lipschitz_on_with K (λ x, F x t) (ball x₀ 1),
  { have conv : convex ℝ (closed_ball x₀ 1 ×ˢ Icc a₀ b₀),
      from (convex_closed_ball x₀ 1).prod (convex_Icc a₀ b₀),
    rcases hF.lipschitz_on_with le_rfl conv cpct with ⟨K, hK⟩,
    use K,
    intros t t_in,
    rw [show (λ (x : H), F x t) = (uncurry F) ∘ (λ x : H, (x, t)), by { ext, simp }, ← mul_one K],
    apply hK.comp ((lipschitz_with.prod_mk_right t).lipschitz_on_with $ ball x₀ 1),
    rw maps_to',
    rintros ⟨x, s⟩ ⟨x', hx, h⟩, cases h,
    refine ⟨ball_subset_closed_ball hx, mem_Icc_of_Ioo t_in⟩ },
  have cont_x : ∀ x, continuous (F x),
    from λ x, hF.continuous.comp (continuous.prod.mk x),
  have int_Icc : ∀ x, integrable_on (F x) (Icc a₀ b₀),
    from λ x, (cont_x x).locally_integrable is_compact_Icc,
  have int_Ioo : ∀ x, integrable_on (F x) (Ioo a₀ b₀),
    from λ x, (int_Icc x).mono_set Ioo_subset_Icc_self,
  apply has_fderiv_at_parametric_primitive_of_lip' _ _ zero_lt_one ha ht₀
    (λ x hx, (cont_x x).ae_strongly_measurable) (int_Ioo x₀) (cont_x x₀).continuous_at
    _ _ _ (continuous_at_const : continuous_at (λ (t : ℝ), (K : ℝ)) $ s x₀) (λ t, nnreal.coe_nonneg K),
  { apply ae_of_all,
    intro t,
    apply (cont_diff.has_strict_fderiv_at _ le_rfl).has_fderiv_at,
    rw show (λ x, F x t) = (uncurry F) ∘ (λ x, (x, t)), by { ext, simp },
    exact hF.comp ((cont_diff_prod_mk_left t).of_le le_top) },
  { exact (cont_diff.has_strict_fderiv_at hs le_rfl).has_fderiv_at },
  { refl },
  { apply continuous.ae_strongly_measurable,
    have : (λ t, fderiv ℝ (λ (x : H), F x t) x₀) =
      ((λ φ : H × ℝ →L[ℝ] E, φ.comp (inl ℝ H ℝ)) ∘ (fderiv ℝ $ uncurry F) ∘ (λ t, (x₀, t))),
    { ext t,
      have : has_fderiv_at (λ e, F e t) ((fderiv ℝ (uncurry F) (x₀, t)).comp (inl ℝ H ℝ)) x₀ :=
        (hF.has_strict_fderiv_at le_rfl).has_fderiv_at.comp _ (has_fderiv_at_prod_mk_left _ _),
      rw [this.fderiv] },
    rw this, clear this,
    exact (inl ℝ H ℝ).comp_rightL.continuous.comp ((hF.continuous_fderiv le_rfl).comp $
      continuous.prod.mk x₀) },
  { simp_rw [ae_restrict_iff' measurable_set_Ioo],
    refine eventually_of_forall (λ t t_in, _),
    rw nnabs_coe K,
    exact F_lip t t_in },
  { exact integrable_on_const.mpr (or.inr measure_Ioo_lt_top) }
end

end

section
variables {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
          [complete_space E]
          {H : Type*} [normed_add_comm_group H] [normed_space ℝ H]
          [finite_dimensional ℝ H]

open real continuous_linear_map asymptotics

local notation u ` ⬝ `:70 φ :=  continuous_linear_map.comp (continuous_linear_map.to_span_singleton ℝ u) φ

lemma cont_diff_parametric_primitive_of_cont_diff' {F : H → ℝ → E} {n : ℕ}
  (hF : cont_diff ℝ n ↿F)
  {s : H → ℝ} (hs : cont_diff ℝ n s)
  (a : ℝ) :
  cont_diff ℝ n (λ x : H, ∫ t in a..s x, F x t)  :=
begin
  induction n with n ih generalizing F,
  { rw [with_top.coe_zero, cont_diff_zero] at *,
    exact continuous_parametric_interval_integral_of_continuous hF hs },
  { have hF₁ : cont_diff ℝ 1 (↿F) := hF.one_of_succ,
    have hs₁ : cont_diff ℝ 1 s := hs.one_of_succ,
    have h : ∀ x, has_fderiv_at (λ x, ∫ t in a..s x, F x t)
      ((∫ t in a..s x, fderiv ℝ (λ x', F x' t) x) + F x (s x) ⬝ fderiv ℝ s x) x :=
    λ x, (has_fderiv_at_parametric_primitive_of_cont_diff' hF₁ hs₁ x a).2,
    rw cont_diff_succ_iff_fderiv_apply,
    split,
    { exact λ x₀, ⟨_, h x₀⟩ },
    { intro x,
      rw fderiv_eq h,
      apply cont_diff.add,
      { simp only [continuous_linear_map.coe_coe],
        have hD' : cont_diff ℝ n ↿(λ x₀ t, fderiv ℝ (λ x, F x t) x₀) :=
          cont_diff.fderiv (hF.comp₂ cont_diff_snd cont_diff_fst.snd) cont_diff_fst le_rfl,
        have hD : cont_diff ℝ n ↿(λ x' a, (fderiv ℝ (λ e, F e a) x') x) :=
          hD'.clm_apply cont_diff_const,
        convert ih hs.of_succ hD,
        ext x',
        refine continuous_linear_map.interval_integral_apply _ x,
        exact (continuous_curry x' hD'.continuous).interval_integrable _ _, },
      { exact ((cont_diff_succ_iff_fderiv.mp hs).2.smul_right
          (hF.of_succ.comp $ cont_diff_id.prod hs.of_succ)).clm_apply cont_diff_const } } }
end

end

section

universe variables v u

variables {E : Type u}
variables [normed_add_comm_group E] [normed_space ℝ E]
          [complete_space E]
          {H : Type v} [normed_add_comm_group H] [normed_space ℝ H]
          [finite_dimensional ℝ H]

/- Should we directly prove the version below?-/

lemma cont_diff_parametric_primitive_of_cont_diff
  {F : H → ℝ → E} {n : ℕ∞} (hF : cont_diff ℝ n ↿F)
  {s : H → ℝ} (hs : cont_diff ℝ n s)
  (a : ℝ) :
  cont_diff ℝ n (λ x : H, ∫ t in a..s x, F x t) :=
begin
  induction n using with_top.rec_top_coe,
  { rw cont_diff_top at *,
    exact λ n, cont_diff_parametric_primitive_of_cont_diff' (hF n) (hs n) a },
  { exact cont_diff_parametric_primitive_of_cont_diff' hF hs a },
end

lemma cont_diff_parametric_primitive_of_cont_diff''
  {F : H → ℝ → E} {n : ℕ∞} (hF : cont_diff ℝ n ↿F) (a : ℝ) :
  cont_diff ℝ n (λ x : H × ℝ, ∫ t in a..x.2, F x.1 t) :=
cont_diff_parametric_primitive_of_cont_diff (hF.comp (cont_diff_fst.prod_map cont_diff_id))
cont_diff_snd a

lemma cont_diff_parametric_integral_of_cont_diff
  {F : H → ℝ → E} {n : ℕ∞} (hF : cont_diff ℝ n ↿F)
  (a b : ℝ) :
  cont_diff ℝ n (λ x : H, ∫ t in a..b, F x t) :=
cont_diff_parametric_primitive_of_cont_diff hF cont_diff_const a

lemma cont_diff.fderiv_parametric_integral
  {F : H → ℝ → E} (hF : cont_diff ℝ 1 ↿F)
  (a b : ℝ) :
  fderiv ℝ (λ x : H, ∫ t in a..b, F x t) = λ x : H, (∫ t in a..b, fderiv ℝ (λ x', F x' t) x) :=
begin
  ext x₀,
  cases has_fderiv_at_parametric_primitive_of_cont_diff' hF cont_diff_const x₀ a with int h,
  rw [h.fderiv, fderiv_const],
  simp only [continuous_linear_map.comp_zero, add_zero, pi.zero_apply]
end

end
