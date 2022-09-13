import notations
import loops.reparametrization
import to_mathlib.analysis.cut_off
import to_mathlib.topology.hausdorff_distance

noncomputable theory

open set function finite_dimensional prod int topological_space metric filter
open measure_theory measure_theory.measure real
open_locale topological_space unit_interval

variables {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
          {F : Type*} [normed_add_comm_group F]
          {g b : E → F} {Ω : set (E × F)} {U K C : set E}
variables [normed_space ℝ F] [finite_dimensional ℝ F]

lemma exist_loops_aux1
  (hK : is_compact K)
  (hΩ_op : is_open Ω)
  (hb : 𝒞 ∞ b)
  (hgK : ∀ᶠ x near K, g x = b x)
  (hconv : ∀ x, g x ∈ hull (connected_component_in (prod.mk x ⁻¹' Ω) $ b x)) :
  ∃ (γ : E → ℝ → loop F) (V ∈ 𝓝ˢ K) (ε > 0), surrounding_family_in g b γ V Ω ∧
  (∀ (x ∈ V), ball (x, b x) (ε + ε) ⊆ Ω) ∧
  ∀ (x ∈ V) t s, dist (γ x t s) (b x) < ε :=
begin
  have b_in : ∀ x, (x, b x) ∈ Ω :=
    λ x, (connected_component_in_nonempty_iff.mp (convex_hull_nonempty_iff.mp ⟨g x, hconv x⟩) : _),
  have h2Ω : is_open (Ω ∩ fst ⁻¹' univ), { rwa [preimage_univ, inter_univ] },

  -- we could probably get away with something simpler to get γ₀.
  obtain ⟨γ₀, hγ₀_cont, hγ₀, h2γ₀, h3γ₀, -, hγ₀_surr⟩ := -- γ₀ is γ* in notes
    surrounding_loop_of_convex_hull is_open_univ is_connected_univ
    (by { rw [convex_hull_univ], exact mem_univ 0 }) (mem_univ (0 : F)),
  obtain ⟨ε₀, hε₀, V, hV, hεΩ⟩ :=
    hK.exists_thickening_image hΩ_op (continuous_id.prod_mk hb.continuous) (λ x _, b_in x),
  let range_γ₀ := (λ i : ℝ × ℝ, ∥γ₀ i.1 i.2∥) '' (I ×ˢ I),
  have h4γ₀ : bdd_above range_γ₀ :=
  (is_compact_Icc.prod is_compact_Icc).bdd_above_image (hγ₀_cont.norm.continuous_on),
  have h0 : 0 < 1 + Sup range_γ₀ := add_pos_of_pos_of_nonneg zero_lt_one (le_cSup_of_le h4γ₀
    (mem_image_of_mem _ $ mk_mem_prod unit_interval.zero_mem unit_interval.zero_mem) $
    norm_nonneg _),
  generalize' h0ε₁ : ε₀ / 2 = ε₁,
  have hε₁ : 0 < ε₁ := h0ε₁ ▸ div_pos hε₀ two_pos,
  let ε := ε₁ / (1 + Sup range_γ₀),
  have hε : 0 < ε := div_pos hε₁ h0,
  have h2ε : ∀ t s : ℝ, ∥ε • γ₀ t s∥ < ε₁,
  { intros t s, simp [norm_smul, mul_comm_div, real.norm_eq_abs, abs_eq_self.mpr, hε.le],
    refine lt_of_lt_of_le _ (mul_one _).le,
    rw [mul_lt_mul_left hε₁, div_lt_one h0],
    refine (zero_add _).symm.le.trans_lt _,
    refine add_lt_add_of_lt_of_le zero_lt_one (le_cSup h4γ₀ _),
    rw [← loop.fract_eq, ← h3γ₀],
    refine mem_image_of_mem _ (mk_mem_prod proj_I_mem_Icc $ unit_interval.fract_mem _) },
  let γ₁ : E → ℝ → loop F := λ x t, (γ₀ t).transform (λ y, b x + ε • y), -- `γ₁ x` is `γₓ` in notes
  refine ⟨γ₁, _⟩,
  have hbV : ∀ᶠ x near K, x ∈ V := hV,
  have h1 : ∀ (x ∈ V) (t s : ℝ), ball (x, b x) (ε₁ + ε₁) ⊆ Ω,
  { intros x hx t s,
    simp [← h0ε₁],
    refine (ball_subset_thickening (mem_image_of_mem _ hx) _).trans hεΩ },
  refine ⟨_, hgK.and hbV, ε₁, hε₁, ⟨⟨by simp [γ₁, hγ₀], by simp [γ₁, h2γ₀], _, _, _⟩, _⟩, _, _⟩,
  { intros x t s, simp [γ₁, h3γ₀] },
  { rintro x ⟨hx, -⟩, simp_rw [hx, γ₁],
    exact (hγ₀_surr.smul0 hε.ne').vadd0 },
  { refine hb.continuous.fst'.add (continuous_const.smul $ hγ₀_cont.snd') },
  { rintro x ⟨-, hx⟩ t ht s hs,
    have : ∥ε • γ₀ t s∥ < ε₀ := (h2ε t s).trans (h0ε₁ ▸ half_lt_self hε₀),
    refine h1 x hx t s (by simp [← h0ε₁, this]) },
  { intros x hx,
    rw [← h0ε₁, add_halves'],
    refine (ball_subset_thickening (mem_image_of_mem _ hx.2) _).trans hεΩ },
  { rintro x ⟨-, hx⟩ t s, simp [h2ε] }
end

/- Some remarks about `exist_loops_aux2`:
  `δ`: loop after smoothing
  `γ`: loop before smoothing (defined on all of `E`)
  Requirements:
  (0) `δ x t` is a loop
  (1) `δ` lands in `Ω`
  (2) `δ` has the correct values: for `s = 0` and `t = 0` it should be `b`
  (3) `δ` should be constant on `t ≤ 0` and for `t ≥ 1`.
  (4) `δ x 1` surrounds `g x`.
  (5) Near `K`, the line connecting `b` and `δ` lies in `Ω`

  Strategy:
  (a) We need `ε₁` satisfying the following conditions:
  (a1) We need to ensure that an `ε₁ x`-ball around `(x, δ x s t)` lies in `Ω` for some
    continuous `ε₁`.
  (a4) Furthermore, `ε₁` should be small enough so that any function with that
    distance from `γ` still surrounds `g`, using `surrounding_family.surrounds_of_close`.
  (a5): `ε₁ x < ε₀` (obtained from `exist_loops_aux1`)
  (b) Replace `γ x t s` by `γ x (linear_reparam t) (linear_reparam s)`.
  (e) Let `δ' x` be a family of loop that is at most `ε₁` away from `γ` using
    `exists_smooth_and_eq_on`. Since `γ` is smooth near `s ∈ ℤ` and `t ≤ 0` we can also
    ensure that `δ' = γ` for those values (*).
    Now let `δ x t s = δ' x (smooth_transition t) (fract s)`
    We immediately get (0) and (3). We get (2) by (*).
    This is still smooth, since `δ'` is doesn't depend on `s` near `s ∈ ℤ`.
  (f) (a1) gives (1), (a4) gives (4) and (a5) gives (5).

  Note: to ensure (2) the reparamerization strategy  from the blueprint
  (ensuring that `γ` is locally constant in the `t` and `s` directions)
  doesn't work.
  We also need to take the convolution in the `x`-direction,
  meaning that the value won't stay the same, since `γ` is not constant in the `x`-direction.

  -/

lemma exist_loops_aux2 [finite_dimensional ℝ E]
  (hK : is_compact K)
  (hΩ_op : is_open Ω)
  (hg : 𝒞 ∞ g) (hb : 𝒞 ∞ b)
  (hgK : ∀ᶠ x near K, g x = b x)
  (hconv : ∀ x, g x ∈ hull (connected_component_in (prod.mk x ⁻¹' Ω) $ b x)) :
  ∃ (γ : E → ℝ → loop F), surrounding_family_in g b γ univ Ω ∧ 𝒞 ∞ ↿γ ∧
  ∀ᶠ x near K, ∀ t s, closed_ball (x, b x) (dist (γ x t s) (b x)) ⊆ Ω :=
begin
  have h2Ω : is_open (Ω ∩ fst ⁻¹' univ), { rwa [preimage_univ, inter_univ] },
  obtain ⟨γ₁, V, hV, ε₀, hε₀, hγ₁, hΩ, h2γ₁⟩ := exist_loops_aux1 hK hΩ_op hb hgK hconv,
  obtain ⟨γ₂, hγ₂, hγ₂₁⟩ :=
    exists_surrounding_loops hK is_closed_univ is_open_univ subset.rfl h2Ω
    (λ x hx, hg.continuous.continuous_at) hb.continuous (λ x _, hconv x) ⟨V, hV, hγ₁⟩,
  let γ₃ : E → ℝ → loop F := λ x t, (γ₂ x (linear_reparam t)).reparam linear_reparam,
  have hγ₃ : surrounding_family_in g b γ₃ univ Ω := hγ₂.reparam,
  obtain ⟨ε₁, hε₁, hcε₁, hγε₁⟩ := hγ₃.to_sf.surrounds_of_close_univ hg.continuous,
  classical,
  let f : E → ℝ × ℝ → ℝ := λ x y, if Ωᶜ.nonempty then inf_dist (x, γ₃ x y.1 y.2) Ωᶜ else 1,
  have hI : is_compact (I ×ˢ I) := is_compact_Icc.prod is_compact_Icc,
  have h1f : continuous ↿f :=
    (continuous_fst.prod_mk hγ₃.cont).inf_dist.if_const _ continuous_const,
  have h2f : ∀ x : E, continuous (f x) :=
    λ x, h1f.comp₂ continuous_const continuous_id,
  have h3f : ∀ {x y}, 0 < f x y,
  { intros x y, by_cases hΩ : Ωᶜ.nonempty,
    { simp_rw [f, if_pos hΩ, ← hΩ_op.is_closed_compl.not_mem_iff_inf_dist_pos hΩ, not_mem_compl_iff,
      hγ₃.val_in (mem_univ _)] },
    { simp_rw [f, if_neg hΩ, zero_lt_one] }},
  let ε₂ : E → ℝ := λ x, min (min ε₀ (ε₁ x)) (Inf (f x '' (I ×ˢ I))),
  have hcε₂ : continuous ε₂ :=
    (continuous_const.min hcε₁).min (hI.continuous_Inf h1f),
  have hε₂ : ∀ {x}, 0 < ε₂ x := λ x, lt_min (lt_min hε₀ (hε₁ x))
    ((hI.lt_Inf_iff_of_continuous
      ((nonempty_Icc.mpr zero_le_one).prod (nonempty_Icc.mpr zero_le_one))
      (h2f x).continuous_on _).mpr $ λ x hx, h3f),
  let γ₄ := ↿γ₃,
  have h0γ₄ : ∀ x t s, γ₄ (x, t, s) = γ₃ x t s := λ x t s, rfl,
  have hγ₄ : continuous γ₄ := hγ₃.cont,
  let C₁ : set ℝ := Iic (5⁻¹  : ℝ) ∪ Ici (4 / 5),
  have h0C₁ : (0 : ℝ) ∈ C₁ := or.inl (by { rw [mem_Iic], norm_num1 }),
  have h1C₁ : (1 : ℝ) ∈ C₁ := or.inr (by { rw [mem_Ici], norm_num1 }),
  have h2C₁ : ∀ (s : ℝ) (hs : fract s = 0), fract ⁻¹' C₁ ∈ 𝓝 s,
  { intros s hs,
    refine fract_preimage_mem_nhds _ (λ _, _),
    { rw [hs], refine mem_of_superset (Iic_mem_nhds $ by norm_num) (subset_union_left _ _) },
    { refine mem_of_superset (Ici_mem_nhds $ by norm_num) (subset_union_right _ _) } },
  let C : set (E × ℝ × ℝ) := (λ x, x.2.1) ⁻¹' Iic (5⁻¹ : ℝ) ∪ (λ x, fract x.2.2) ⁻¹' C₁,
  have hC : is_closed C,
  { refine (is_closed_Iic.preimage continuous_snd.fst).union _,
    refine ((is_closed_Iic.union is_closed_Ici).preimage_fract _).preimage continuous_snd.snd,
    exact λ x, or.inl (show (0 : ℝ) ≤ 5⁻¹, by norm_num) },
  let U₁ : set ℝ := Iio (4⁻¹ : ℝ) ∪ Ioi (3 / 4),
  let U : set (E × ℝ × ℝ) := (λ x, x.2.1) ⁻¹' Iio (4⁻¹ : ℝ) ∪ (λ x, fract x.2.2) ⁻¹' U₁,
  have hUC : U ∈ 𝓝ˢ C,
  { have hU : is_open U,
    { refine (is_open_Iio.preimage continuous_snd.fst).union _,
      refine ((is_open_Iio.union is_open_Ioi).preimage_fract _).preimage continuous_snd.snd,
      exact λ x, or.inr (show (3/4 : ℝ) < 1, by norm_num) },
    exact hU.mem_nhds_set.mpr (union_subset_union (λ x hx, lt_of_le_of_lt hx (by norm_num)) $
      union_subset_union (λ x hx, lt_of_le_of_lt hx (by norm_num))
      (λ x hx, lt_of_lt_of_le (by norm_num) hx)) },
  have h2γ₄ : eq_on γ₄ (λ x, b x.1) U,
  { rintro ⟨x, t, s⟩ hxts,
    simp_rw [h0γ₄, γ₃, loop.reparam_apply],
    cases hxts with ht hs,
    { refine hγ₂.to_sf.t_le_zero_eq_b x (linear_reparam s) (linear_reparam_nonpos (le_of_lt ht)) },
    { rw [← loop.fract_eq, fract_linear_reparam_eq_zero, hγ₂.base],
      exact or.imp le_of_lt le_of_lt hs } },
  have h3γ₄ : smooth_on γ₄ U := hb.fst'.cont_diff_on.congr h2γ₄,
  obtain ⟨γ₅, hγ₅, hγ₅₄, hγ₅C⟩ :=
    exists_smooth_and_eq_on hγ₄ hcε₂.fst' (λ x, hε₂) hC ⟨U, hUC, h3γ₄⟩,
  let γ : E → ℝ → loop F := λ x t, ⟨λ s, γ₅ (x, smooth_transition t, fract s),
    λ s, by rw [fract_add_one s]⟩,
  have hγ : 𝒞 ∞ ↿γ,
  { rw [cont_diff_iff_cont_diff_at],
    rintro ⟨x, t, s⟩, by_cases hs : fract s = 0,
    { have : (λ x, γ x.1 x.2.1 x.2.2) =ᶠ[𝓝 (x, t, s)] λ x, b x.1,
      { have : (λ x : E × ℝ × ℝ, (x.1, smooth_transition x.2.1, fract x.2.2)) ⁻¹' C ∈ 𝓝 (x, t, s),
        { simp_rw [C, @preimage_union _ _ _ (_ ⁻¹' _), preimage_preimage, fract_fract],
          refine mem_of_superset _ (subset_union_right _ _),
          refine continuous_at_id.snd'.snd'.preimage_mem_nhds (h2C₁ s hs) },
        refine eventually_of_mem this _,
        intros x hx,
        simp_rw [γ, loop.coe_mk],
        refine (hγ₅C hx).trans
          (h2γ₄ $ (subset_interior_iff_mem_nhds_set.mpr hUC).trans interior_subset hx) },
      exact hb.fst'.cont_diff_at.congr_of_eventually_eq this },
    { exact (hγ₅.comp₃ cont_diff_fst smooth_transition.cont_diff.fst'.snd' $ cont_diff_snd.snd'.sub
        cont_diff_const).cont_diff_at.congr_of_eventually_eq
        ((eventually_eq.rfl.prod_mk $ eventually_eq.rfl.prod_mk $
        (fract_eventually_eq hs).comp_tendsto continuous_at_id.snd'.snd').fun_comp ↿γ₅) } },
  refine ⟨γ, ⟨⟨_, _, _, _, hγ.continuous⟩, _⟩, hγ, _⟩,
  { intros x t, simp_rw [γ, loop.coe_mk, fract_zero], rw [hγ₅C], exact hγ₃.base x _,
    exact or.inr (by { rw [mem_preimage, fract_zero], exact h0C₁ }) },
  { intros x s, simp_rw [γ, loop.coe_mk, smooth_transition.zero_of_nonpos le_rfl], rw [hγ₅C],
    exact hγ₃.t₀ x (fract s),
    exact or.inl (show (0 : ℝ) ≤ 5⁻¹, by norm_num) },
  { intros x t s, simp_rw [γ, loop.coe_mk, smooth_transition_proj_I] },
  { rintro x -, apply hγε₁, intro s,
    simp_rw [← (γ₃ x 1).fract_eq s, γ, loop.coe_mk, smooth_transition.one_of_one_le le_rfl],
    exact (hγ₅₄ (x, 1, fract s)).trans_le ((min_le_left _ _).trans $ min_le_right _ _) },
  { rintro x - t - s -, rw [← not_mem_compl_iff],
    by_cases hΩ : Ωᶜ.nonempty, swap,
    { rw [not_nonempty_iff_eq_empty] at hΩ, rw [hΩ], apply not_mem_empty },
    refine not_mem_of_dist_lt_inf_dist _,
    exact (x, γ₃ x (smooth_transition t) (fract s)),
    rw [dist_comm, dist_prod_same_left],
    refine (hγ₅₄ (x, _, fract s)).trans_le ((min_le_right _ _).trans $ cInf_le _ _),
    refine (is_compact_Icc.prod is_compact_Icc).bdd_below_image (h2f x).continuous_on,
    rw [← hγ₃.proj_I],
    simp_rw [f, if_pos hΩ],
    apply mem_image_of_mem _ (mk_mem_prod proj_I_mem_Icc (unit_interval.fract_mem s)) },
  { refine eventually_of_mem (filter.inter_mem hV hγ₂₁) (λ x hx t s, _),
    refine (closed_ball_subset_ball _).trans (hΩ x hx.1),
    refine (dist_triangle _ _ _).trans_lt (add_lt_add_of_le_of_lt
      ((hγ₅₄ (x, _, fract s)).le.trans $ (min_le_left _ _).trans $ min_le_left _ _) _),
    simp_rw [γ₄, has_uncurry.uncurry, γ₃, loop.reparam_apply, show γ₂ x = γ₁ x, from hx.2],
    exact h2γ₁ x hx.1 _ _ }
end

variables (g b Ω U K)
variables [measurable_space F] [borel_space F]

/-- A "nice" family of loops consists of all the properties we want from the `exist_loops` lemma:
it is a smooth homotopy in `Ω` with fixed endpoints from the constant loop at `b x` to a loop with
average `g x` that is also constantly `b x` near `K`.
The first two conditions are implementation specific: the homotopy is constant outside the unit
interval. -/
structure nice_loop (γ : ℝ → E → loop F) : Prop :=
(t_le_zero : ∀ x, ∀ t ≤ 0, γ t x = γ 0 x)
(t_ge_one : ∀ x, ∀ t ≥ 1, γ t x = γ 1 x)
(t_zero : ∀ x s, γ 0 x s = b x)
(s_zero : ∀ x t, γ t x 0 = b x)
(avg : ∀ x, (γ 1 x).average = g x)
(mem_Ω : ∀ x t s, (x, γ t x s) ∈ Ω)
(smooth : 𝒞 ∞ ↿γ)
(rel_K : ∀ᶠ x in 𝓝ˢ K, ∀ t s, γ t x s = b x)

variables {g b Ω U K}


theorem exist_loops [finite_dimensional ℝ E]
  (hK : is_compact K)
  (hΩ_op : is_open Ω)
  (hg : 𝒞 ∞ g) (hb : 𝒞 ∞ b)
  (hgK : ∀ᶠ x near K, g x = b x)
  (hconv : ∀ x, g x ∈ hull (connected_component_in (prod.mk x ⁻¹' Ω) $ b x)) :
  ∃ γ : ℝ → E → loop F, nice_loop g b Ω K γ :=
begin
  obtain ⟨γ₁, hγ₁, hsγ₁, h2γ₁⟩ := exist_loops_aux2 hK hΩ_op hg hb hgK hconv,
  let γ₂ : smooth_surrounding_family g :=
    ⟨hg, λ x, γ₁ x 1, hsγ₁.comp₃ cont_diff_fst cont_diff_const cont_diff_snd,
      λ x, hγ₁.surrounds x (mem_univ _)⟩,
  classical,
  let γ₃ : ℝ → E → loop F :=
  λ t x, (γ₁ x t).reparam $ (γ₂.reparametrize x).equivariant_map,
  have hγ₃ : 𝒞 ∞ ↿γ₃ :=
    hsγ₁.comp₃ cont_diff_snd.fst cont_diff_fst (γ₂.reparametrize_smooth.snd'),
  obtain ⟨χ, hχ, h1χ, h0χ, h2χ⟩ := exists_cont_diff_one_nhds_of_interior hK.is_closed
    (subset_interior_iff_mem_nhds_set.mpr $ hgK.and h2γ₁),
  simp_rw [← or_iff_not_imp_left] at h0χ,
  let γ : ℝ → E → loop F :=
  λ t x, χ x • loop.const (b x) + (1 - χ x) • γ₃ t x,
  have h1γ : ∀ x, ∀ t ≤ 0, γ t x = γ 0 x,
  { intros x t ht, ext s, simp [hγ₁.to_sf.t_le_zero _ _ ht] },
  have h2γ : ∀ x, ∀ t ≥ 1, γ t x = γ 1 x,
  { intros x t ht, ext s, simp [hγ₁.to_sf.t_ge_one _ _ ht] },
  refine ⟨γ, h1γ, h2γ, _, _, _, _, _, _⟩,
  { intros x t, simp [hγ₁.t₀] },
  { intros x t, simp [hγ₁.base] },
  { intros x,
    have h1 : interval_integrable (χ x • loop.const (b x) : loop F) volume 0 1,
    { show interval_integrable (λ t, χ x • b x) volume (0 : ℝ) (1 : ℝ),
      exact interval_integrable_const, },
    have h2 : interval_integrable ((1 - χ x) • γ₃ 1 x : loop F) volume 0 1 :=
    ((hγ₃.comp₃ cont_diff_const cont_diff_const cont_diff_id)
      .continuous.interval_integrable _ _).smul _,
    have h3 : (γ₃ 1 x).average = g x := γ₂.reparametrize_average x,
    simp [h1, h2, h3],
    rcases h0χ x with ⟨hx,-⟩|hx,
    { rw [hx, smul_add_one_sub_smul] },
    { simp [hx] } },
  { intros x t s,
    have : ∀ (P : F → Prop) t, (∀ t ∈ I, P (γ t x s)) → P (γ t x s),
    { intros P t hP,
      rcases le_total 0 t with h1t|h1t, rcases le_total t 1 with h2t|h2t,
      { exact hP t ⟨h1t, h2t⟩},
      { rw [h2γ x t h2t], exact hP 1 ⟨zero_le_one, le_rfl⟩ },
      { rw [h1γ x t h1t], exact hP 0 ⟨le_rfl, zero_le_one⟩ } },
    refine this (λ y, (x, y) ∈ Ω) t (λ t ht, _),
    rcases h0χ x with ⟨hx, h2x⟩|hx,
    { refine h2x t (γ₂.reparametrize x s) _, simp [γ, dist_smul_add_one_sub_smul_le (h2χ x)] },
    { simp [hx], apply hγ₁.val_in (mem_univ _) } },
  { exact (hχ.fst'.snd'.smul hb.fst'.snd').add ((cont_diff_const.sub hχ.fst'.snd').smul hγ₃) },
  { exact h1χ.mono (λ x (hx : χ x = 1), by simp [hx]), }
end
