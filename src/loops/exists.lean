import notations
import loops.reparametrization
import to_mathlib.analysis.cut_off
import to_mathlib.topology.hausdorff_distance

noncomputable theory

open set function finite_dimensional prod int topological_space metric filter
open measure_theory measure_theory.measure
open_locale topological_space unit_interval


variables {E : Type*} [normed_group E] [normed_space ℝ E]
          {F : Type*} [normed_group F]
          {g b : E → F} {Ω : set (E × F)} {U K C : set E}
variables [normed_space ℝ F] [measurable_space F] [borel_space F] [finite_dimensional ℝ F]

variables (g b Ω U K)

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

-- /--
-- `ε = wiggle_room` is the amount of wiggle room we have, with the property that
-- `ball (x, b x) (ε + ε) ⊆ Ω` for all `x` in V.
-- -/
-- def wiggle_room

lemma exists_loops_aux1 [finite_dimensional ℝ E]
  (hK : is_compact K)
  (hΩ_op : is_open Ω)
  (hg : 𝒞 ∞ g) (hb : 𝒞 ∞ b)
  (hgK : ∀ᶠ x near K, g x = b x)
  (hconv : ∀ x, g x ∈ hull (connected_comp_in (prod.mk x ⁻¹' Ω) $ b x)) :
  ∃ (γ : E → ℝ → loop F) (V ∈ 𝓝ˢ K) (ε > 0), surrounding_family_in g b γ V Ω ∧
  (∀ (x ∈ V), closed_ball (x, b x) (ε + ε) ⊆ Ω) ∧
  ∀ (x ∈ V) t s, dist (γ x t s) (b x) < ε :=
begin
  have b_in : ∀ x, (x, b x) ∈ Ω :=
    λ x, (connected_comp_in_nonempty_iff.mp (convex_hull_nonempty_iff.mp ⟨g x, hconv x⟩) : _),
  have bK_im : (λ x, (x, b x)) '' K ⊆ Ω := image_subset_iff.mpr (λ x _, b_in x),
  have h2Ω : is_open (Ω ∩ fst ⁻¹' univ), { rwa [preimage_univ, inter_univ] },

  -- we could probably get away with something simpler to get γ₀.
  obtain ⟨γ₀, hγ₀_cont, hγ₀, h2γ₀, h3γ₀, -, hγ₀_surr⟩ := -- γ₀ is γ* in notes
    surrounding_loop_of_convex_hull is_open_univ is_connected_univ
    (by { rw [convex_hull_univ], exact mem_univ 0 }) (mem_univ (0 : F)),
  have := λ x, local_loops_open ⟨univ, univ_mem, h2Ω⟩ hg.continuous.continuous_at
    hb.continuous (hconv x),
  obtain ⟨ε₀, hε₀, V, hV, hεΩ⟩ :=
    hΩ_op.exists_thickening_image hK (continuous_id.prod_mk hb.continuous) bK_im,
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
  { intros t s, simp [norm_smul, mul_comm_div', real.norm_eq_abs, abs_eq_self.mpr, hε.le],
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
    -- refine (closed_ball_subset_ball $ h2ε _ _).trans _,
    refine (ball_subset_thickening (mem_image_of_mem _ hx) _).trans hεΩ },
  refine ⟨_, hgK.and hbV, ε₁, hε₁, ⟨⟨by simp [γ₁, hγ₀], by simp [γ₁, h2γ₀], _, _, _⟩, _⟩, _, _⟩,
  { intros x t s, simp [γ₁, h3γ₀] },
  { rintro x ⟨hx, -⟩, simp_rw [hx, γ₁],
    exact (hγ₀_surr.smul0 hε.ne').vadd0 },
  { refine hb.continuous.fst'.add (continuous_const.smul $ hγ₀_cont.snd') },
  { rintro x ⟨-, hx⟩ t ht s hs,
    have : ∥ε • γ₀ t s∥ < ε₀ := (h2ε t s).trans (h0ε₁ ▸ half_lt_self hε₀),
    refine h1 x hx t s (by simp [← h0ε₁, this]) },
  { sorry },
  { rintro x ⟨-, hx⟩ t s, simp [h2ε] }
end

/- Some remarks about `exists_loops_aux2`:
  `γ₅`: loop after smoothing
  `γ₃`: loop before smoothing (defined on all of `E`)
  Requirements:
  (1) `γ₅` lands in `Ω`
  (2) `γ₅` has the correct values: for `s = 0` and `t = 0` it should be `b`
  (3) `γ₅` should be constant on `t ≤ 0` and for `t ≥ 1`.
  (4) `γ₅ x 1` surrounds `g x`.
  (5) Near `K`, the line connecting `b` and `γ₅` lies in `Ω`

  Strategy:
  (a) We need `ε₁` satisfying the following conditions:
  (a1) [DONE] We need to ensure that an `ε₁ x`-ball around `(x, γ x s t)` lies in `Ω` for some
    continuous `ε₁`.
  (a4) Furthermore, `ε₁` should be small enough so that any function with that
    distance from `γ` still surrounds `g`. This requires a strengthening of
    `surrounds.eventually_surrounds` where we can also ensure that `ε₁` is continuous
    Q: how?
  (a5): [DONE] `ε₁ x < ε₀`
  (c) We want a continuous `ε₂` such that if `φ.R < ε₂` we get `dist (γ₅ x) (γ₃ x) < ε₁ x`.
    Something like
    `ε₂ x = ε₁ x / supr { 1 + ∥ γ x t s - γ x t' s'∥  | t s t' s' ∈ [0,1]}`. (Q: how exactly?)
  (d) Choose `φ.R x` as a smooth positive function below `ε₂ x` (using `exists_smooth_pos`) and let
    `φ.r = φ.R / 2`.
  (e) Let `γ₅ = γ₃ ⋆ φ`
  (f) Using (b), (a1) gives (1) and (a4) gives (4) and (a5) gives (5).
  (g) We ensure (3) by applying a smooth transition on `t`. To help (g) we furthermore
    make sure `γ` is constant for `t ≤ 1/4` and `t ≥ 3/4`.
  (h) To ensure (2), *after* the convolution we can use a partition of unity to interpolate between
    `γ` to `b`. We should be equal to `b` for `s ∈ ℤ` and for `t = 0` and for `x` near `K`
    (we currently do the last part after reparametrization, but we can just as well do it here).
    On all these values `γ₃ = b`
    This interpolation lies in `Ω` by (a1) and (a5), since `γ₃ = b` on `s ∈ ℤ` and `t = 0` and
      close to `b` by `exists_loops_aux1`.
    We can ensure that this preserves (4) using (g)

  Note: to ensure (2) the reparamerization strategy  from the blueprint
  (ensuring that `γ` is locally constant in the `t` and `s` directions)
  doesn't work.
  We also need to take the convolution in the `x`-direction,
  meaning that the value won't stay the same, since `γ` is not constant in the `x`-direction.

  -/
lemma exists_loops_aux2 [finite_dimensional ℝ E]
  (hK : is_compact K)
  (hΩ_op : is_open Ω)
  (hg : 𝒞 ∞ g) (hb : 𝒞 ∞ b)
  (hgK : ∀ᶠ x near K, g x = b x)
  (hconv : ∀ x, g x ∈ hull (connected_comp_in (prod.mk x ⁻¹' Ω) $ b x)) :
  ∃ (γ : E → ℝ → loop F), surrounding_family_in g b γ univ Ω ∧ 𝒞 ∞ ↿γ ∧
  ∀ᶠ x near K, ∀ t s, closed_ball (x, b x) (dist (γ x t s) (b x)) ⊆ Ω :=
begin
  have b_in : ∀ x, (x, b x) ∈ Ω :=
    λ x, (connected_comp_in_nonempty_iff.mp (convex_hull_nonempty_iff.mp ⟨g x, hconv x⟩) : _),
  have h2Ω : is_open (Ω ∩ fst ⁻¹' univ), { rwa [preimage_univ, inter_univ] },
  -- have bK_im : (λ x, (x, b x)) '' K ⊆ Ω := image_subset_iff.mpr (λ x _, b_in x),
  -- have h2Ω_op : ∀ x, is_open (prod.mk x ⁻¹' Ω),
  --  from λ x, hΩ_op.preimage (continuous.prod.mk x),
  borelize E,
  letI K₀ : positive_compacts E,
  { refine ⟨⟨closed_ball 0 1, is_compact_closed_ball 0 1⟩, _⟩,
    rw [interior_closed_ball, nonempty_ball], all_goals { norm_num } },
  letI : measure_space E := ⟨add_haar_measure K₀⟩,
  -- haveI : is_add_haar_measure (volume : measure E) :=
  --   infer_instance,

  obtain ⟨γ₁, V, hV, ε₀, hε₀, hγ₁, hΩ, h2γ₁⟩ := exists_loops_aux1 hK hΩ_op hg hb hgK hconv,
  obtain ⟨γ₂, hγ₂, hγ₂₁⟩ :=
    exists_surrounding_loops hK is_closed_univ is_open_univ subset.rfl h2Ω
    (λ x hx, hg.continuous.continuous_at) hb.continuous (λ x _, hconv x) ⟨V, hV, hγ₁⟩,
  obtain ⟨ε₁, hε₁, hcε₁, hγε₁⟩ := hγ₂.to_sf.surrounds_of_close_univ hg.continuous,
  let ε₂ : E → ℝ := λ x, min (min ε₀ (ε₁ x)) (⨅ y : I × I, inf_dist (x, γ₂ x y.1 y.2) Ωᶜ), -- todo
  have hcε₂ : continuous ε₂ := sorry, -- (continuous_inf_dist_pt _).comp (continuous_id.prod_mk hg.continuous),
  have hε₂ : ∀ {x}, 0 < ε₂ x, sorry,
  -- let ε₂ : E → ℝ := λ x, ε₁ x / ⨆ y z : I × I, dist (γ₂ x y.1 y.2) (γ₂ x z.1 z.2), -- todo
  -- have hε₂ : continuous ε₂ := sorry, -- (continuous_inf_dist_pt _).comp (continuous_id.prod_mk hg.continuous),
  -- have h2ε₂ : ∀ {x}, 0 < ε₂ x, sorry,
  -- obtain ⟨ε₃, hε₃, h2ε₃⟩ := exists_smooth_pos is_open_univ hε₁ (λ x _, h2ε₁),
  -- have h2ε₃ : ∀ {x}, 0 < ε₃ x := λ x, h2ε₃ x (mem_univ _),
  -- let φ : E × ℝ × ℝ → ℝ :=
  -- λ x, (⟨⟨ε₃ x.1 / 2, ε₃ x.1, half_pos h2ε₃, half_lt_self h2ε₃⟩⟩ : cont_diff_bump (0 : E × ℝ × ℝ)) x,
  let γ₃ : E → ℝ → loop F := λ x t, (γ₂ x (linear_reparam t)).reparam linear_reparam,
  let γ₄ := ↿γ₃,
  have hγ₄ : continuous γ₄,
  { sorry },
  -- let γ₅ : E × ℝ × ℝ → F := γ₄,
  -- let γ₆ : E → ℝ → loop F := γ₃,
  -- { refine λ s x, ⟨λ t, γ₅ (x, s, t), λ t, _⟩,
  --   change ∫ u, φ u • γ₃ (x - u.1) (s - u.2.1) (t + 1 - u.2.2) =
  --     ∫ u, φ u • γ₃ (x - u.1) (s - u.2.1) (t - u.2.2),
  --   simp_rw [← sub_add_eq_add_sub, (γ₃ _ _).per] },
  -- let γ₇ : E → ℝ → loop F := λ x t, γ₆ x (real.smooth_transition $ 2 * t - 1 / 2),
  let s : set (E × ℝ × ℝ) := { x : E × ℝ × ℝ | x.2.1 = 0 ∨ fract x.2.2 = 0 },
    -- (K : set E) ×ˢ ((univ : set ℝ) ×ˢ (univ : set ℝ)) ∪
    -- (univ : set E) ×ˢ (({0} : set ℝ) ×ˢ (univ : set ℝ)) ∪
    -- (univ : set E) ×ˢ ((univ : set ℝ) ×ˢ (range (coe : ℤ → ℝ))),
  have hs : is_closed s := sorry,
  let U : set ℝ := (Icc (1 / 4 : ℝ) (3 / 4))ᶜ,
  let t : set (E × ℝ × ℝ) :=
  { x : E × ℝ × ℝ | x.2.1 ∈ U ∨ fract x.2.2 ∈ U },
  have hts : t ∈ 𝓝ˢ s := sorry,
  have hsγ₄ : smooth_on γ₄ t,
  { sorry },
  obtain ⟨γ₅, hγ₅, hγ₅₄, hγ₅s⟩ := exists_smooth_and_eq_on hγ₄ hcε₂.fst' (λ x, hε₂) hs ⟨t, hts, hsγ₄⟩,
  let γ : E → ℝ → loop F := λ x t, ⟨λ s, γ₅ (x, t, fract s), sorry⟩,
  -- obtain ⟨χ, hχ, h1χ, h0χ, h2χ⟩ := exists_cont_diff_one_nhds_of_interior hs hst,
  -- let γ :  ℝ → E → ℝ → F :=

  -- λ t x s, χ (t, x, s) • b x + (1 - χ (t, x, s)) • γ₇ x t s,
  sorry
end

theorem exists_loops [finite_dimensional ℝ E]
  (hK : is_compact K)
  (hΩ_op : is_open Ω)
  (hg : 𝒞 ∞ g) (hb : 𝒞 ∞ b)
  (hgK : ∀ᶠ x near K, g x = b x)
  (hconv : ∀ x, g x ∈ hull (connected_comp_in (prod.mk x ⁻¹' Ω) $ b x)) :
  ∃ γ : ℝ → E → loop F, nice_loop g b Ω K γ :=
begin
  obtain ⟨γ₁, hγ₁, hsγ₁, h2γ₁⟩ := exists_loops_aux2 hK hΩ_op hg hb hgK hconv,
  let γ₂ : smooth_surrounding_family g :=
    ⟨λ x, γ₁ x 1, hsγ₁.comp₃ cont_diff_fst cont_diff_const cont_diff_snd,
      λ x, hγ₁.surrounds x (mem_univ _)⟩,
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
    { simp [hx], exact hγ₁.val_in (mem_univ _) ht } },
  { exact (hχ.fst'.snd'.smul hb.fst'.snd').add ((cont_diff_const.sub hχ.fst'.snd').smul hγ₃) },
  { exact h1χ.mono (λ x (hx : χ x = 1), by simp [hx]), }
end
