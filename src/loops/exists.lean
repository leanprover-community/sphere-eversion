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
  `δ`: loop after smoothing
  `γ`: loop before smoothing (defined on all of `E`)
  Requirements:
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
  (a5): `ε₁ x < ε₀` (obtained from `exists_loops_aux1`)
  (b) Replace `γ x t s` by `γ x (linear_reparam t) (linear_reparam s)`.
  (e) Let `δ x` be a family of loop that is at most `ε₁` away from `γ` using
    `exists_smooth_and_eq_on`. Since `γ` is smooth near `s ∈ ℤ` and `t ≤ 0` and `t ≥ 1` we can also
    ensure that `δ = γ` for those values. This gives (2) and (3).
  (f) (a1) gives (1), (a4) gives (4) and (a5) gives (5).

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
  have h2Ω : is_open (Ω ∩ fst ⁻¹' univ), { rwa [preimage_univ, inter_univ] },
  obtain ⟨γ₁, V, hV, ε₀, hε₀, hγ₁, hΩ, h2γ₁⟩ := exists_loops_aux1 hK hΩ_op hg hb hgK hconv,
  obtain ⟨γ₂, hγ₂, hγ₂₁⟩ :=
    exists_surrounding_loops hK is_closed_univ is_open_univ subset.rfl h2Ω
    (λ x hx, hg.continuous.continuous_at) hb.continuous (λ x _, hconv x) ⟨V, hV, hγ₁⟩,
  let γ₃ : E → ℝ → loop F := λ x t, (γ₂ x (linear_reparam t)).reparam linear_reparam,
  have hγ₃ : surrounding_family_in g b γ₃ univ Ω := hγ₂.reparam,
  obtain ⟨ε₁, hε₁, hcε₁, hγε₁⟩ := hγ₃.to_sf.surrounds_of_close_univ hg.continuous,
  let f : E → ℝ × ℝ → ℝ := λ x y, inf_dist (x, γ₃ x y.1 y.2) Ωᶜ,
  have hcont : ∀ x : E, continuous (f x) :=
    λ x, (continuous_inf_dist_pt _).comp (continuous_const.prod_mk $
      hγ₃.cont.comp₃ continuous_const continuous_fst continuous_snd),
  let ε₂ : E → ℝ := λ x, min (min ε₀ (ε₁ x)) (Inf (f x '' (I ×ˢ I))),
  have hcε₂ : continuous ε₂ := sorry, -- (continuous_inf_dist_pt _).comp (continuous_id.prod_mk hg.continuous),
  have hε₂ : ∀ {x}, 0 < ε₂ x, sorry,
  let γ₄ := ↿γ₃,
  have hγ₄ : continuous γ₄ := hγ₃.cont,
  let C₁ : set ℝ := Iic (1 / 5 : ℝ) ∪ Ici (4 / 5),
  have h0C₁ : (0 : ℝ) ∈ C₁ := or.inl (by { rw [mem_Iic], norm_num1 }),
  have h1C₁ : (1 : ℝ) ∈ C₁ := or.inr (by { rw [mem_Ici], norm_num1 }),
  have hC₁ : ∀ t, proj_I t = t ∨ t ∈ C₁,
  { simp_rw [proj_I_eq_self, ← mem_union, ← eq_univ_iff_forall, C₁, ← union_assoc],
    rw [union_comm (Icc _ _), Iic_union_Icc', Iic_union_Ici'],
    refine le_trans _ (le_max_right _ _),
    all_goals { norm_num1 }  },
  let C : set (E × ℝ × ℝ) := { x : E × ℝ × ℝ | x.2.1 ∈ C₁ ∨ fract x.2.2 ∈ C₁ },
  have hC : is_closed C := sorry,
  let U₁ : set ℝ := Iio (1 / 4 : ℝ) ∪ Ioi (3 / 4),
  let U : set (E × ℝ × ℝ) :=
  { x : E × ℝ × ℝ | x.2.1 ∈ U₁ ∨ fract x.2.2 ∈ U₁ },
  have hUC : U ∈ 𝓝ˢ C := sorry,
  have hγ₄U : smooth_on γ₄ U,
  { sorry },
  obtain ⟨γ₅, hγ₅, hγ₅₄, hγ₅C⟩ := exists_smooth_and_eq_on hγ₄ hcε₂.fst' (λ x, hε₂) hC ⟨U, hUC, hγ₄U⟩,
  let γ : E → ℝ → loop F := λ x t, ⟨λ s, γ₅ (x, t, fract s), λ s, by rw [fract_add_one s]⟩,
  have hγ : 𝒞 ∞ ↿γ,
  { sorry },
  refine ⟨γ, ⟨⟨_, _, _, _, hγ.continuous⟩, _⟩, hγ, _⟩,
  { intros x t, simp_rw [γ, loop.coe_mk, fract_zero], rw [hγ₅C], exact hγ₃.base x t,
    exact or.inr (by { rw [fract_zero], exact h0C₁ }) },
  { intros x s, simp_rw [γ, loop.coe_mk], rw [hγ₅C], exact hγ₃.t₀ x (fract s),
    exact or.inl h0C₁ },
  { intros x t s, simp_rw [γ, loop.coe_mk], rcases hC₁ t with ht|ht, rw [ht],
    rw [hγ₅C, hγ₅C], exact hγ₃.proj_I x t (fract s), exact or.inl ht,
    exact or.inl (proj_I_mapsto h0C₁ h1C₁ ht) },
  { rintro x -, apply hγε₁, intro s, rw [← (γ₃ x 1).fract_eq s],
    exact (hγ₅₄ (x, 1, fract s)).trans_le ((min_le_left _ _).trans $ min_le_right _ _) },
  { rintro x - t - s -, rw [← not_mem_compl_iff], refine not_mem_of_dist_lt_inf_dist _,
    exact (x, γ₃ x t (fract s)),
    rw [dist_comm, dist_prod_same_left],
    refine (hγ₅₄ (x, t, fract s)).trans_le ((min_le_right _ _).trans $ cInf_le _ _),
    refine (is_compact_Icc.prod is_compact_Icc).bdd_below_image (hcont x).continuous_on,
    rw [← hγ₃.proj_I],
    apply mem_image_of_mem (f x) (mk_mem_prod proj_I_mem_Icc (unit_interval.fract_mem s)) },
  { refine eventually_of_mem (filter.inter_mem hV hγ₂₁) (λ x hx t s, _),
    refine (closed_ball_subset_closed_ball _).trans (hΩ x hx.1),
    refine (dist_triangle _ _ _).trans
      (add_le_add ((hγ₅₄ (x, t, fract s)).le.trans $ (min_le_left _ _).trans $ min_le_left _ _) _),
    simp_rw [γ₄, has_uncurry.uncurry, γ₃, loop.reparam_apply, show γ₂ x = γ₁ x, from hx.2],
    exact (h2γ₁ x hx.1 _ _).le }
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
