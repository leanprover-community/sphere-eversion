import notations
import loops.reparametrization
import to_mathlib.analysis.cut_off
import to_mathlib.convolution
import to_mathlib.topology.hausdorff_distance

noncomputable theory

open set function finite_dimensional prod int topological_space metric filter
open measure_theory measure_theory.measure
open_locale topological_space unit_interval convolution


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

/-- For every continuous positive function there is a smaller smooth positive function.

proof sketch: choose locally constant functions on compact sets, and patch them using a partition
of unity. -/
lemma exists_smooth_pos {f : E → ℝ} {U : set E} (hU : is_open U) (hf : continuous f)
  (h2f : ∀ x ∈ U, 0 < f x) :
  ∃ φ : E → ℝ, cont_diff ℝ ⊤ φ ∧ ∀ x ∈ U, 0 < φ x :=
sorry

lemma exists_loops_aux1 [finite_dimensional ℝ E]
  (hK : is_compact K)
  (hΩ_op : is_open Ω)
  (hg : 𝒞 ∞ g) (hb : 𝒞 ∞ b)
  (hgK : ∀ᶠ x near K, g x = b x)
  (hconv : ∀ x, g x ∈ hull (connected_comp_in (prod.mk x ⁻¹' Ω) $ b x)) :
  ∃ (γ : E → ℝ → loop F) (V ∈ 𝓝ˢ K), surrounding_family_in g b γ V Ω ∧
  ∀ (x ∈ V) t s, closed_ball (x, b x) (dist (γ x t s) (b x)) ⊆ Ω :=
begin
  have b_in : ∀ x, (x, b x) ∈ Ω :=
    λ x, (connected_comp_in_nonempty_iff.mp (convex_hull_nonempty_iff.mp ⟨g x, hconv x⟩) : _),
  have bK_im : (λ x, (x, b x)) '' K ⊆ Ω := image_subset_iff.mpr (λ x _, b_in x),
  have h2Ω : is_open (Ω ∩ fst ⁻¹' univ), { rwa [preimage_univ, inter_univ] },

  -- we could probably get away with something simpler to get γ₀.
  obtain ⟨γ₀, hγ₀_cont, hγ₀0, h2γ₀0, -, hγ₀_surr⟩ := -- γ₀ is γ* in notes
    surrounding_loop_of_convex_hull is_open_univ is_connected_univ
    (by { rw [convex_hull_univ], exact mem_univ 0 }) (mem_univ (0 : F)),
  have := λ x, local_loops_open ⟨univ, univ_mem, h2Ω⟩ hg.continuous.continuous_at
    hb.continuous (hconv x),
  obtain ⟨ε₀, hε₀, V, hV, hεΩ⟩ :=
    hΩ_op.exists_thickening_image hK (continuous_id.prod_mk hb.continuous) bK_im,
  let ε := ε₀ / ⨆ i : unit_interval × unit_interval, ∥γ₀ i.1 i.2∥,
  have hε : 0 < ε := sorry,
  let γ₁ : E → ℝ → loop F := λ x t, (γ₀ t).transform (λ y, b x + ε • y), -- `γ₁ x` is `γₓ` in notes
  refine ⟨γ₁, _⟩,
  have hbV : ∀ᶠ x near K, x ∈ V, sorry,
  refine ⟨_, hgK.and hbV, ⟨⟨by simp [γ₁, hγ₀0], by simp [γ₁, h2γ₀0], _, _⟩, _⟩, _⟩,
  { rintro x ⟨hx, -⟩, rw [hx],
    exact (hγ₀_surr.smul0 hε.ne').vadd0 },
  { refine hb.continuous.fst'.add (continuous_const.smul hγ₀_cont.snd') },
  { rintro x ⟨hx, h2x⟩ t ht s hs, sorry },
  { sorry, }
end

lemma exists_loops_aux2 [finite_dimensional ℝ E]
  (hK : is_compact K)
  (hΩ_op : is_open Ω)
  (hg : 𝒞 ∞ g) (hb : 𝒞 ∞ b)
  (hgK : ∀ᶠ x near K, g x = b x)
  (hconv : ∀ x, g x ∈ hull (connected_comp_in (prod.mk x ⁻¹' Ω) $ b x)) :
  ∃ (γ : E → ℝ → loop F), surrounding_family_in g b γ univ Ω ∧ 𝒞 ∞ ↿γ ∧
  (∀ x (t ≤ 0), γ x t = γ x 0) ∧ (∀ x (t ≥ 1), γ x t = γ x 1) ∧
  ∀ᶠ x near K, ∀ t s, closed_ball (x, b x) (dist (γ x t s) (b x)) ⊆ Ω :=
begin
  have b_in : ∀ x, (x, b x) ∈ Ω :=
    λ x, (connected_comp_in_nonempty_iff.mp (convex_hull_nonempty_iff.mp ⟨g x, hconv x⟩) : _),
  have h2Ω : is_open (Ω ∩ fst ⁻¹' univ), { rwa [preimage_univ, inter_univ] },
  -- have bK_im : (λ x, (x, b x)) '' K ⊆ Ω := image_subset_iff.mpr (λ x _, b_in x),
  -- have h2Ω_op : ∀ x, is_open (prod.mk x ⁻¹' Ω),
  --  from λ x, hΩ_op.preimage (continuous.prod.mk x),

  -- choose a volume on E
  letI : measurable_space E := borel E,
  haveI : borel_space E := ⟨rfl⟩,
  letI K₀ : positive_compacts E,
  { refine ⟨⟨closed_ball 0 1, is_compact_closed_ball 0 1⟩, _⟩,
    rw [interior_closed_ball, nonempty_ball], all_goals { norm_num } },
  letI : measure_space E := ⟨add_haar_measure K₀⟩,
  -- haveI : is_add_haar_measure (volume : measure E) :=
  --   infer_instance,

  obtain ⟨γ₁, V, hV, hγ₁, h2γ₁⟩ := exists_loops_aux1 hK hΩ_op hg hb hgK hconv,
  obtain ⟨γ₂, hγ₂, hγ₂₁⟩ :=
    exists_surrounding_loops hK is_closed_univ is_open_univ subset.rfl h2Ω
    (λ x hx, hg.continuous.continuous_at) hb.continuous (λ x _, hconv x) ⟨V, hV, hγ₁⟩,
  let γ₃ : E → ℝ → loop F := λ x t, (γ₂ x (linear_reparam t)).reparam linear_reparam,
  let ε₁ : E → ℝ := λ x, ⨅ y : ℝ × ℝ, inf_dist (x, γ₂ x y.1 y.2) Ωᶜ, -- todo
  have hε₁ : continuous ε₁ := sorry, -- (continuous_inf_dist_pt _).comp (continuous_id.prod_mk hg.continuous),
  have h2ε₁ : ∀ {x}, 0 < ε₁ x, sorry,
  obtain ⟨ε₂, hε₂, h2ε₂⟩ := exists_smooth_pos is_open_univ hε₁ (λ x _, h2ε₁),
  have h2ε₂ : ∀ {x}, 0 < ε₂ x := λ x, h2ε₂ x (mem_univ _),
  let φ : E × ℝ × ℝ → ℝ :=
  λ x, (⟨⟨ε₂ x.1 / 2, ε₂ x.1, half_pos h2ε₂, half_lt_self h2ε₂⟩⟩ : cont_diff_bump (0 : E × ℝ × ℝ)) x,
  let γ₄ := ↿γ₃,
  let γ₅ : E × ℝ × ℝ → F := φ ⋆ γ₄,
  let γ₆ : ℝ → E → loop F,
  { refine λ s x, ⟨λ t, γ₅ (x, s, t), λ t, _⟩,
    change ∫ u, φ u • γ₃ (x - u.1) (s - u.2.1) (t + 1 - u.2.2) =
      ∫ u, φ u • γ₃ (x - u.1) (s - u.2.1) (t - u.2.2),
    simp_rw [← sub_add_eq_add_sub, (γ₃ _ _).per] },
  -- todo: apply reparametrization

  sorry
end

@[simp] lemma smul_add_one_sub_smul {R M : Type*} [ring R] [add_comm_monoid M] [module R M]
  {r : R} {m : M} : r • m + (1 - r) • m = m :=
by rw [← add_smul, add_sub_cancel'_right, one_smul]

@[simp] lemma dist_prod_same_left {x : E} {y₁ y₂ : F} : dist (x, y₁) (x, y₂) = dist y₁ y₂ :=
by simp [prod.dist_eq, dist_nonneg]

lemma dist_smul_add_one_sub_smul_le {r : ℝ} {x y : E} (h : r ∈ unit_interval) :
  dist (r • x + (1 - r) • y) x ≤ dist y x :=
by sorry

lemma exists_loops [finite_dimensional ℝ E]
  (hK : is_compact K)
  (hΩ_op : is_open Ω)
  (hg : 𝒞 ∞ g) (hb : 𝒞 ∞ b)
  (hgK : ∀ᶠ x near K, g x = b x)
  (hconv : ∀ x, g x ∈ hull (connected_comp_in (prod.mk x ⁻¹' Ω) $ b x)) :
  ∃ γ : ℝ → E → loop F, nice_loop g b Ω K γ :=
begin
  obtain ⟨γ₁, hγ₁, hsγ₁, h2γ₁, h3γ₁, h4γ₁⟩ := exists_loops_aux2 hK hΩ_op hg hb hgK hconv,
  let γ₂ : smooth_surrounding_family g :=
    ⟨λ x, γ₁ x 1, hsγ₁.comp₃ cont_diff_fst cont_diff_const cont_diff_snd,
      λ x, hγ₁.surrounds x (mem_univ _)⟩,
  let γ₃ : ℝ → E → loop F :=
  λ t x, (γ₁ x t).reparam $ (γ₂.reparametrize x).equivariant_map,
  have hγ₃ : 𝒞 ∞ ↿γ₃ :=
    hsγ₁.comp₃ cont_diff_snd.fst cont_diff_fst (γ₂.reparametrize_smooth.snd'),
  obtain ⟨χ, hχ, h1χ, h0χ, h2χ⟩ := exists_cont_diff_one_nhds_of_interior hK.is_closed
    (subset_interior_iff_mem_nhds_set.mpr $ hgK.and h4γ₁),
  simp_rw [← or_iff_not_imp_left] at h0χ,
  let γ : ℝ → E → loop F :=
  λ t x, χ x • loop.const (b x) + (1 - χ x) • γ₃ t x,
  have h1γ : ∀ x, ∀ t ≤ 0, γ t x = γ 0 x,
  { intros x t ht, ext s, simp [h2γ₁ _ _ ht] },
  have h2γ : ∀ x, ∀ t ≥ 1, γ t x = γ 1 x,
  { intros x t ht, ext s, simp [h3γ₁ _ _ ht] },
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
