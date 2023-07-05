import to_mathlib.partition

noncomputable theory

open_locale topological_space filter manifold big_operators
open set function filter



section
variables {ι : Type*}
variables {E : Type*} [normed_add_comm_group E] [normed_space ℝ E] [finite_dimensional ℝ E]
  {H : Type*} [topological_space H] {I : model_with_corners ℝ E H} {M : Type*}
  [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
  [sigma_compact_space M] [t2_space M]


section

variables {F : Type*} [add_comm_group F] [module ℝ F]

lemma exists_of_convex {P : (Σ x : M, germ (𝓝 x) F) → Prop}
  (hP : ∀ x, really_convex (smooth_germ I x) {φ | P ⟨x, φ⟩})
  (hP' : ∀ x : M, ∃ f : M → F, ∀ᶠ x' in 𝓝 x, P ⟨x', f⟩) : ∃ f : M → F, ∀ x, P ⟨x, f⟩ :=
begin
  replace hP' : ∀ x : M, ∃ f : M → F, ∃ U ∈ 𝓝 x, ∀ x' ∈ U, P ⟨x', f⟩,
  { intros x,
    rcases hP' x with ⟨f, hf⟩,
    exact ⟨f, {x' | P ⟨x', ↑f⟩}, hf, λ _, id⟩ },
  choose φ U hU hφ using hP',
  rcases smooth_bump_covering.exists_is_subordinate I is_closed_univ (λ x h, hU x) with ⟨ι, b, hb⟩,
  let ρ := b.to_smooth_partition_of_unity,
  refine ⟨λ x : M, (∑ᶠ i, (ρ i x) • φ (b.c i) x), λ x₀, _⟩,
  let g : ι → germ (𝓝 x₀) F := λ i, φ (b.c i),
  have : ((λ x : M, (∑ᶠ i, (ρ i x) • φ (b.c i) x)) : germ (𝓝 x₀) F) ∈
    really_convex_hull (smooth_germ I x₀) (g '' (ρ.fintsupport x₀)),
    from ρ.germ_combine_mem (λ i x, φ (b.c i) x),
  simp_rw [really_convex_iff_hull] at hP,
  apply hP x₀, clear hP,
  have H : g '' ↑(ρ.fintsupport x₀) ⊆ {φ : (𝓝 x₀).germ F | P ⟨x₀, φ⟩},
  { rintros _ ⟨i, hi, rfl⟩,
    exact hφ _ _ (smooth_bump_covering.is_subordinate.to_smooth_partition_of_unity hb i $
      (ρ.mem_fintsupport_iff _ i).mp hi) },
  exact really_convex_hull_mono H this,
end

end

variables {F : Type*} [normed_add_comm_group F] [normed_space ℝ F]
variables {G : Type*} [normed_add_comm_group G] [normed_space ℝ G]
  {HG : Type*} [topological_space HG] (IG : model_with_corners ℝ G HG) {N : Type*}
  [topological_space N] [charted_space HG N] [smooth_manifold_with_corners IG N]

local notation `𝓒` := cont_mdiff I 𝓘(ℝ, F)
local notation `𝓒_on` := cont_mdiff_on I 𝓘(ℝ, F)

variable (I)


lemma really_convex_cont_mdiff_at (x : M) (n : ℕ∞) :
  really_convex (smooth_germ I x) {φ : germ (𝓝 x) F | φ.cont_mdiff_at I n} :=
begin
  classical,
  rw [nontrivial.really_convex_iff],
  rintros w w_pos w_supp w_sum,
  have : (support w).finite := support_finite_of_finsum_eq_one w_sum,
  let fin_supp := this.to_finset,
  have : support (λ (i : (𝓝 x).germ F), w i • i) ⊆ fin_supp,
  { rw set.finite.coe_to_finset, exact support_smul_subset_left w id },
  rw finsum_eq_sum_of_support_subset _ this, clear this,
  apply filter.germ.cont_mdiff_at.sum,
  intros φ hφ,
  refine (smooth_germ.cont_mdiff_at _).smul (w_supp _),
  simpa [fin_supp] using hφ
end

lemma exists_cont_mdiff_of_convex
  {P : M → F → Prop} (hP : ∀ x, convex ℝ {y | P x y})
  {n : ℕ∞}
  (hP' : ∀ x : M, ∃ U ∈ 𝓝 x, ∃ f : M → F, 𝓒_on n f U ∧ ∀ x ∈ U, P x (f x)) :
  ∃ f : M → F, 𝓒 n f ∧ ∀ x, P x (f x) :=
begin
  let PP : (Σ x : M, germ (𝓝 x) F) → Prop := λ p, p.2.cont_mdiff_at I n ∧ P p.1 p.2.value,
  have hPP : ∀ x, really_convex (smooth_germ I x) {φ | PP ⟨x, φ⟩},
  { intros x,
    apply really_convex.inter,
    apply really_convex_cont_mdiff_at,
    dsimp only,
    let v : germ (𝓝 x) F →ₛₗ[smooth_germ.value_ring_hom I x] F := filter.germ.valueₛₗ I x,
    change really_convex (smooth_germ I x) (v ⁻¹' {y | P x y}),
    dsimp only [← smooth_germ.value_order_ring_hom_to_ring_hom] at v,
    apply really_convex.preimageₛₗ,
    rw [really_convex_iff_convex],
    apply hP },
  have hPP' : ∀ x, ∃ f : M → F, ∀ᶠ x' in 𝓝 x, PP ⟨x', f⟩,
  { intro x,
    rcases hP' x with ⟨U, U_in, f, hf, hf'⟩,
    use f,
    filter_upwards [eventually_mem_nhds.mpr U_in] with y hy,
    exact ⟨hf.cont_mdiff_at hy, hf' y (mem_of_mem_nhds hy)⟩ },
  rcases exists_of_convex hPP hPP' with ⟨f, hf⟩,
  exact ⟨f, λ x, (hf x).1, λ x, (hf x).2⟩
end

lemma exists_cont_diff_of_convex
  {P : E → F → Prop} (hP : ∀ x, convex ℝ {y | P x y})
  {n : ℕ∞}
  (hP' : ∀ x : E, ∃ U ∈ 𝓝 x, ∃ f : E → F, cont_diff_on ℝ n f U ∧ ∀ x ∈ U, P x (f x)) :
  ∃ f : E → F, cont_diff ℝ n f ∧ ∀ x, P x (f x) :=
begin
  simp_rw ← cont_mdiff_iff_cont_diff,
  simp_rw ← cont_mdiff_on_iff_cont_diff_on  at ⊢ hP',
  exact exists_cont_mdiff_of_convex hP hP'
end
end

section

variables {E₁ E₂ E₃ E₄ F : Type*}
variables [normed_add_comm_group E₁] [normed_space ℝ E₁] [finite_dimensional ℝ E₁]
variables [normed_add_comm_group E₂] [normed_space ℝ E₂] [finite_dimensional ℝ E₂]
variables [normed_add_comm_group E₃] [normed_space ℝ E₃] [finite_dimensional ℝ E₃]
variables [normed_add_comm_group E₄] [normed_space ℝ E₄] [finite_dimensional ℝ E₄]
variables [normed_add_comm_group F] [normed_space ℝ F]

variables {H₁ M₁ H₂ M₂ H₃ M₃ H₄ M₄ : Type*}
variables [topological_space H₁] (I₁ : model_with_corners ℝ E₁ H₁)
variables [topological_space M₁] [charted_space H₁ M₁] [smooth_manifold_with_corners I₁ M₁]
variables [sigma_compact_space M₁] [t2_space M₁]
variables [topological_space H₂] (I₂ : model_with_corners ℝ E₂ H₂)
variables [topological_space M₂] [charted_space H₂ M₂] [smooth_manifold_with_corners I₂ M₂]
variables [topological_space H₃] (I₃ : model_with_corners ℝ E₃ H₃)
variables [topological_space M₃] [charted_space H₃ M₃] [smooth_manifold_with_corners I₃ M₃]
variables [topological_space H₄] (I₄ : model_with_corners ℝ E₄ H₄)
variables [topological_space M₄] [charted_space H₄ M₄] [smooth_manifold_with_corners I₄ M₄]

local notation `𝓒` := cont_mdiff (I₁.prod I₂) 𝓘(ℝ, F)
local notation `𝓒_on` := cont_mdiff_on (I₁.prod I₂) 𝓘(ℝ, F)

lemma really_convex_cont_mdiff_at_prod {x : M₁} (n : ℕ∞) :
  really_convex (smooth_germ I₁ x) {φ : germ (𝓝 x) (M₂ → F) | φ.cont_mdiff_at_prod I₁ I₂ n} :=
begin
  classical,
  rw [nontrivial.really_convex_iff],
  rintros w w_pos w_supp w_sum,
  have : (support w).finite := support_finite_of_finsum_eq_one w_sum,
  let fin_supp := this.to_finset,
  have : support (λ (i : (𝓝 x).germ (M₂ → F)), w i • i) ⊆ fin_supp,
  { rw set.finite.coe_to_finset,
    exact support_smul_subset_left w id },
  rw finsum_eq_sum_of_support_subset _ this, clear this,
  apply filter.germ.cont_mdiff_at_prod.sum,
  intros φ hφ,
  refine (smooth_germ.cont_mdiff_at _).smul_prod (w_supp _),
  simpa [fin_supp] using hφ
end

@[main_declaration]
lemma exists_cont_mdiff_of_convex₂
  {P : M₁ → (M₂ → F) → Prop} (hP : ∀ x, convex ℝ {f | P x f}) {n : ℕ∞}
  (hP' : ∀ x : M₁, ∃ (U ∈ 𝓝 x) (f : M₁ → M₂ → F),
    𝓒_on n (uncurry f) (U ×ˢ (univ : set M₂)) ∧ ∀ y ∈ U, P y (f y)) :
  ∃ f : M₁ → M₂ → F, 𝓒 n (uncurry f) ∧ ∀ x, P x (f x) :=
begin
  let PP : (Σ x : M₁, germ (𝓝 x) (M₂ → F)) → Prop :=
    λ p, p.2.cont_mdiff_at_prod I₁ I₂ n ∧ P p.1 p.2.value,
  have hPP : ∀ x, really_convex (smooth_germ I₁ x) {φ | PP ⟨x, φ⟩},
  { intros x,
    apply really_convex.inter,
    apply really_convex_cont_mdiff_at_prod,
    dsimp only,
    let v : germ (𝓝 x) (M₂ → F) →ₛₗ[smooth_germ.value_ring_hom I₁ x] (M₂ → F) :=
      filter.germ.valueₛₗ I₁ x,
    change really_convex (smooth_germ I₁ x) (v ⁻¹' {y | P x y}),
    dsimp only [← smooth_germ.value_order_ring_hom_to_ring_hom] at v,
    apply really_convex.preimageₛₗ,
    rw [really_convex_iff_convex],
    apply hP },
  have hPP' : ∀ x, ∃ f : M₁ → M₂ → F, ∀ᶠ x' in 𝓝 x, PP ⟨x', f⟩,
  { intro x,
    rcases hP' x with ⟨U, U_in, f, hf, hf'⟩,
    use f,
    filter_upwards [eventually_mem_nhds.mpr U_in] with y hy,
    refine ⟨λz, hf.cont_mdiff_at (prod_mem_nhds hy univ_mem), hf' y (mem_of_mem_nhds hy)⟩ },
  rcases exists_of_convex hPP hPP' with ⟨f, hf⟩,
  exact ⟨f, λ ⟨x, y⟩, (hf x).1 y, λ x, (hf x).2⟩
end

lemma exists_cont_diff_of_convex₂
  {P : E₁ → (E₂ → F) → Prop} (hP : ∀ x, convex ℝ {f | P x f}) {n : ℕ∞}
  (hP' : ∀ x : E₁, ∃ (U ∈ 𝓝 x) (f : E₁ → E₂ → F),
    cont_diff_on ℝ n (uncurry f) (U ×ˢ (univ : set E₂)) ∧ ∀ y ∈ U, P y (f y)) :
  ∃ f : E₁ → E₂ → F, cont_diff ℝ n (uncurry f) ∧ ∀ x, P x (f x) :=
begin
  simp_rw [← cont_mdiff_on_iff_cont_diff_on, model_with_corners_self_prod] at hP',
  simp_rw [← cont_mdiff_iff_cont_diff, model_with_corners_self_prod],
  rw [← charted_space_self_prod] at hP' ⊢, -- Why does `simp_rw` not succeed here?
  exact exists_cont_mdiff_of_convex₂ 𝓘(ℝ, E₁) 𝓘(ℝ, E₂) hP hP',
end
end

section
variables {ι : Type*}
variables {E : Type*} [normed_add_comm_group E] [normed_space ℝ E] [finite_dimensional ℝ E]
  {H : Type*} [topological_space H] {I : model_with_corners ℝ E H} {M : Type*}
  [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
  [sigma_compact_space M] [t2_space M]

open topological_space

example {f : E → ℝ} (h : ∀ x : E, ∃ U ∈ 𝓝 x, ∃ ε : ℝ, ∀ x' ∈ U, 0 < ε ∧ ε ≤ f x') :
  ∃ f' : E → ℝ, cont_diff ℝ ⊤ f' ∧ ∀ x, (0 < f' x ∧ f' x ≤ f x) :=
begin
  let P : E → ℝ → Prop := λ x t, 0 < t ∧ t ≤ f x,
  have hP : ∀ x, convex ℝ {y | P x y}, from λ x, convex_Ioc _ _,
  apply exists_cont_diff_of_convex hP,
  intros x,
  rcases h x with ⟨U, U_in, ε, hU⟩,
  exact ⟨U, U_in, λ x, ε, cont_diff_on_const, hU⟩
end

variables {F : Type*} [normed_add_comm_group F] [normed_space ℝ F]

lemma convex_set_of_imp_eq (P : Prop) (y : F) : convex ℝ {x : F | P → x = y } :=
by by_cases hP : P; simp [hP, convex_singleton, convex_univ]

-- lemma exists_smooth_and_eq_on_aux1 {f : E → F} {ε : E → ℝ} (hf : continuous f)
--   (hε : continuous ε) (h2ε : ∀ x, 0 < ε x) (x₀ : E) :
--   ∃ U ∈ 𝓝 x₀, ∀ x ∈ U, dist (f x₀) (f x) < ε x :=
-- begin
--   have h0 : ∀ x, dist (f x) (f x) < ε x := λ x, by simp_rw [dist_self, h2ε],
--   refine ⟨_, (is_open_lt (continuous_const.dist hf) hε).mem_nhds $ h0 x₀, λ x hx, hx⟩
-- end

-- lemma exists_smooth_and_eq_on_aux2 {n : ℕ∞} {f : E → F} {ε : E → ℝ} (hf : continuous f)
--   (hε : continuous ε) (h2ε : ∀ x, 0 < ε x)
--   {s : set E} (hs : is_closed s) (hfs : ∃ U ∈ 𝓝ˢ s, cont_diff_on ℝ n f U)
--   (x₀ : E) :
--   ∃ U ∈ 𝓝 x₀, ∀ x ∈ U, dist (f x₀) (f x) < ε x :=
-- begin
--   have h0 : ∀ x, dist (f x) (f x) < ε x := λ x, by simp_rw [dist_self, h2ε],
--   refine ⟨_, (is_open_lt (continuous_const.dist hf) hε).mem_nhds $ h0 x₀, λ x hx, hx⟩
-- end

lemma exists_smooth_and_eq_on {n : ℕ∞} {f : E → F} {ε : E → ℝ} (hf : continuous f)
  (hε : continuous ε) (h2ε : ∀ x, 0 < ε x)
  {s : set E} (hs : is_closed s) (hfs : ∃ U ∈ 𝓝ˢ s, cont_diff_on ℝ n f U) :
  ∃ f' : E → F, cont_diff ℝ n f' ∧ (∀ x, dist (f' x) (f x) < ε x) ∧ eq_on f' f s :=
begin
  have h0 : ∀ x, dist (f x) (f x) < ε x := λ x, by simp_rw [dist_self, h2ε],
  let P : E → F → Prop := λ x t, dist t (f x) < ε x ∧ (x ∈ s → t = f x),
  have hP : ∀ x, convex ℝ {y | P x y} :=
    λ x, (convex_ball (f x) (ε x)).inter (convex_set_of_imp_eq _ _),
  obtain ⟨f', hf', hPf'⟩ := exists_cont_diff_of_convex hP _,
  { exact ⟨f', hf', λ x, (hPf' x).1, λ x, (hPf' x).2⟩ },
  { intros x,
    obtain ⟨U, hU, hfU⟩ := hfs,
    by_cases hx : x ∈ s,
    { refine ⟨U, mem_nhds_set_iff_forall.mp hU x hx, _⟩,
      refine ⟨f, hfU, λ y _, ⟨h0 y, λ _, rfl⟩⟩ },
    { have : is_open {y : E | dist (f x) (f y) < ε y} := is_open_lt (continuous_const.dist hf) hε,
      exact ⟨_, (this.sdiff hs).mem_nhds ⟨h0 x, hx⟩, λ _, f x, cont_diff_on_const,
        λ y hy, ⟨hy.1, λ h2y, (hy.2 h2y).elim⟩⟩ } },
end

end
