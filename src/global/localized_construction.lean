import global.localisation

noncomputable theory

open set filter model_with_corners metric
open_locale topological_space manifold

set_option trace.filter_inst_type true

variables
{EM : Type*} [normed_add_comm_group EM] [normed_space ℝ EM] [finite_dimensional ℝ EM]
{HM : Type*} [topological_space HM] {IM : model_with_corners ℝ EM HM} [boundaryless IM]
{M : Type*} [topological_space M] [charted_space HM M] [smooth_manifold_with_corners IM M]
[t2_space M]
[locally_compact_space M] -- FIXME: investigate how to deduce this from finite-dimensional
[nonempty M] -- FIXME: investigate how to remove this
[sigma_compact_space M]

{EX : Type*} [normed_add_comm_group EX] [normed_space ℝ EX] [finite_dimensional ℝ EX]
  [measurable_space EX] [borel_space EX]
{HX : Type*} [topological_space HX] {IX : model_with_corners ℝ EX HX} [model_with_corners.boundaryless IX]
-- note: X is a metric space
{X : Type*} [metric_space X] [charted_space HX X] [smooth_manifold_with_corners IX X]
[locally_compact_space X] -- FIXME: investigate how to deduce this from finite-dimensional
[sigma_compact_space X]
[nonempty X] -- FIXME: investigate how to remove this

lemma filter.eventually.forall {α β : Type*} {P : β → α → Prop} {A : filter α}
  (h : ∀ᶠ a in A, ∀ b, P b a) (b : β) : ∀ᶠ a in A, P b a :=
begin
  rw [filter.eventually, set_of_forall] at h,
  apply mem_of_superset h,
  intros a ha,
  rw [mem_Inter] at ha,
  exact ha b
end

open_locale unit_interval

lemma open_smooth_embedding.improve_htpy_formal_sol
  (φ : open_smooth_embedding 𝓘(ℝ, EM) EM IM M)
  (ψ : open_smooth_embedding 𝓘(ℝ, EX) EX IX X)
  {R : rel_mfld IM M IX X}
  (hRample : R.ample)
  (hRopen : is_open R)
  {A C : set M}
  (hA : is_closed A)
  (hC : is_closed C)
  {δ : M → ℝ}
  (hδ_pos : ∀ x, 0 < δ x)
  (hδ_cont : continuous δ)
  {F : htpy_formal_sol R}
  (hFt0 : ∀ᶠ t near Iic (0 : ℝ), F t = F 0)
  (hFt1 : ∀ᶠ t near Ici (1 : ℝ), F t = F 1)
  (hF₀A : ∀ᶠ x near A, (F 0).is_holonomic_at x)
  (hFF₀δ : ∀ t x, dist ((F t).bs x) ((F 0).bs x) < δ x)
  (hFφψ : ∀ t, (F t).bs '' (range φ) ⊆ range ψ)
  (hFA : ∀ᶠ x near A, ∀ t, F t x = F 0 x)
  (hFC : ∀ᶠ x near C, (F 1).is_holonomic_at x)
  {K₀ K₁ : set EM}
  (hK₀ : is_compact K₀)
  (hK₁ : is_compact K₁)
  (hK₀K₁ : K₀ ⊆ interior K₁) :
  ∃ F' : htpy_formal_sol R,
    (∀ᶠ t near Iic (0 : ℝ), F' t = F 0) ∧
    (∀ᶠ t near Ici (1 : ℝ), F' t = F' 1) ∧
    (∀ᶠ x near A, ∀ t, (F' t) x = F 0 x) ∧
    (∀ t, ∀ x ∉ φ '' K₁, F' t x = F t x) ∧
    (∀ t x, dist ((F' t).bs x) ((F 0).bs x) < δ x) ∧
    ∀ᶠ x near A ∪ (C ∪ φ '' K₀), (F' 1).is_holonomic_at x :=
begin
  let Rloc : rel_loc EM EX := (R.localize φ ψ).rel_loc,
  have hRloc_op : is_open Rloc,
  { exact  is_open_of_is_open _ (hRopen.preimage $ one_jet_bundle.continuous_transfer _ _) },
  have hRloc_ample : Rloc.is_ample,
  { exact ample_of_ample _ (hRample.localize _ _) },
  -- TODO: try to be consistent about how to state the hFφψ condition
  replace hFφψ : ∀ (t : ℝ), range ((F t).bs ∘ φ) ⊆ range ψ,
  { intro t,
    rw range_comp,
    exact hFφψ t },
  let p : chart_pair IM M IX X :=
  { φ := φ,
    ψ := ψ,
    K₁ := K₁,
    hK₁ := hK₁ },
  let δ' : M → ℝ := λ x, δ x - dist ((F 1).bs x) ((F 0).bs x),
  have δ'_pos : ∀ x, 0 < δ' x,
  { intros x,
    exact sub_pos.mpr (hFF₀δ 1 x) },
  have δ'_cont : continuous δ',
  { exact hδ_cont.sub (continuous.dist (F.smooth_bs.continuous.comp (continuous.prod.mk 1))
                                       (F.smooth_bs.continuous.comp (continuous.prod.mk 0))) },
  rcases p.dist_update δ'_pos δ'_cont hFφψ with ⟨τ, τ_pos, hτ⟩,
  let 𝓕 : Rloc.htpy_formal_sol := F.localize p hFφψ,
  have h𝓕t0 : ∀ᶠ t near Iic (0 : ℝ), 𝓕 t = 𝓕 0,
  { apply hFt0.mono,
    intros t ht,
    exact htpy_formal_sol.localize_eq_of_eq' _ _ _ ht },
  have h𝓕t1 : ∀ᶠ t near Ici (1 : ℝ), 𝓕 t = 𝓕 1,
  { apply hFt1.mono,
    intros t ht,
    exact htpy_formal_sol.localize_eq_of_eq' _ _ _ ht },
  have h𝓕₀A :  ∀ᶠ e near φ ⁻¹' A, (𝓕 0).is_holonomic_at e ∧ ∀ t, 𝓕 t e = 𝓕 0 e,
  { rw eventually_nhds_set_iff at hF₀A hFA ⊢,
    intros e he,
    rw [φ.inducing.nhds_eq_comap, eventually_comap],
    apply ((hF₀A _ he).and $ hFA _ he).mono,
    rintros x hx e rfl,
    exact ⟨F.is_holonomic_localize p hFφψ e 0 hx.1, λ t, F.localize_eq_of_eq p hFφψ (hx.2 t)⟩ },
  let L : landscape EM :=
  { C := φ ⁻¹' C,
    K₀ := K₀,
    K₁ := K₁,
    hC := hC.preimage φ.continuous,
    hK₀ := hK₀,
    hK₁ := hK₁,
    h₀₁ := hK₀K₁ },
  have h𝓕C : ∀ᶠ (x : EM) near L.C, (𝓕 1).is_holonomic_at x,
  { rw eventually_nhds_set_iff at hFC ⊢,
    intros e he,
    rw [φ.inducing.nhds_eq_comap, eventually_comap],
    apply (hFC _ he).mono,
    rintros x hx e rfl,
    exact F.is_holonomic_localize p hFφψ e 1 hx },
  rcases 𝓕.improve hRloc_op hRloc_ample L τ_pos (hA.preimage φ.continuous) h𝓕₀A h𝓕C h𝓕t0 h𝓕t1
    with ⟨𝓕', h𝓕't0, h𝓕't1, h𝓕'relA, h𝓕'relK₁, h𝓕'dist, h𝓕'hol⟩,
  have hcompat : p.compat F 𝓕', from ⟨hFφψ, h𝓕'relK₁⟩,
  let F' : htpy_formal_sol R := p.update F 𝓕',
  have hF'relK₁ : ∀ t, ∀ x ∉ φ '' K₁, F' t x = F t x,
  { apply p.update_eq_of_not_mem },
  have hF't0 : ∀ᶠ (t : ℝ) near Iic 0, F' t = F 0,
  { apply (h𝓕t0.and $ h𝓕't0.and hFt0).mono,
    rintros t ⟨ht, ht', ht''⟩,
    rw p.update_eq_of_forall F 𝓕' (λ _, _),
    exact ht'',
    rw [ht', ← ht], refl },
  have hF't1 : ∀ᶠ (t : ℝ) near Ici 1, F' t = F' 1,
  { -- TODO: this proofs should use more congruence lemmas
    apply (hFt1.and h𝓕't1).mono,
    rintros t ⟨ht, ht'⟩,
    dsimp only [F', chart_pair.update],
    split_ifs,
    apply formal_sol.coe_inj,
    intros x,
    rcases classical.em (x ∈ range p.φ) with ⟨e, rfl⟩|hx,
    { simp only [open_smooth_embedding.update_htpy_formal_sol_apply_image],
      rw rel_loc.htpy_formal_sol.unloc_congr,
      rw ht' },
    { simp only [hx, open_smooth_embedding.update_htpy_formal_sol_apply_of_not_mem, not_false_iff],
      rw ht } },
  refine ⟨p.update F 𝓕', hF't0, hF't1, _, _, _, _⟩,
  { intros t,
    apply φ.forall_near hK₁ h𝓕'relA,
    { apply hFA.mono,
      intros x hx hx' t,
      rw hF'relK₁ t x hx',
      exact hx t },
    { intros e he t,
      rw p.update_eq_of_eq' _ _ hcompat,
      exact he t } },
  { exact hF'relK₁ },
  { have key : ∀ (e ∈ K₁) (t ∈ I), dist ((F' t).bs (φ e)) ((F 0).bs (φ e)) < δ (φ e),
    { intros e he t ht,
      rcases h𝓕'dist e t with ⟨t', ht'⟩|h,
      { convert hFF₀δ t' (φ e) using 2,
        change ((p.update F 𝓕') t _).1.2 = _,
        rw p.update_eq_of_eq' F 𝓕' hcompat ht',
        refl, },
      calc dist ((F' t).bs (φ e)) ((F 0).bs (φ e)) ≤ dist ((F' t).bs (φ e)) ((F 1).bs (φ e)) + dist ((F 1).bs (φ e)) ((F 0).bs (φ e)) : dist_triangle _ _ _
      ... < δ' (φ e) + dist ((F 1).bs (φ e)) ((F 0).bs (φ e)) : add_lt_add_right (hτ hcompat e he t ht h) _
      ... = (δ (φ e) - dist ((F 1).bs (φ e)) ((F 0).bs (φ e))) + dist ((F 1).bs (φ e)) ((F 0).bs (φ e)) : rfl
      ... = δ (φ e) : sub_add_cancel _ _ },
    intros t x,
    rcases classical.em (x ∈ φ '' K₁) with ⟨e, he, rfl⟩|hx,
    { by_cases ht : t ∈ (Icc 0 1 : set ℝ),
      { exact key e he t ht },
      { rw [mem_Icc, not_and_distrib, not_le, not_le] at ht,
        cases ht with ht ht,
        { erw [hF't0.on_set t ht.le, dist_self],
          apply hδ_pos },
        { rw [hF't1.on_set t ht.le],
          exact key e he _ unit_interval.one_mem } } },
    { convert hFF₀δ t x using 2,
      change ((p.update F 𝓕') t x).1.2 = _,
      rw p.update_eq_of_not_mem F 𝓕' hx,
      refl } },
  { rw [show L.K₀ = K₀, from rfl, ← preimage_image_eq K₀ φ.injective, ← preimage_union,
        ← preimage_union] at h𝓕'hol,
    apply φ.forall_near hK₁ h𝓕'hol, clear h𝓕'hol,
    rw [nhds_set_union, eventually_sup],
    split,
    { apply ((hFA.eventually_nhds_set).and hF₀A).mono,
      rintros x ⟨a, b⟩ c,
      apply (p.update_is_holonomic_at_iff' c hcompat).mpr,
      apply b.congr,
      apply a.mono,
      intros x hx,
      exact (hx 1).symm },
    { apply filter.eventually.union,
      { apply hFC.mono,
        intros x hx hx',
        apply hx.congr,
        symmetry,
        have : ∀ᶠ y in 𝓝 x, y ∈ (φ '' K₁)ᶜ,
        { exact is_open_iff_mem_nhds.mp (hK₁.image φ.continuous).is_closed.is_open_compl x hx' },
        apply this.mono,
        exact hF'relK₁ _ },
      { have : ∀ᶠ x near φ '' K₀, x ∈ p.φ '' K₁,
      { suffices : ∀ᶠ x near φ '' K₀, x ∈ interior (p.φ '' K₁), from this.mono interior_subset,
        apply is_open_interior.forall_near_mem_of_subset,
        exact (image_subset φ hK₀K₁).trans (φ.open_map.image_interior_subset K₁) },
        apply this.mono,
        exact λ a hx hx', (hx' hx).elim } },
    { exact λ _, (p.update_is_holonomic_at_iff hcompat).mpr } },
end
