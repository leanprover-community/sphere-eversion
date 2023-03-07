import global.localisation
import local.h_principle

noncomputable theory

open set filter model_with_corners metric
open_locale topological_space manifold

set_option trace.filter_inst_type true

variables
{EM : Type*} [normed_add_comm_group EM] [normed_space ℝ EM] [finite_dimensional ℝ EM]
{HM : Type*} [topological_space HM] {IM : model_with_corners ℝ EM HM} [boundaryless IM]
{M : Type*} [topological_space M] [charted_space HM M] [smooth_manifold_with_corners IM M]
[t2_space M] [locally_compact_space M] [nonempty M] [sigma_compact_space M]

{EX : Type*} [normed_add_comm_group EX] [normed_space ℝ EX] [finite_dimensional ℝ EX]
  [measurable_space EX] [borel_space EX]
{HX : Type*} [topological_space HX] {IX : model_with_corners ℝ EX HX} [model_with_corners.boundaryless IX]
-- note: X is a metric space
{X : Type*} [metric_space X] [charted_space HX X] [smooth_manifold_with_corners IX X]
[locally_compact_space X]
[sigma_compact_space X]
[nonempty X]

lemma open_smooth_embedding.improve_formal_sol
  (φ : open_smooth_embedding 𝓘(ℝ, EM) EM IM M)
  (ψ : open_smooth_embedding 𝓘(ℝ, EX) EX IX X)
  {R : rel_mfld IM M IX X}
  (hRample : R.ample)
  (hRopen : is_open R)
  {C : set M}
  (hC : is_closed C)
  {δ : M → ℝ}
  (hδ_pos : ∀ x, 0 < δ x)
  (hδ_cont : continuous δ)
  {F : formal_sol R}
  (hFφψ : F.bs '' (range φ) ⊆ range ψ)
  (hFC : ∀ᶠ x near C, F.is_holonomic_at x)
  {K₀ K₁ : set EM}
  (hK₀ : is_compact K₀)
  (hK₁ : is_compact K₁)
  (hK₀K₁ : K₀ ⊆ interior K₁) :
  ∃ F' : htpy_formal_sol R,
    (∀ᶠ t near Iic (0 : ℝ), F' t = F) ∧
    (∀ᶠ t near Ici (1 : ℝ), F' t = F' 1) ∧
    (∀ᶠ x near C, ∀ t, F' t x = F x) ∧
    (∀ t, ∀ x ∉ φ '' K₁, F' t x = F x) ∧
    (∀ t x, dist ((F' t).bs x) (F.bs x) < δ x) ∧
    ∀ᶠ x near C ∪ φ '' K₀, (F' 1).is_holonomic_at x :=
begin
  let Rloc : rel_loc EM EX := (R.localize φ ψ).rel_loc,
  have hRloc_op : is_open Rloc,
  { exact  is_open_of_is_open _ (hRopen.preimage $ one_jet_bundle.continuous_transfer _ _) },
  have hRloc_ample : Rloc.is_ample,
  { exact ample_of_ample _ (hRample.localize _ _) },
  -- TODO: try to be consistent about how to state the hFφψ condition
  replace hFφψ : range (F.bs ∘ φ) ⊆ range ψ,
  { rw range_comp,
    exact hFφψ },
  let p : chart_pair IM M IX X :=
  { φ := φ,
    ψ := ψ,
    K₁ := K₁,
    hK₁ := hK₁ },
  rcases p.dist_update' hδ_pos hδ_cont hFφψ with ⟨τ, τ_pos, hτ⟩,
  let 𝓕 := F.localize p hFφψ,
  let L : landscape EM :=
  { C := φ ⁻¹' C,
    K₀ := K₀,
    K₁ := K₁,
    hC := hC.preimage φ.continuous,
    hK₀ := hK₀,
    hK₁ := hK₁,
    h₀₁ := hK₀K₁ },
  have h𝓕C : ∀ᶠ (x : EM) near L.C, 𝓕.is_holonomic_at x,
  { rw eventually_nhds_set_iff at hFC ⊢,
    intros e he,
    rw [φ.inducing.nhds_eq_comap, eventually_comap],
    apply (hFC _ he).mono,
    rintros x hx e rfl,
    exact F.is_holonomic_localize p hFφψ e hx },
  rcases 𝓕.improve_htpy' hRloc_op hRloc_ample L τ_pos h𝓕C
    with ⟨𝓕', h𝓕't0, h𝓕't1, h𝓕'relC, h𝓕'relK₁, h𝓕'dist, h𝓕'hol⟩,
  have hcompat : p.compat' F 𝓕', from ⟨hFφψ, h𝓕'relK₁⟩,
  let F' : htpy_formal_sol R := p.mk_htpy F 𝓕',
  have hF'relK₁ : ∀ t, ∀ x ∉ φ '' K₁, F' t x = F x,
  { apply p.mk_htpy_eq_of_not_mem },
  have hF't0 : ∀ᶠ (t : ℝ) near Iic 0, F' t = F,
  { apply h𝓕't0.mono,
    rintros t ht,
    exact p.mk_htpy_eq_of_forall hcompat ht },
  have hF't1 : ∀ᶠ (t : ℝ) near Ici 1, F' t = F' 1,
  { exact h𝓕't1.mono (λ t, p.mk_htpy_congr _) },
  refine ⟨F', hF't0, hF't1, _, _, _, _⟩,
  { apply φ.forall_near hK₁ h𝓕'relC (eventually_of_forall $ λ x hx t, hF'relK₁ t x hx),
    { intros e he t,
      rw p.mk_htpy_eq_of_eq _ _ hcompat,
      exact he t } },
  { exact hF'relK₁ },
  { intros t x,
    rcases classical.em (x ∈ φ '' K₁) with ⟨e, he, rfl⟩|hx,
    { by_cases ht : t ∈ (Icc 0 1 : set ℝ),
      { exact hτ hcompat e he t ht (h𝓕'dist e t) },
      { rw [mem_Icc, not_and_distrib, not_le, not_le] at ht,
        cases ht with ht ht,
        { erw [hF't0.on_set t ht.le, dist_self],
          apply hδ_pos },
        { rw [hF't1.on_set t ht.le],
          exact hτ hcompat e he 1 (right_mem_Icc.mpr zero_le_one) (h𝓕'dist e 1) } } },
    { change dist ((F' t x).1.2) (F.bs x) < δ x,
      erw [p.mk_htpy_eq_of_not_mem _ _ hx, dist_self],
      apply hδ_pos } },
  { have h𝓕'holC : ∀ᶠ (x : EM) near L.C, (𝓕' 1).is_holonomic_at x,
    { apply (h𝓕'relC.eventually_nhds_set.and h𝓕C).mono,
      rintros x ⟨hx, hx'⟩,
      exact jet_sec.is_holonomic_at.congr hx' (hx.mono $ λ x' hx', (hx' 1).symm) },
    have : ∀ᶠ x near φ ⁻¹' C  ∪ K₀, (𝓕' 1).is_holonomic_at x := h𝓕'holC.union h𝓕'hol,
    rw [← preimage_image_eq K₀ φ.injective, ← preimage_union] at this,
    apply φ.forall_near hK₁ this,
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
    { exact λ _, (p.mk_htpy_is_holonomic_at_iff hcompat).mpr } },
end
