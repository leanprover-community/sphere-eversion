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
  (hF₀A : ∀ᶠ x near A, (F 0).is_holonomic_at x)
  (hFF₀δ : ∀ t x, dist ((F t).bs x) ((F 0).bs x) < δ x)
  (hFφψ : ∀ t, (F t).bs '' (range φ) ⊆ range ψ)
  (hFA : ∀ t, ∀ᶠ x near A, F t x = F 0 x)
  (hFC : ∀ᶠ x near C, (F 1).is_holonomic_at x)
  {K₀ K₁ : set EM}
  (hK₀ : is_compact K₀)
  (hK₁ : is_compact K₁)
  (hK₀K₁ : K₀ ⊆ interior K₁) :
  ∃ F' : htpy_formal_sol R,
    F' 0 = F 0 ∧
    (∀ t, ∀ᶠ x near A, (F' t) x = F 0 x) ∧
    (∀ t, ∀ᶠ x near C, (F' t) x = F t x) ∧
    (∀ t, ∀ x ∉ φ '' K₁, F' t x = F t x) ∧
    (∀ t x, dist ((F' t).bs x) ((F 0).bs x) < δ x) ∧
    ∀ᶠ x near A ∪ φ '' K₀, (F' 1).is_holonomic_at x :=
begin
  let Rloc : rel_loc EM EX := (R.localize φ ψ).rel_loc,
  have hRloc_op : is_open Rloc,
  sorry { exact  is_open_of_is_open _ (hRopen.preimage $ one_jet_bundle.continuous_transfer _ _) },
  have hRloc_ample : Rloc.is_ample,
  sorry { exact ample_of_ample _ (hRample.localize _ _) },
  -- TODO: try to be consistent about how to state the hFφψ condition
  replace hFφψ : ∀ (t : ℝ), range ((F t).bs ∘ φ) ⊆ range ψ,
  sorry { intro t,
    rw range_comp,
    exact hFφψ t },
  let p : chart_pair IM M IX X :=
  { φ := φ,
    ψ := ψ,
    K₁ := K₁,
    hK₁ := hK₁ },
  let 𝓕 : Rloc.htpy_formal_sol := F.localize p hFφψ,
  let 𝓕' : Rloc.htpy_formal_sol := sorry, -- coming from Chapter 2
  have hcompat : p.compat F 𝓕',
  {
    sorry },
  have h𝓕'rel : ∀ t, ∀ x ∉ closed_ball (0 : EM) 2, 𝓕' t x = F.localize p hFφψ t x,
  {
    sorry },
  have h𝓕'relA : ∀ t, ∀ᶠ x near φ ⁻¹' A, 𝓕' t x = F.localize p hFφψ 0 x,
  {
    sorry },
  have h𝓕'relA' : ∀ t, ∀ᶠ x near A, ∀ e, x = φ e → 𝓕' t e = F.localize p hFφψ 0 e,
  {
    sorry },
  have h𝓕'relC : ∀ t, ∀ᶠ x near C, ∀ e, x = φ e → 𝓕' t e = F.localize p hFφψ t e,
  {
    sorry },
  have h𝓕'₀ : 𝓕' 0 = 𝓕 0,
  {
    sorry },
  have h𝓕'hol : ∀ᶠ x near A ∪ φ '' K₀, ∀ e, x = φ e → (𝓕' 1).is_holonomic_at e,
  {
    sorry },
  let F' : htpy_formal_sol R := p.update F 𝓕',
  refine ⟨p.update F 𝓕', _, _, _, _, _, _⟩,
  sorry { rw p.update_eq_of_forall F 𝓕' (λ _, _),
    rw h𝓕'₀,
    refl, },
  sorry { intros t,
    apply ((h𝓕'relA' t).and $ hFA t).mono,
    rintros x ⟨H, H'⟩,
    by_cases hx : x ∈ range φ,
    { rcases hx with ⟨e, rfl⟩,
      have : ∀ (hF : p.accepts F), (𝓕' t) e = ((F.localize p hF) t) e,
      { intros hF,
        rw [H e rfl, htpy_formal_sol.localize_eq_of_eq p F hF H'],
        refl },
      rw p.update_eq_of_eq F 𝓕' this,
      exact H' },
    { rw [p.update_eq_of_not_mem, H'],
      exact  (λ hx', hx (mem_range_of_mem_image φ _ hx')) } },
  sorry { intro t,
    apply (h𝓕'relC t).mono,
    intros x H,
    by_cases hx : x ∈ range φ,
    { rcases hx with ⟨e, rfl⟩,
      rw [p.update_eq_of_eq F 𝓕' (λ hF, _)],
      rw H e rfl,
      refl },
    { rw [p.update_eq_of_not_mem],
      exact (λ hx', hx (mem_range_of_mem_image φ _ hx')) } },
  sorry { exact λ _ _, p.update_eq_of_not_mem _ _ },
  {
    sorry },
  sorry { rw [nhds_set_union, eventually_sup] at h𝓕'hol ⊢,
    clear hFF₀δ h𝓕'rel h𝓕'relA h𝓕'relA' h𝓕'relC hFC hδ_pos hδ_cont δ hRloc_op hRloc_ample hRample hRopen,
    split,
    { apply ((h𝓕'hol.1.eventually_nhds_set.and (hFA 1).eventually_nhds_set).and hF₀A).mono, clear h𝓕'hol,
      intros x H,
      by_cases hx : x ∈ range φ,
      { rcases hx with ⟨e, rfl⟩,
        rw p.update_is_holonomic_at_iff hcompat,
        exact (H.1.1.self_of_nhds e rfl) },
      { rw p.update_is_holonomic_at_iff' hx hcompat,
        exact H.2.congr (eventually_eq.symm H.1.2) } },
    { have : ∀ᶠ x near φ '' K₀, x ∈ range p.φ,
      { exact p.φ.is_open_range.forall_near_mem_of_subset (image_subset_range _ _) },
      apply (this.and h𝓕'hol.2).mono,
      rintros x ⟨⟨e, rfl⟩, H⟩,
      rw p.update_is_holonomic_at_iff hcompat,
      exact H e rfl } },
end
