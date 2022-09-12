import to_mathlib.data.set.prod
import to_mathlib.data.nat.basic
import local.h_principle
import global.parametricity_for_free
import global.localisation

import interactive_expr

/-!
# Gromov's theorem

We prove the h-principle for open and ample first order differential relations.
-/

noncomputable theory

open set filter model_with_corners
open_locale topological_space manifold

variables
{EM : Type*} [normed_add_comm_group EM] [normed_space ℝ EM] [finite_dimensional ℝ EM]
{HM : Type*} [topological_space HM] {IM : model_with_corners ℝ EM HM} [boundaryless IM]
{M : Type*} [topological_space M] [charted_space HM M] [smooth_manifold_with_corners IM M]
[t2_space M]
[locally_compact_space M] -- FIXME: investigate how to deduce this from finite-dimensional
[nonempty M] -- FIXME: investigate how to remove this
[sigma_compact_space M]

{EX : Type*} [normed_add_comm_group EX] [normed_space ℝ EX] [finite_dimensional ℝ EX]
{HX : Type*} [topological_space HX] {IX : model_with_corners ℝ EX HX} [model_with_corners.boundaryless IX]
-- note: X is a metric space
{X : Type*} [metric_space X] [charted_space HX X] [smooth_manifold_with_corners IX X]
[locally_compact_space X] -- FIXME: investigate how to deduce this from finite-dimensional
[sigma_compact_space X]
[nonempty X] -- FIXME: investigate how to remove this

{R : rel_mfld IM M IX X}
{A : set M} {δ : M → ℝ}

set_option trace.filter_inst_type true

lemma rel_mfld.ample.satisfies_h_principle_core
  (hRample : R.ample) (hRopen : is_open R)
  (hA : is_closed A)
  (hδ_pos : ∀ (x : M), 0 < δ x)
  (hδ_cont : continuous δ)
  (F₀ : formal_sol R)
  (hF₀A : ∀ᶠ x near A, F₀.is_holonomic_at x)
  (L : localisation_data IM IX F₀.bs) :
  ∃ F : ℕ → htpy_formal_sol R, ∀ n : ℕ,
    ((F n 0 = F₀) ∧
    (∀ t, ∀ᶠ x near A, F n t x = F₀ x) ∧
    (∀ t x, dist ((F n t).bs x) (F₀.bs x) < δ x) ∧

    (∀ x ∈ ⋃ i ≤ L.index n, (L.φ i) '' metric.closed_ball 0 1,
      ((F n) 1).to_one_jet_sec.is_holonomic_at x)) ∧
    ((L.index (n + 1)  = L.index n → F (n + 1) = F n) ∧
     ∀ t (x ∉ range (L.φ $ L.index $ n+1)), F (n + 1) t x = F n t x) :=
begin
  classical,
  borelize EX,
  have cont_bs : continuous F₀.bs, from F₀.smooth_bs.continuous,
  have := L.ε_spec,
  let P : ℕ → htpy_formal_sol R → Prop := λ n Fn,
    (Fn 0 = F₀) ∧
    (∀ t, ∀ᶠ x near A, Fn t x = F₀ x) ∧
    (∀ t x, dist ((Fn t).bs x) (F₀.bs x) < δ x) ∧
    (∀ t x, dist ((Fn t).bs x) (F₀.bs x) < L.ε x) ∧
    (∀ x ∈ ⋃ i ≤ L.index n, (L.φ i) '' metric.closed_ball 0 1,
      (Fn 1).is_holonomic_at x),
  let Q : ℕ → htpy_formal_sol R → htpy_formal_sol R → Prop := λ n Fn Fnp1,
    (L.index (n + 1)  = L.index n → Fnp1 = Fn) ∧
     ∀ t, ∀ x ∉ range (L.φ $ L.index $ n+1), Fnp1 t x = Fn t x,
  suffices : ∃ F : ℕ → htpy_formal_sol R, ∀ n, P n (F n) ∧ Q n (F n) (F $ n+1),
  sorry { rcases this with ⟨F, hF⟩,
    use F,
    intro n,
    cases hF n,
    tauto },
  apply exists_by_induction' P Q,
  { dsimp only [P],
    have Union_eq : ∀ s : L.ι → set M, (⋃ i ≤ L.index 0, s i) = s 0,
    {
      sorry },
    let 𝓕₀ := L.loc_formal_sol (L.rg_subset_rg 0),
    have : ∀ᶠ (x : EM) near (L.landscape hA 0).C, 𝓕₀.is_holonomic_at x,
    {
      sorry },
    let Id := open_smooth_embedding.id 𝓘(ℝ, ℝ) ℝ,
    have foo := (Id.prod (L.φ 0)).smooth_update (L.ψj 0) (λ p : ℝ × M, F₀.bs p.2),
    let τ : ℝ × M → ℝ := λ p, min (δ p.2) (L.ε p.2),
    have τ_pos : ∀ p, 0 < τ p, sorry,
    have τ_cont : continuous τ, sorry,
    have cpct : is_compact ((Icc 0 1 : set ℝ) ×ˢ (metric.closed_ball 0 2 : set EM)), sorry,
    have smth : smooth (𝓘(ℝ, ℝ).prod IM) IX (λ (p : ℝ × M), F₀.to_one_jet_sec.bs p.snd), sorry,
    have sub : (λ (p : ℝ × M), F₀.bs p.2) '' range (Id.prod (L.φ 0)) ⊆ range (L.ψj 0), sorry,
    rcases (Id.prod (L.φ 0)).dist_update (L.ψj 0) (λ p : ℝ × M, F₀.bs p.2)
      cpct smth sub τ_pos τ_cont with ⟨η, η_pos, hη⟩,

    rcases rel_loc.formal_sol.improve_htpy (L.is_open_loc_rel 0 hRopen) (L.is_ample 0 hRample)
      (L.landscape hA 0) η_pos 𝓕₀ this with ⟨𝓗, h𝓗₀, h𝓗C, h𝓗K₁, h𝓗δ, h𝓗K₀⟩,
    let H := L.unloc_htpy_formal_sol 0 𝓗,
    refine ⟨H, _, _, _, _, _⟩,
    sorry { apply L.unloc_loc,
      rw h𝓗₀ },
    sorry { apply L.foobar _ _ h𝓗C,
      apply subset_union_left ((L.φ 0) ⁻¹' A) },
    { suffices : ∀ p : ℝ × M, dist ((H p.1).bs p.2) (F₀.bs p.2) < min (δ p.2) (L.ε p.2),
      sorry { exact λ t x, (this (t, x)).trans_le (min_le_left _ _) },
      rintros ⟨t, x⟩,
      convert hη _ _ _ (t, x),
      dsimp,
      all_goals { sorry } },
    {
      sorry },
    sorry { apply L.barbaz' (L.rg_subset_rg 0) _ h𝓗K₀,
      dsimp [localisation_data.landscape],
      rw [Union_eq, preimage_image_eq],
      exact (L.φ 0).injective } },
  sorry { rintros n F ⟨hF₀, hfA, hFδ, hFhol⟩,
    sorry },
end

/-- The non-parametric version of Gromov's theorem -/
lemma rel_mfld.ample.satisfies_h_principle (hRample : R.ample) (hRopen : is_open R)
  (hA : is_closed A)
  (hδ_pos : ∀ x, 0 < δ x) (hδ_cont : continuous δ) :
  R.satisfies_h_principle A δ :=
begin
  apply rel_mfld.satisfies_h_principle_of_weak hA,
  unfreezingI { clear_dependent A },
  intros A hA 𝓕₀ h𝓕₀,
  have cont : continuous 𝓕₀.bs, from 𝓕₀.smooth_bs.continuous,
  let L : localisation_data IM IX 𝓕₀.bs := std_localisation_data EM IM EX IX cont,
  let π := L.index,

  suffices : ∃ F : ℕ → htpy_formal_sol R, ∀ n,
    ((F n 0 = 𝓕₀) ∧
    (∀ t, ∀ᶠ x near A, F n t x = 𝓕₀ x) ∧
    (∀ t x, dist ((F n t).bs x) (𝓕₀.bs x) < δ x) ∧

    (∀ x ∈ ⋃ i ≤ π n, L.φ i '' metric.closed_ball (0 : EM) 1,
             (F n 1).is_holonomic_at x)) ∧
    ((π (n+1) = π n → F (n+1) = F n) ∧
     (∀ t, ∀ x ∉ range (L.φ $ π (n+1)), F (n+1) t x = F n t x)),
  { clear_dependent hRample hRopen,
    simp_rw [and_assoc, forall_and_distrib] at this,
    rcases this with ⟨F, hF₀, hfA, hFδ, hFhol, hFπ, hFultim⟩,
    let FF := λ n : ℕ, λ p : ℝ × M, F n p.1 p.2,
    have h : ∀ n : ℕ, ∀ x ∉ (univ : set ℝ) ×ˢ range (L.φ $ π $ n+1), FF (n+1) x = FF n x,
    { rintros n ⟨t, x⟩ H,
      exact hFultim _ _ _ (λ hx, H ⟨trivial, hx⟩) },
    have h' : ∀ (n : ℕ), π (n + 1) = π n → FF (n + 1) = FF n,
    { intros n hn,
      ext1 ⟨t, x⟩,
      dsimp [FF],
      rw hFπ n hn },
    have loc_fin : locally_finite (λ i, (univ ×ˢ range (L.φ i) : set $ ℝ × M)),
    { rintros ⟨t, x⟩,
      rcases L.lf_φ x with ⟨s, s_in, hs⟩,
      refine ⟨univ ×ˢ s, _, _⟩,
      { rw nhds_prod_eq,
        exact filter.prod_mem_prod filter.univ_mem s_in },
      { convert hs,
        ext i,
        simp [univ_prod_inter_univ_prod] } },
    have : ∀ x : ℝ × M, ∀ᶠ n in at_top, x.2 ∈ ⋃ i ≤ π n, (L.φ i) '' metric.ball 0 1,
    { rintros ⟨t, x⟩,
      rw [eventually_at_top],
      rcases (mem_top.mpr L.h₁ x) with ⟨-, ⟨i, rfl⟩, hi : x ∈ (L.φ i) '' metric.ball 0 1⟩,
      refine ⟨indexing.to_nat i, λ n hn, _⟩,
      have : i ≤ π n,
      { rw ← indexing.from_to i,
        exact indexing.mono_from hn },
      exact mem_bUnion this hi },
    cases loc_fin.exists_forall_eventually_of_indexing h h' with G hG, clear h h' loc_fin,
    choose n hn' hn using λ x, eventually_at_top.mp ((this x).and (hG x)), clear hG this,
    have G_eq : ∀ t x, G (t, x) = F (n (t, x)) t x,
    { exact λ t x, ((hn (t, x) _ le_rfl).eq_of_nhds).symm },
    have hG11 : ∀ t x, (G (t, x)).1.1 = x,
    { intros t x,
      rw G_eq,
      refl },
    let 𝓕 : htpy_formal_sol R := {
      bs := λ t x, (G (t, x)).1.2,
      ϕ := λ t x, (G (t, x)).2,
      smooth' := begin
        intro x,
        apply ((F (n x)).smooth' x).congr_of_eventually_eq,
        apply (hn x _ le_rfl).mono,
        intros p hp,
        dsimp only,
        rw [show (p.1, p.2) = p, from prod.ext rfl rfl, ← hp],
        refl
      end,
      is_sol' := begin
        intros t x,
        change one_jet_bundle.mk x (G (t, x)).1.2 (G (t, x)).2 ∈ R,
        rw ← (hn (t, x) _ le_rfl).eq_of_nhds,
        exact (F (n (t, x))).is_sol' t x,
      end },
    refine ⟨𝓕, _, _, _, _⟩,
    { clear_dependent δ hfA hFhol hFπ hFultim,
      intro x,
      ext,
      { refl },
      { change (G (0, x)).1.2 = _,
        rw [G_eq, hF₀] },
      { apply heq_of_eq,
        change (G (0, x)).2 = _,
        rw [G_eq, hF₀] } },
    { clear_dependent δ hF₀ hfA hFπ hFultim,
      intro x,
      have : x ∈ ⋃ i ≤ π (n (1, x)), (L.φ i) '' metric.closed_ball 0 1,
      { have : x ∈ _ := hn' (1, x) _ le_rfl,
        apply set.bUnion_mono subset_rfl _ this,
        rintros i -,
        exact image_subset _ metric.ball_subset_closed_ball, },
      apply (hFhol (n (1, x)) x this).congr, clear this,
      have : F (n (1, x)) 1 =ᶠ[𝓝 x] (λ x, G (1, x)),
      { exact (hn (1, x) (n(1, x)) le_rfl).slice },
      apply this.mono, clear this,
      rintros y (hy : F (n (1, x)) 1 y = G (1, y)),
      change F (n (1, x)) 1 y = 𝓕 1 y,
      rw hy,
      change G (1, y) = 𝓕 1 y,
      ext ; try { refl },
      rw hG11,
      refl },
    { clear_dependent δ hF₀ hFhol hFπ hFultim,
      intros x x_in t,
      rw [← (hfA (n (t, x)) t).nhds_set_forall_mem x x_in, ← G_eq],
      ext ; try { refl },
      rw hG11, refl, },
    { clear_dependent hF₀ hFhol hFπ hFultim hfA,
      intros t x,
      apply le_of_lt,
      change dist (G (t, x)).1.2 (𝓕₀.bs x) < δ x,
      rw ← (hn (t, x) _ le_rfl).eq_of_nhds,
      exact hFδ (n (t, x)) t x } },
  exact hRample.satisfies_h_principle_core hRopen hA hδ_pos hδ_cont 𝓕₀ h𝓕₀ L,
end

variables
{EP : Type*} [normed_add_comm_group EP] [normed_space ℝ EP]  [finite_dimensional ℝ EP]
{HP : Type*} [topological_space HP] {IP : model_with_corners ℝ EP HP} [model_with_corners.boundaryless IP]
{P : Type*} [topological_space P] [charted_space HP P] [smooth_manifold_with_corners IP P]
[locally_compact_space P] -- investigate how to deduce this from finite-dimensional
[sigma_compact_space P]
[t2_space P]
[nonempty P] -- investigate how to remove this
{C : set (P × M)}

/-- **Gromov's Theorem** -/
theorem rel_mfld.ample.satisfies_h_principle_with (hRample : R.ample) (hRopen : is_open R)
  (hC : is_closed C)
  (hδ_pos : ∀ x, 0 < δ x) (hδ_cont : continuous δ) :
  R.satisfies_h_principle_with IP C δ :=
begin
  have hδ_pos' : ∀ (x : P × M), 0 < δ x.2 := λ (x : P × M), hδ_pos x.snd,
  have hδ_cont' : continuous (λ (x : P × M), δ x.2) := hδ_cont.comp continuous_snd,
  have is_op : is_open (rel_mfld.relativize IP P R) := R.is_open_relativize hRopen,
  apply rel_mfld.satisfies_h_principle.satisfies_h_principle_with,
  exact (hRample.relativize IP P).satisfies_h_principle is_op hC hδ_pos' hδ_cont',
end

variables
{E' : Type*} [normed_add_comm_group E'] [normed_space ℝ E'] [finite_dimensional ℝ E']
{H' : Type*} [topological_space H'] {I' : model_with_corners ℝ E' H'} [model_with_corners.boundaryless I']
{M' : Type*} [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M']
[locally_compact_space M'] -- investigate how to deduce this from finite-dimensional
[sigma_compact_space M']
[t2_space M']
[nonempty M'] -- investigate how to remove this

include IP

/-- Gromov's Theorem without metric space assumption -/
theorem rel_mfld.ample.satisfies_h_principle_with' {R : rel_mfld IM M I' M'}
  (hRample : R.ample) (hRopen : is_open R) (hC : is_closed C)
  (hδ_pos : ∀ x, 0 < δ x) (hδ_cont : continuous δ) :
  by letI := (@topological_space.metrizable_space_metric _ _
    (manifold_with_corners.metrizable_space I' M')); exact
  R.satisfies_h_principle_with IP C δ :=
begin
  haveI := (@topological_space.metrizable_space_metric _ _
    (manifold_with_corners.metrizable_space I' M')),
  apply rel_mfld.ample.satisfies_h_principle_with; assumption
end
