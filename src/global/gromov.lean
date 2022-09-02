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
  [measurable_space EX] [borel_space EX] -- FIXME: Assuming this is a bit silly, we should use letI
                                         -- at the beginning of the proof needing it
{HX : Type*} [topological_space HX] {IX : model_with_corners ℝ EX HX} [model_with_corners.boundaryless IX]
-- note: X is a metric space
{X : Type*} [metric_space X] [charted_space HX X] [smooth_manifold_with_corners IX X]
[locally_compact_space X] -- FIXME: investigate how to deduce this from finite-dimensional
[sigma_compact_space X]
[nonempty X] -- FIXME: investigate how to remove this

{R : rel_mfld IM M IX X}
{A : set M} {ε : M → ℝ}

lemma univ_prod_inter_univ_prod {α β : Type*} {s t : set β} :
  (univ : set α) ×ˢ s ∩ (univ : set α) ×ˢ t = (univ : set α) ×ˢ (s ∩ t) :=
begin
  ext ⟨a, b⟩,
  simp
end

@[simp] lemma univ_prod_nonempty_iff {α β : Type*} [nonempty α] {s : set β} :
  ((univ : set α) ×ˢ s).nonempty ↔ s.nonempty :=
begin
  inhabit α,
  split,
  { rintro ⟨⟨-, b⟩, ⟨-, h : b ∈ s⟩⟩,
    exact ⟨b, h⟩ },
  { rintro ⟨b, h⟩,
    exact ⟨⟨default, b⟩, ⟨trivial, h⟩⟩ }
end



-- The next lemma won't be used, it's a warming up exercise for the one below.
-- It could go to mathlib.
lemma exists_by_induction {α : Type*} {P : ℕ → α → Prop}
  (h₀ : ∃ a, P 0 a)
  (ih : ∀ n a, P n a → ∃ a', P (n+1) a') :
  ∃ f : ℕ → α, ∀ n, P n (f n) :=
begin
  choose f₀ hf₀ using h₀,
  choose! F hF using ih,
  exact ⟨λ n, nat.rec_on n f₀ F, λ n, nat.rec hf₀ (λ n ih, hF n _ ih) n⟩
end

-- We make `P` and `Q` explicit to help the elaborator when applying the lemma
-- (elab_as_eliminator isn't enough).
lemma exists_by_induction' {α : Type*} (P : ℕ → α → Prop) (Q : ℕ → α → α → Prop)
  (h₀ : ∃ a, P 0 a)
  (ih : ∀ n a, P n a → ∃ a', P (n+1) a' ∧ Q n a a') :
  ∃ f : ℕ → α, ∀ n, P n (f n) ∧ Q n (f n) (f $ n+1) :=
begin
  choose f₀ hf₀ using h₀,
  choose! F hF hF' using ih,
  have key : ∀ n, P n (nat.rec_on n f₀ F), from λ n, nat.rec hf₀ (λ n ih, hF n _ ih) n,
  exact ⟨λ n, nat.rec_on n f₀ F, λ n, ⟨key n, hF' n _ (key n)⟩⟩
end

set_option trace.filter_inst_type true

lemma rel_mfld.ample.satisfies_h_principle_core
  (hRample : R.ample) (hRopen : is_open R)
  (hA : is_closed A)
  (hε_pos : ∀ (x : M), 0 < ε x)
  (hε_cont : continuous ε)
  (𝓕₀ : formal_sol R)
  (h𝓕₀ : ∀ᶠ x near A, 𝓕₀.to_one_jet_sec.is_holonomic_at x)
  (L : localisation_data IM IX 𝓕₀.to_one_jet_sec.bs) :
  ∃ F : ℕ → htpy_formal_sol R, ∀ n : ℕ,
    ((F n 0 = 𝓕₀) ∧
    (∀ t, ∀ᶠ x near A, F n t x = 𝓕₀ x) ∧
    (∀ t x, dist ((F n t).bs x) (𝓕₀.bs x) <ε x) ∧

    (∀ x ∈ ⋃ i ≤ L.index n, (L.φ i) '' metric.closed_ball 0 1,
      ((F n) 1).to_one_jet_sec.is_holonomic_at x)) ∧
    ((L.index (n + 1)  = L.index n → F (n + 1) = F n) ∧
     ∀ t (x ∉ range (L.φ $ L.index $ n+1)), F (n + 1) t x = F n t x) :=
begin
  have cont_bs : continuous 𝓕₀.bs, from 𝓕₀.to_one_jet_sec.smooth_bs.continuous,
  rcases localisation_stability EM IM EX IX cont_bs L with ⟨η, η_pos, η_cont, hη⟩,
  let P : ℕ → htpy_formal_sol R → Prop := λ n Fn,
    (Fn 0 = 𝓕₀) ∧
    (∀ t, ∀ᶠ x near A, Fn t x = 𝓕₀ x) ∧
    (∀ t x, dist ((Fn t).bs x) (𝓕₀.bs x) <ε x) ∧

    (∀ x ∈ ⋃ i ≤ L.index n, (L.φ i) '' metric.closed_ball 0 1,
      (Fn 1).is_holonomic_at x),
  let Q : ℕ → htpy_formal_sol R → htpy_formal_sol R → Prop := λ n Fn Fnp1,
    (L.index (n + 1)  = L.index n → Fnp1 = Fn) ∧
     ∀ t, ∀ x ∉ range (L.φ $ L.index $ n+1), Fnp1 t x = Fn t x,
  apply exists_by_induction' P Q,
  { dsimp only [P],
    let 𝓕 := L.loc_formal_sol (L.rg_subset_rg 0),
    have : ∀ᶠ (x : EM) near (L.landscape hA 0).C, 𝓕.is_holonomic_at x,
    {
      sorry },
    let δ : ℝ := sorry,
    have δ_pos : δ > 0, sorry,
    rcases rel_loc.formal_sol.improve (L.is_open_loc_rel 0 hRopen) (L.is_ample 0 hRample) δ_pos this
      with ⟨H, hH0, hHC, hHK₁, hHδ, hHsol, hHK₀⟩,
    use L.unloc_htpy_formal_sol 0 hHsol,
    sorry },
  {
    sorry },
end

/-- The non-parametric version of Gromov's theorem -/
lemma rel_mfld.ample.satisfies_h_principle (hRample : R.ample) (hRopen : is_open R)
  (hA : is_closed A)
  (hε_pos : ∀ x, 0 < ε x) (hε_cont : continuous ε) :
  R.satisfies_h_principle A ε :=
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
    (∀ t x, dist ((F n t).bs x) (𝓕₀.bs x) < ε x) ∧

    (∀ x ∈ ⋃ i ≤ π n, L.φ i '' metric.closed_ball (0 : EM) 1,
             (F n 1).is_holonomic_at x)) ∧
    ((π (n+1) = π n → F (n+1) = F n) ∧
     (∀ t, ∀ x ∉ range (L.φ $ π (n+1)), F (n+1) t x = F n t x)),
  { clear_dependent hRample hRopen,
    simp_rw [and_assoc, forall_and_distrib] at this,
    rcases this with ⟨F, hF₀, hfA, hFε, hFhol, hFπ, hFultim⟩,
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
    { clear_dependent ε hfA hFhol hFπ hFultim,
      intro x,
      ext,
      { refl },
      { change (G (0, x)).1.2 = _,
        rw [G_eq, hF₀] },
      { apply heq_of_eq,
        change (G (0, x)).2 = _,
        rw [G_eq, hF₀] } },
    { clear_dependent ε hF₀ hfA hFπ hFultim,
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
    { clear_dependent ε hF₀ hFhol hFπ hFultim,
      intros x x_in t,
      rw [← (hfA (n (t, x)) t).nhds_set_forall_mem x x_in, ← G_eq],
      ext ; try { refl },
      rw hG11, refl, },
    { clear_dependent hF₀ hFhol hFπ hFultim hfA,
      intros t x,
      apply le_of_lt,
      change dist (G (t, x)).1.2 (𝓕₀.bs x) < ε x,
      rw ← (hn (t, x) _ le_rfl).eq_of_nhds,
      exact hFε (n (t, x)) t x } },
  exact hRample.satisfies_h_principle_core hRopen hA hε_pos hε_cont 𝓕₀ h𝓕₀ L,
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
  (hε_pos : ∀ x, 0 < ε x) (hε_cont : continuous ε) :
  R.satisfies_h_principle_with IP C ε :=
begin
  have hε_pos' : ∀ (x : P × M), 0 < ε x.2 := λ (x : P × M), hε_pos x.snd,
  have hε_cont' : continuous (λ (x : P × M), ε x.2) := hε_cont.comp continuous_snd,
  have is_op : is_open (rel_mfld.relativize IP P R) := R.is_open_relativize IP P hRopen,
  apply rel_mfld.satisfies_h_principle.satisfies_h_principle_with,
  exact (hRample.relativize IP P).satisfies_h_principle is_op hC hε_pos' hε_cont',
end

variables
{E' : Type*} [normed_add_comm_group E'] [normed_space ℝ E'] [finite_dimensional ℝ E']
  [measurable_space E'] [borel_space E']
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
  (hε_pos : ∀ x, 0 < ε x) (hε_cont : continuous ε) :
  by letI := (@topological_space.metrizable_space_metric _ _
    (manifold_with_corners.metrizable_space I' M')); exact
  R.satisfies_h_principle_with IP C ε :=
begin
  haveI := (@topological_space.metrizable_space_metric _ _
    (manifold_with_corners.metrizable_space I' M')),
  apply rel_mfld.ample.satisfies_h_principle_with; assumption
end
