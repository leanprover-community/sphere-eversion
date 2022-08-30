import global.relation
import global.localisation_data

/-!
# Gromov's theorem

We prove the h-principle for open and ample first order differential relations.
-/

noncomputable theory

open set
open_locale topological_space manifold

variables
{E : Type*} [normed_add_comm_group E] [normed_space ℝ E] [finite_dimensional ℝ E]
{H : Type*} [topological_space H] {I : model_with_corners ℝ E H} [model_with_corners.boundaryless I]
{M : Type*} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
[t2_space M]
[locally_compact_space M] -- investigate how to deduce this from finite-dimensional
[nonempty M] -- investigate how to remove this
[sigma_compact_space M]

{EX : Type*} [normed_add_comm_group EX] [normed_space ℝ EX]  [finite_dimensional ℝ EX]
{HX : Type*} [topological_space HX] {IX : model_with_corners ℝ EX HX} [model_with_corners.boundaryless IX]
-- note: X is a metric space
{X : Type*} [metric_space X] [charted_space HX X] [smooth_manifold_with_corners IX X]
[locally_compact_space X] -- investigate how to deduce this from finite-dimensional
[sigma_compact_space X]
[nonempty X] -- investigate how to remove this

{R : rel_mfld I M IX X}
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

/- The next two instances are evil but temporary
We need to sort out whether we can drop `encodable` from localisation_data.lean
-/
instance bar (ι : Type*) [encodable ι] : linear_order ι := sorry
instance baz (ι : Type*) [encodable ι] : indexing ι := sorry


/-- The non-parametric version of Gromov's theorem -/
lemma rel_mfld.ample.satisfies_h_principle (h1 : R.ample) (h2 : is_open R)
  (hC₂ : is_closed A)
  (hε_pos : ∀ x, 0 < ε x) (hε_cont : continuous ε) :
  R.satisfies_h_principle A ε :=
begin
  intros 𝓕₀ h𝓕₀,
  have cont : continuous 𝓕₀.bs,
  {
    sorry },
  let L : localisation_data I IX 𝓕₀.bs := std_localisation_data E I EX IX cont,
  letI := L.hι,
  let π : ℕ → L.ι := indexing.from_nat,
  rcases localisation_stability E I EX IX cont L with ⟨ε, ε_pos, ε_cont, hε⟩,
  suffices : ∃ F : ℕ → htpy_formal_sol R,
    (∀ t, F 0 t = 𝓕₀) ∧
    (∀ n t, ∀ᶠ x near A, F n t x = 𝓕₀ x) ∧
    (∀ n t x, dist ((F n t).bs x) (𝓕₀.bs x) < ε x) ∧
    (∀ n, π (n+1) = π n → F (n+2) = F (n + 1)) ∧
    (∀ n, ∀ x ∈ ⋃ i < π n, L.φ i '' metric.closed_ball (0 : E) 1,
             (F (n+1) 1).to_one_jet_sec.is_holonomic_at x) ∧
    (∀ n t, ∀ x ∉ range (L.φ $ π n), F (n+1) t x = F n t x),
  { rcases this with ⟨F, hF₀, hfA, hFε, hFπ, hFhol, hFultim⟩,
    let FF := λ n : ℕ, λ p : ℝ × M, F n p.1 p.2,
    have h : ∀ n : ℕ, ∀ x ∉ (univ : set ℝ) ×ˢ range (L.φ $ π n), FF (n+1) x = FF n x,
    sorry { rintros n ⟨t, x⟩ H,
      exact hFultim _ _ _ (λ hx, H ⟨trivial, hx⟩) },
    have h' : ∀ (n : ℕ), π (n + 1) = π n → FF (n + 2) = FF (n + 1),
    sorry { intros n hn,
      ext1 ⟨t, x⟩,
      dsimp [FF],
      rw hFπ n hn },
    have loc_fin : locally_finite (λ i : L.ι, (univ ×ˢ range (L.φ i) : set $ ℝ × M)),
    sorry { rintros ⟨t, x⟩,
      rcases L.lf_φ x with ⟨s, s_in, hs⟩,
      refine ⟨univ ×ˢ s, _, _⟩,
      { rw nhds_prod_eq,
        exact filter.prod_mem_prod filter.univ_mem s_in },
      { convert hs,
        ext i,
        simp [univ_prod_inter_univ_prod] } },
    cases loc_fin.exists_forall_eventually_of_indexing h h' with G hG,
    choose n hn using λ x, (hG x).exists,
    let 𝓕 : htpy_formal_sol R := {
      bs := λ t x, (G (t, x)).1.2,
      ϕ := λ t x, (G (t, x)).2,
      smooth' := sorry /- begin
        intro x,
        apply ((F (n x)).smooth' x).congr_of_eventually_eq,
        /- The following goal will probably come back
        (λ (p : ℝ × M), one_jet_bundle.mk p.2 (G (p.1, p.2)).1.2 (G (p.1, p.2)).2)
          =ᶠ[𝓝 x]
         λ (p : ℝ × M), one_jet_bundle.mk p.2 ((F (n x)).bs p.1 p.2) ((F (n x)).ϕ p.1 p.2)
        -/
        apply (hn x).mono,
        intros p hp,
        dsimp only,
        rw [show (p.1, p.2) = p, from prod.ext rfl rfl, ← hp],
        refl
      end -/,
      is_sol' := /- begin
        intros t x,
        change one_jet_bundle.mk x (G (t, x)).1.2 (G (t, x)).2 ∈ R,
        rw ← (hn (t, x)).eq_of_nhds,
        exact (F (n (t, x))).is_sol' t x,
      end -/sorry },
    refine ⟨𝓕, _, _, _, _⟩,
    {
      sorry },
    {
      sorry },
    {
      sorry },
    {
      sorry }, },
  sorry
end

variables
{EP : Type*} [normed_add_comm_group EP] [normed_space ℝ EP]  [finite_dimensional ℝ EP]
{HP : Type*} [topological_space HP] {IP : model_with_corners ℝ EP HP} [model_with_corners.boundaryless IP]
{P : Type*} [topological_space P] [charted_space HP P] [smooth_manifold_with_corners IP P]
[locally_compact_space P] -- investigate how to deduce this from finite-dimensional
[sigma_compact_space P]
[t2_space P]
[nonempty P] -- investigate how to remove this
{C₁ : set P} {C₂ : set M}

/-- **Gromov's Theorem** -/
theorem rel_mfld.ample.satisfies_h_principle_with (h1 : R.ample) (h2 : is_open R)
  (hC₁ : is_closed C₁) (hC₂ : is_closed C₂)
  (hε_pos : ∀ x, 0 < ε x) (hε_cont : continuous ε) :
  R.satisfies_h_principle_with IP C₁ C₂ ε :=
begin
  have hε_pos' : ∀ (x : P × M), 0 < ε x.2 := λ (x : P × M), hε_pos x.snd,
  have hε_cont' : continuous (λ (x : P × M), ε x.2) := hε_cont.comp continuous_snd,
  have is_op : is_open (rel_mfld.relativize IP P R) := R.is_open_relativize IP P h2,
  apply rel_mfld.satisfies_h_principle.satisfies_h_principle_with,
  exact (h1.relativize IP P).satisfies_h_principle is_op (hC₁.prod hC₂) hε_pos' hε_cont',
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
theorem rel_mfld.ample.satisfies_h_principle_with' {R : rel_mfld I M I' M'}
  (h1 : R.ample) (h2 : is_open R) (hC₁ : is_closed C₁) (hC₂ : is_closed C₂)
  (hε_pos : ∀ x, 0 < ε x) (hε_cont : continuous ε) :
  by letI := (@topological_space.metrizable_space_metric _ _
    (manifold_with_corners.metrizable_space I' M')); exact
  R.satisfies_h_principle_with IP C₁ C₂ ε :=
begin
  haveI := (@topological_space.metrizable_space_metric _ _
    (manifold_with_corners.metrizable_space I' M')),
  apply rel_mfld.ample.satisfies_h_principle_with; assumption
end
