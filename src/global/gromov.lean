import to_mathlib.data.set.prod
import to_mathlib.data.nat.basic
import to_mathlib.geometry.manifold.metrizable
import to_mathlib.topology.constructions
import to_mathlib.logic.basic

import inductive_constructions

import global.parametricity_for_free
import global.localized_construction
import global.localisation_data
/-!
# Gromov's theorem

We prove the h-principle for open and ample first order differential relations.
-/

noncomputable theory

open set filter model_with_corners metric
open_locale topology manifold

variables
{EM : Type*} [normed_add_comm_group EM] [normed_space ℝ EM] [finite_dimensional ℝ EM]
{HM : Type*} [topological_space HM] {IM : model_with_corners ℝ EM HM} [boundaryless IM]
{M : Type*} [topological_space M] [charted_space HM M] [smooth_manifold_with_corners IM M]
[t2_space M] [sigma_compact_space M]

{EX : Type*} [normed_add_comm_group EX] [normed_space ℝ EX] [finite_dimensional ℝ EX]
{HX : Type*} [topological_space HX] {IX : model_with_corners ℝ EX HX} [model_with_corners.boundaryless IX]
-- note: X is a metric space
{X : Type*} [metric_space X] [charted_space HX X] [smooth_manifold_with_corners IX X]
[sigma_compact_space X]

{R : rel_mfld IM M IX X}
{A : set M} {δ : M → ℝ}

set_option trace.filter_inst_type true
local notation `J¹` := one_jet_bundle IM M IX X

lemma rel_mfld.ample.satisfies_h_principle (hRample : R.ample) (hRopen : is_open R)
  (hA : is_closed A)
  (hδ_pos : ∀ x, 0 < δ x) (hδ_cont : continuous δ) :
  R.satisfies_h_principle A δ :=
begin
  borelize EX,
  haveI := locally_compact_manifold IM M,
  haveI := locally_compact_manifold IX X,
  refine rel_mfld.satisfies_h_principle_of_weak hA _,
  unfreezingI { clear_dependent A },
  intros A hA 𝓕₀ h𝓕₀,

  casesI is_empty_or_nonempty M with hM hM,
  { refine  ⟨empty_htpy_formal_sol R, _, _, _, _⟩,
    all_goals { try { apply eventually_of_forall _ } },
    all_goals { try { intro } },
    all_goals { try { intro } },
    all_goals { apply empty_htpy_formal_sol_eq <|> apply (is_empty.false ‹M›).elim } },
  casesI is_empty_or_nonempty X with hX hX,
  { exfalso,
    inhabit M,
    exact (is_empty.false $ 𝓕₀.bs default).elim },
  /- We now start the main proof under the assumption that `M` and `X` are nonempty. -/
  have cont : continuous 𝓕₀.bs, from 𝓕₀.smooth_bs.continuous,
  let L : localisation_data IM IX 𝓕₀.bs := std_localisation_data EM IM EX IX cont,
  let K : index_type L.N → set M := λ i, (L.φ i) '' (closed_ball (0:EM) 1),
  let U : index_type L.N → set M := λ i, range (L.φ i),
  have K_cover : (⋃ i, K i) = univ,
    from eq_univ_of_subset (Union_mono (λ i, image_subset _ ball_subset_closed_ball)) L.h₁,
  let τ := λ x : M, min (δ x) (L.ε x),
  have τ_pos : ∀ x, 0 < τ x, from λ x, lt_min (hδ_pos x) (L.ε_pos x),
  have τ_cont : continuous τ, from hδ_cont.min L.ε_cont,
  have := (λ (x : M) (F' : germ (𝓝 x) J¹), F'.value = 𝓕₀ x),
  let P₀ : Π x : M, germ (𝓝 x) J¹ → Prop := λ x F,
    F.value.1.1 = x ∧
    F.value ∈ R ∧
    F.cont_mdiff_at' IM ((IM.prod IX).prod 𝓘(ℝ, EM →L[ℝ] EX)) ∞ ∧
    restrict_germ_predicate (λ x F', F'.value = 𝓕₀ x) A x F ∧
    dist (F.value.1.2) (𝓕₀.bs x) < τ x,

  let P₁ : Π x : M, germ (𝓝 x) J¹ → Prop := λ x F, is_holonomic_germ F,
  let P₂ : Π p : ℝ × M, germ (𝓝 p) J¹ → Prop := λ p F,
    F.cont_mdiff_at' (𝓘(ℝ).prod IM) ((IM.prod IX).prod 𝓘(ℝ, EM →L[ℝ] EX)) ∞,
  have hP₂ : ∀ (a b : ℝ) (p : ℝ × M) (f : ℝ × M → one_jet_bundle IM M IX X),
    P₂ (a*p.1+b, p.2) f → P₂ p (λ p : ℝ × M, f (a*p.1+b, p.2)),
  { rintros a b ⟨t, x⟩ f h,
    change cont_mdiff_at _ _ _ (f ∘ λ (p : ℝ × M), (a * p.1 + b, p.2)) (t, x),
    change cont_mdiff_at _ _ _ f ((λ (p : ℝ × M), (a * p.1 + b, p.2)) (t, x)) at h,
    have : cont_mdiff_at (𝓘(ℝ, ℝ).prod IM) (𝓘(ℝ, ℝ).prod IM) ∞ (λ (p : ℝ × M), (a * p.1 + b, p.2)) (t, x),
    { have h₁ : cont_mdiff_at 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (λ t, a * t + b) t,
      from cont_mdiff_at_iff_cont_diff_at.mpr
        (((cont_diff_at_id : cont_diff_at ℝ ∞ id t).const_smul a).add cont_diff_at_const),
      exact h₁.prod_map cont_mdiff_at_id },
    exact h.comp (t, x) this },
  have init : ∀ x : M, P₀ x (𝓕₀ : M → J¹),
  { refine λ x, ⟨rfl, 𝓕₀.is_sol x, 𝓕₀.smooth x, _, _⟩,
    { revert x,
      exact forall_restrict_germ_predicate_of_forall (λ x, rfl) },
    { erw dist_self,
      exact τ_pos x } },
  have ind : ∀ (i : index_type L.N) (f : M → J¹), (∀ x, P₀ x f) → (∀ᶠ x near ⋃ j < i, K j, P₁ x f) →
    ∃ F : ℝ → M → J¹, (∀ t, ∀ x, P₀ x $ F t) ∧ (∀ᶠ x near ⋃ j ≤ i, K j, P₁ x $ F 1) ∧
                     (∀ p, P₂ p ↿F) ∧ (∀ t, ∀ x ∉ U i, F t x = f x) ∧
                     (∀ᶠ t near Iic 0, F t = f) ∧ (∀ᶠ t near Ici 1, F t = F 1),
  { intros i f hf₀ hf₁,
    let K₀ : set EM := closed_ball 0 1,
    have hK₀ : is_compact K₀, from is_compact_closed_ball 0 1,
    let K₁ : set EM := closed_ball 0 2,
    have hK₁ : is_compact K₁, from is_compact_closed_ball 0 2,
    have hK₀K₁ : K₀ ⊆ interior K₁,
    { dsimp [K₀, K₁],
      rw interior_closed_ball (0 : EM) (by norm_num : (2 : ℝ) ≠ 0),
      exact closed_ball_subset_ball (by norm_num) },
    let C := ⋃ j < i, (L.φ j) '' closed_ball 0 1,
    have hC : is_closed C,
    { -- TODO: rewrite localization_data.is_closed_Union to match this.
      exact is_closed_bUnion (finite_Iio _) (λ j hj, (hK₀.image $ (L.φ j).continuous).is_closed) },
    simp only [P₀, forall_and_distrib] at hf₀,
    rcases hf₀ with ⟨hf_sec, hf_sol, hf_smooth, hf_A, hf_dist⟩,
    rw forall_restrict_germ_predicate_iff at hf_A,
    let F : formal_sol R := mk_formal_sol f hf_sec hf_sol hf_smooth,
    have hFAC : ∀ᶠ x near A ∪ C, F.is_holonomic_at x,
    { rw eventually_nhds_set_union,
      refine ⟨_, hf₁⟩,
      apply (hf_A.and h𝓕₀).eventually_nhds_set.mono (λ x hx, _),
      rw eventually_and at hx,
      apply hx.2.self_of_nhds.congr,
      apply hx.1.mono (λ x' hx', _),
      simp [F],
      exact hx'.symm },
    have hFφψ : F.bs '' (range $ L.φ i) ⊆ range (L.ψj i),
    { rw ← range_comp,
      apply L.ε_spec,
      intro x,
      calc dist (F.bs x) (𝓕₀.bs x) = dist (f x).1.2 (𝓕₀.bs x) : by simp only [F, mk_formal_sol_bs_apply]
      ... < τ x : hf_dist x
      ... ≤ L.ε x : min_le_right _ _ },
    let η : M → ℝ := λ x, τ x - dist (f x).1.2 (𝓕₀.bs x),
    have η_pos : ∀ x, 0 < η x,
    { exact λ x, sub_pos.mpr (hf_dist x) },
    have η_cont : continuous η,
    { have : cont_mdiff IM ((IM.prod IX).prod 𝓘(ℝ, EM →L[ℝ] EX)) ∞ f, from λ x, hf_smooth x,
      apply τ_cont.sub,
      exact (one_jet_bundle_proj_continuous.comp this.continuous).snd.dist
        𝓕₀.smooth_bs.continuous },
    rcases (L.φ i).improve_formal_sol (L.ψj i) hRample hRopen (hA.union hC) η_pos η_cont hFφψ hFAC
      hK₀ hK₁ hK₀K₁ with ⟨F', hF'₀, hF'₁, hF'AC, hF'K₁, hF'η, hF'hol⟩,
    refine ⟨λ t x, F' t x, _, _, _, _, _, _⟩,
    { refine λ t x, ⟨rfl, F'.is_sol, (F' t).smooth x, _, _⟩,
      { revert x,
        rw forall_restrict_germ_predicate_iff,
        rw [eventually_nhds_set_union] at hF'AC,
        apply (hF'AC.1.and hf_A).mono,
        rintros x ⟨hx, hx'⟩,
        change F' t x = _,
        rw [hx t, ← hx', mk_formal_sol_apply],
        refl },
      { calc dist (F' t x).1.2 (𝓕₀.bs x) ≤ dist (F' t x).1.2 (F.bs x) + dist (F.bs x) (𝓕₀.bs x) : dist_triangle _ _ _
        ... < η x + dist (F.bs x) (𝓕₀.bs x) : add_lt_add_right (hF'η t x) _
        ... = τ x : by simp [η] } },
    { rw [union_assoc, eventually_nhds_set_union] at hF'hol,
      replace hF'hol := hF'hol.2,
      simp_rw [← L.Union_succ'] at hF'hol,
      exact hF'hol },
    { exact F'.smooth },
    { intros t x hx,
      rw hF'K₁ t x ((mem_range_of_mem_image _ _).mt hx),
      simp [F] },
    { apply hF'₀.mono (λ x hx, _),
      erw hx,
      ext1 y,
      simp [F] },
    { apply hF'₁.mono (λ x hx, _),
      rw hx } },
  rcases inductive_htpy_construction P₀ P₁ P₂ hP₂ L.lf_φ K_cover init
    (𝓕₀.smooth.comp cont_mdiff_snd) ind with ⟨F, hF₀, hFP₀, hFP₁, hFP₂⟩,
  simp only [P₀, forall₂_and_distrib] at hFP₀,
  rcases hFP₀ with ⟨hF_sec, hF_sol, hF_smooth, hF_A, hF_dist⟩,
  refine ⟨mk_htpy_formal_sol F hF_sec hF_sol hFP₂, _, _, _, _⟩,
  { intros x,
    rw [mk_htpy_formal_sol_apply, hF₀] },
  { exact hFP₁ },
  { intros x hx t,
    rw mk_htpy_formal_sol_apply,
    exact (forall_restrict_germ_predicate_iff.mp $ hF_A t).on_set x hx },
  { intros t x,
    change dist (mk_htpy_formal_sol F hF_sec hF_sol hFP₂ t x).1.2 (𝓕₀.bs x) ≤ δ x,
    rw mk_htpy_formal_sol_apply,
    exact (hF_dist t x).le.trans (min_le_left _ _) }
end


variables
{EP : Type*} [normed_add_comm_group EP] [normed_space ℝ EP]  [finite_dimensional ℝ EP]
{HP : Type*} [topological_space HP] {IP : model_with_corners ℝ EP HP} [boundaryless IP]
{P : Type*} [topological_space P] [charted_space HP P] [smooth_manifold_with_corners IP P]
[sigma_compact_space P]
[t2_space P]
{C : set (P × M)}

/-
We now deduce the parametric case from the unparametric one using
`rel_mfld.satisfies_h_principle.satisfies_h_principle_with` which reduces the parametric
`h`-principle to the non-parametric one for a different relation and `rel_mafld.ample.relativize`
which ensures the ampleness assumption survives this reduction.
-/

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
[sigma_compact_space M'] [t2_space M']

include IP

/-
Since every (sigma-compact) manifold is metrizable, the metric space assumption can be removed.
-/

/-- Gromov's Theorem without metric space assumption -/
theorem rel_mfld.ample.satisfies_h_principle_with' {R : rel_mfld IM M I' M'}
  (hRample : R.ample) (hRopen : is_open R) (hC : is_closed C)
  (hδ_pos : ∀ x, 0 < δ x) (hδ_cont : continuous δ) :
  by letI := manifold_metric I' M' ; exact
  R.satisfies_h_principle_with IP C δ :=
by apply rel_mfld.ample.satisfies_h_principle_with; assumption
