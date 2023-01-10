
import to_mathlib.data.set.prod
import to_mathlib.data.set.lattice
import to_mathlib.data.nat.basic
import to_mathlib.topology.constructions
import to_mathlib.partition3

import global.localized_construction
import global.localisation_data
/-!
# Gromov's theorem

We prove the h-principle for open and ample first order differential relations.
-/

noncomputable theory

open set filter model_with_corners metric
open_locale topological_space manifold

/-- Given a predicate on germs `P : (Σ x : X, germ (𝓝 x) Y) → Prop` and `A : set X`,
build a new predicate on germs `restrict_germ_predicate P A` such that
`(∀ x, restrict_germ_predicate P A ⟨x, f⟩) ↔ ∀ᶠ x near A, P ⟨x, f⟩`, see
`forall_restrict_germ_predicate_iff` for this equivalence. -/
def restrict_germ_predicate {X Y : Type*} [topological_space X]
  (P : (Σ x : X, germ (𝓝 x) Y) → Prop) (A : set X) : (Σ x : X, germ (𝓝 x) Y) → Prop :=
λ ⟨x, φ⟩, quotient.lift_on' φ (λ f, x ∈ A → ∀ᶠ y in 𝓝 x, P ⟨y, f⟩) begin
  have : ∀ f f' : X → Y, f =ᶠ[𝓝 x] f' → (∀ᶠ y in 𝓝 x, P ⟨y, f⟩) → ∀ᶠ y in 𝓝 x, P ⟨y, f'⟩,
  { intros f f' hff' hf,
    apply (hf.and $ eventually.eventually_nhds hff').mono,
    rintros y ⟨hy, hy'⟩,
    rwa germ.coe_eq.mpr (eventually_eq.symm hy') },
  exact λ f f' hff', propext $ forall_congr $ λ _, ⟨this f f' hff', this f' f hff'.symm⟩,
end

lemma forall_restrict_germ_predicate_iff {X Y : Type*} [topological_space X]
  {P : (Σ x : X, germ (𝓝 x) Y) → Prop} {A : set X} {f : X → Y} :
  (∀ x, restrict_germ_predicate P A ⟨x, f⟩) ↔ ∀ᶠ x near A, P ⟨x, f⟩ :=
by { rw eventually_nhds_set_iff, exact iff.rfl }

-- Replace localisation_data.Union_succ with
lemma localisation_data.Union_succ' {𝕜 : Type*} [nontrivially_normed_field 𝕜] {E : Type*} [normed_add_comm_group E]
  [normed_space 𝕜 E] {H : Type*} [topological_space H] {I : model_with_corners 𝕜 E H}
  {M : Type*} [topological_space M] [charted_space H M]
  [smooth_manifold_with_corners I M] {E' : Type*} [normed_add_comm_group E']
  [normed_space 𝕜 E'] {H' : Type*} [topological_space H']
  {I' : model_with_corners 𝕜 E' H'} {M' : Type*} [topological_space M']
  [charted_space H' M'] [smooth_manifold_with_corners I' M'] {f : M → M'}
  (ld : localisation_data I I' f) {β : Type*} (s : ld.ι → set β) (i : index_type ld.N) :
  (⋃ j ≤ i, s j) = (⋃ j < i, s j) ∪ s i :=
begin
  simp only [(λ j, le_iff_lt_or_eq : ∀ j, j ≤ i ↔ j < i ∨ j = i)],
  erw [bUnion_union, bUnion_singleton],
  refl
end

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

def mk_htpy_formal_sol (F : ℝ × M → one_jet_bundle IM M IX X) (hsec : ∀ p, (F p).1.1 = p.2)
(hsol : ∀ p, F p ∈ R)
(hsmooth : smooth (𝓘(ℝ).prod IM) ((IM.prod IX).prod 𝓘(ℝ, EM →L[ℝ] EX)) ↿F) : htpy_formal_sol R :=
{ bs := λ t m, (F (t, m)).1.2,
  ϕ := λ t m, (F (t, m)).2,
  smooth' := sorry,
  is_sol' := λ t m, begin
    convert hsol (t, m),
    refine  one_jet_bundle.ext IM M IX X _ _ _,
    rw hsec,
    all_goals { refl }
    end}

lemma index_type.lt_or_eq_succ (N n : ℕ) :
  (n : index_type N) < (n+1 : ℕ) ∨ (n : index_type N) = (n+1 : ℕ) :=
begin
  rw or_comm,
  exact eq_or_lt_of_le (indexing.mono_from n.le_succ)
end

lemma index_type.le_or_lt_succ {N n : ℕ} (hn : (n : index_type N) < (n+1 : ℕ)) (j : index_type N) :
  j ≤ n ↔ j < (n + 1 : ℕ) :=
begin
  split ; intros hj,
  { exact hj.trans_lt hn },
  { cases N,
    exact nat.lt_succ_iff.mp hj,
    cases j with j hj',
    have : n < N + 1,
    {
      sorry },
    change (⟨j, hj'⟩ : fin (N+1)) ≤ if h : n < N + 1 then ⟨n, h⟩ else fin.last N,
    change (⟨j, hj'⟩ : fin (N+1)) < if h : n+1 < N + 1 then ⟨n+1, h⟩ else fin.last N at hj,
    rw dif_pos this,
    change j ≤ n,
    sorry
    /- --dsimp [index_type] at j,
    change j < if h : n+1 < N + 1 then ⟨n+1, h⟩ else fin.last N at hj,
    change j ≤ if h : n < N + 1 then ⟨n, h⟩ else fin.last N,
    split_ifs,
    { cases j with j hj',
      change j ≤ n,
      split_ifs at hj,
      exact nat.lt_succ_iff.mp hj,
      cases N,
      apply (nat.lt_succ_iff.mp hj').trans n.zero_le,

      change j < N + 1 at hj,
      have := nat.lt_succ_iff.mp hj,
      sorry },
    exact j.le_last -/ }
end

lemma index_type.tendsto_coe_at_top (N : ℕ) : tendsto (coe : ℕ → index_type N) at_top at_top :=
sorry

lemma index_type.not_lt_zero {N : ℕ} (j : index_type N) : ¬ (j < 0) :=
sorry

lemma inductive_construction {X Y : Type*} [topological_space X]
  (P₀ P₁ : (Σ x : X, germ (𝓝 x) Y) → Prop) {N : ℕ} {U K : index_type N → set X}
  --(U_op : ∀ i, is_open (U i)) (K_cpct : ∀ i, is_compact (K i)) (K_sub_U : ∀ i, K i ⊆ U i)
  (U_fin : locally_finite U) (K_cover : (⋃ i, K i) = univ)
  (init : ∃ f : X → Y, ∀ x, P₀ ⟨x, f⟩)
  (ind : ∀ (i : index_type N) (f : X → Y), (∀ x, P₀ ⟨x, f⟩) → (∀ x ∈ ⋃ j < i, K j, P₁ ⟨x, f⟩) →
    ∃ f' : X → Y, (∀ x, P₀ ⟨x, f'⟩) ∧ (∀ x ∈ ⋃ j ≤ i, K j, P₁ ⟨x, f'⟩) ∧ ∀ x ∉ U i, f' x = f x) :
    ∃ f : X → Y, ∀ x, P₀ ⟨x, f⟩ ∧ P₁ ⟨x, f⟩ :=
begin
  let P : ℕ → (X → Y) → Prop :=
    λ n f, (∀ x, P₀ ⟨x, f⟩) ∧ ∀ x ∈ (⋃ i ≤ (n : index_type N) , K i), P₁ ⟨x, f⟩,
  let Q : ℕ → (X → Y) → (X → Y) → Prop :=
    λ n f f', ((((n+1:ℕ) : index_type N) = n) → f' = f) ∧  ∀ x ∉ U (n + 1 : ℕ), f' x = f x,
  obtain ⟨f, hf⟩ : ∃ f : ℕ → X → Y, ∀ n, P n (f n) ∧ Q n (f n) (f $ n + 1),
  { apply exists_by_induction',
    { dsimp [P],
      cases init with f₀ hf₀,
      rcases ind 0 f₀ hf₀ _ with ⟨f', h₀f', h₁f', hf'⟩,
      use [f', h₀f'],
      intros x hx,
      apply h₁f' _ hx,
      have : (⋃ (j : index_type N) (H : j < 0), K j) = ∅,
      { simp [index_type.not_lt_zero] },
      simp only [this, mem_empty_iff_false, is_empty.forall_iff, implies_true_iff] },
    { rintros n f ⟨h₀f, h₁f⟩,
      rcases index_type.lt_or_eq_succ N n with hn | hn,
      { simp_rw index_type.le_or_lt_succ hn at h₁f,
        rcases ind (n+1 : ℕ) f h₀f h₁f with ⟨f', h₀f', h₁f', hf'⟩,
        exact ⟨f', ⟨h₀f', h₁f'⟩, ⟨λ hn', (hn.ne hn'.symm).elim, hf'⟩⟩ },
      { simp only [hn] at h₁f,
        exact ⟨f, ⟨h₀f, h₁f⟩, λ hn, rfl, λ x hx, rfl⟩ } } },
  dsimp only [P, Q] at hf,
  simp only [forall_and_distrib] at hf,
  rcases hf with ⟨⟨h₀f, h₁f⟩, hf, hf'⟩,
  rcases U_fin.exists_forall_eventually_of_indexing hf' hf with ⟨F, hF⟩,
  refine ⟨F, λ x, _,⟩,
  have : ∀ᶠ (n : ℕ) in at_top, x ∈ ⋃ i ≤ (n : index_type N), K i,
  { have : x ∈ ⋃ (i : index_type N), K i := K_cover.symm ▸ (mem_univ x),
    rcases mem_Union.mp this with ⟨i, hi⟩,
    apply (filter.tendsto_at_top.mp (index_type.tendsto_coe_at_top N) i).mono,
    intros n hn,
    exact mem_Union₂.mpr ⟨i, hn, hi⟩ },
  rcases eventually_at_top.mp ((hF x).and this) with ⟨n₀, hn₀⟩,
  rcases hn₀ n₀ le_rfl with ⟨hx, hx'⟩,
  rw germ.coe_eq.mpr hx.symm,
  exact ⟨h₀f n₀ x, h₁f n₀ x hx'⟩
end

-- temporary assumptions to avoid stupid case disjunction and instance juggling

variables [nonempty M] [nonempty X] [locally_compact_space M] [locally_compact_space X]

local notation `J¹` := one_jet_bundle IM M IX X

def is_holonomic_germ {p : ℝ × M} (φ : germ (𝓝 p) J¹) : Prop :=
quotient.lift_on' φ (λ F, mfderiv IM IX (λ x, (F (p.1, x)).1.2) p.2  = (F p).2) sorry

/-- The non-parametric version of Gromov's theorem -/
lemma rel_mfld.ample.satisfies_h_principle (hRample : R.ample) (hRopen : is_open R)
  (hA : is_closed A)
  (hδ_pos : ∀ x, 0 < δ x) (hδ_cont : continuous δ) :
  R.satisfies_h_principle A δ :=
begin
  borelize EX,
  refine rel_mfld.satisfies_h_principle_of_weak hA _,
  unfreezingI { clear_dependent A },
  intros A hA 𝓕₀ h𝓕₀,

  have cont : continuous 𝓕₀.bs, from 𝓕₀.smooth_bs.continuous,
  let L : localisation_data IM IX 𝓕₀.bs := std_localisation_data EM IM EX IX cont,
  let K : index_type L.N → set (ℝ × M) := λ i, (Icc 0 1).prod ((L.φ i) '' (closed_ball (0:EM) 1)),
  let U : index_type L.N → set (ℝ × M) := λ i, univ.prod (range (L.φ i)),
  have U_op : ∀ i, is_open (U i), sorry,
  have K_cpct : ∀ i, is_compact (K i), sorry,
  have K_sub_U : ∀ i, K i ⊆ U i, sorry,
  have U_fin : locally_finite U, sorry,
  have K_cover : (⋃ i, K i) = univ, sorry,
  let τ := λ x : M, min (δ x) (L.ε x),
  have τ_pos : ∀ x, 0 < τ x, from λ x, lt_min (hδ_pos x) (L.ε_pos x),
  have τ_cont : continuous τ, from hδ_cont.min L.ε_cont,
  -- Warning: the property `∀ᶠ (t, x) near (Iic 0 : set ℝ) ×ˢ univ, F t x = 𝓕₀ x`
  -- is weaker than `∀ᶠ t, near (Iic 0 : set ℝ), ∀ x, F t x = 𝓕₀ x` when `M` isn't compact,
  -- so we will need a variation of `localization_data.improve_htpy`
  let P₀ : (Σ p : ℝ × M, germ (𝓝 p) J¹) → Prop := λ F,
    F.2.value.1.1 = F.1.2 ∧
    F.2.value ∈ R ∧
    F.2.cont_mdiff_at' (𝓘(ℝ).prod IM) ((IM.prod IX).prod 𝓘(ℝ, EM →L[ℝ] EX)) ∞ ∧
    restrict_germ_predicate (λ F' : Σ p : ℝ × M, germ (𝓝 p) J¹, F'.2.value = 𝓕₀ F'.1.2)
                            ((Iic 0 : set ℝ) ×ˢ univ) F ∧
    restrict_germ_predicate (λ F' : Σ p : ℝ × M, germ (𝓝 p) J¹, F'.2.mfderiv (𝓘(ℝ).prod IM) ((IM.prod IX).prod 𝓘(ℝ, EM →L[ℝ] EX)) (1, 0) = 0)
                            ((Ici 1 : set ℝ) ×ˢ univ) F ∧
    restrict_germ_predicate (λ F' : Σ p : ℝ × M, germ (𝓝 p) J¹, F'.2.value = 𝓕₀ F'.1.2)
                            (univ ×ˢ A) F ∧
    dist (F.2.value.1.2) (𝓕₀.bs F.1.2) < τ F.1.2,

  /- let P₀ : (ℝ × M → J¹) → Prop := λ F,
    (∀ p, (F p).1.1 = p.2) ∧
    (∀ p, F p ∈ R) ∧
    smooth (𝓘(ℝ).prod IM) ((IM.prod IX).prod 𝓘(ℝ, EM →L[ℝ] EX)) F ∧
    (∀ᶠ t near (Iic 0 : set ℝ), ∀ x, F (t, x) = 𝓕₀ x) ∧
    (∀ᶠ t near (Ici 1 : set ℝ), ∀ x, F (t, x) = F (1, x)) ∧
    (∀ᶠ x near A, ∀ t, F (t, x) = 𝓕₀ x) ∧
    ∀ p : ℝ × M, dist ((F p).1.2) (𝓕₀.bs p.2) < τ p.2,-/
  let P₁ : (Σ p : ℝ × M, germ (𝓝 p) J¹) → Prop := λ F, F.1.1 = 1 → is_holonomic_germ F.2,
  rcases inductive_construction P₀ P₁ /- U_op K_cpct K_sub_U -/ U_fin K_cover _ _ with ⟨F, hF⟩,
    /- ⟨F, ⟨F_sec, F_sol, F_smooth, F_0, F_1, F_A, F_dist⟩, h₁F⟩ -/
  refine ⟨mk_htpy_formal_sol F _ _ _, _, _, _, _⟩,
  sorry { exact F_sec },
  sorry { exact F_sol },
  sorry { exact F_smooth },
  { -- almost exact F_0,
    sorry },
  sorry { exact λ x, h₁F (1, x) rfl },
  { -- almost exact F_A.nhds_set_forall_mem,
    sorry },
  sorry { exact λ t x, (F_dist (t, x)).le.trans (min_le_left _ _) },
  sorry { refine ⟨λ p, 𝓕₀ p.2, _, _, _, _, _, _, _⟩,
    { intros, refl },
    { exact λ p, 𝓕₀.is_sol p.2 },
    { exact 𝓕₀.smooth.comp smooth_snd },
    { exact eventually_of_forall (λ t x, rfl) },
    { exact eventually_of_forall (λ t x, rfl) },
    { exact eventually_of_forall (λ x t, rfl) },
    { intros p,
      change dist (𝓕₀.bs p.2) (𝓕₀.bs p.2) < τ p.2,
      rw dist_self,
      apply τ_pos } },
  sorry
  /- { rintros i F ⟨F_sec, F_sol, F_smooth, F_0, F_1, F_A, F_dist⟩ h₁F,
    let 𝓕 := mk_htpy_formal_sol F F_sec F_sol F_smooth,
    have apply_F : ∀ t x, 𝓕 t x = F (t, x),
    {
      sorry },
    have F_0' : ∀ᶠ (t : ℝ) near Iic 0, 𝓕 t = 𝓕 0,
    {
      sorry },
    have F_1' : ∀ᶠ (t : ℝ) near Ici 1, 𝓕 t = 𝓕 1,
    {
      sorry },
    have F_A' : ∀ᶠ x near A, (𝓕 0).is_holonomic_at x,
    {
      sorry },
    have F_A₀ : ∀ᶠ x near A, ∀ t, 𝓕 t x = 𝓕 0 x,
    {
      sorry },
    have F_dist : ∀ t x, dist ((𝓕 t).bs x) ((𝓕 0).bs x) < τ x,
    {
      sorry },
    have F_range : ∀ t, (𝓕 t).bs '' range (L.φ i) ⊆ range (L.ψj i),
    {
      sorry },
    have F_hol : ∀ᶠ x near ⋃ j < i, (L.φ j) '' closed_ball 0 1, (𝓕 1).is_holonomic_at x,
    {
      sorry },
    let K₀ : set EM := closed_ball 0 1,
    have hK₀ : is_compact K₀, from is_compact_closed_ball 0 1,
    let K₁ : set EM := closed_ball 0 2,
    have hK₁ : is_compact K₁, from is_compact_closed_ball 0 2,
    have hK₀K₁ : K₀ ⊆ interior K₁,
    sorry { dsimp [K₀, K₁],
      rw interior_closed_ball (0 : EM) (by norm_num : (2 : ℝ) ≠ 0),
      exact closed_ball_subset_ball (by norm_num) },
    have hC : is_closed (⋃ j < i, (L.φ j) '' closed_ball 0 1),
    { -- TODO: rewrite localization_data.is_closed_Union to match this.
      exact is_closed_bUnion (finite_Iio _) (λ j hj, (hK₀.image $ (L.φ j).continuous).is_closed) },
    rcases (L.φ i).improve_htpy_formal_sol (L.ψj i) hRample hRopen
        hA hC τ_pos τ_cont F_0' F_1' F_A' F_dist F_range F_A₀ F_hol hK₀ hK₁ hK₀K₁ with
        ⟨F', hF'₀, hF'₁, hF'A, hF'K₁, hF'τ, hF'K₀⟩,
    refine ⟨λ p, F' p.1 p.2, ⟨_, _, F'.smooth, _, _, _, _⟩, _, _⟩,
    sorry { exact λ p, rfl },
    sorry { exact λ p, F'.is_sol },
    {
      sorry },
    {
      sorry },
    {
      sorry },
    { -- dsimp only at hF'τ ⊢,
      sorry },
    sorry { rintros ⟨t, x⟩ hx (rfl : t = 1),
      simp only [K, ← const_prod_Union₂] at hx,
      replace hx := hx.2,
      rw [nhds_set_union, eventually_sup] at hF'K₀,
      replace hF'K₀ := hF'K₀.2.on_set,
      simp_rw [← L.Union_succ'] at hF'K₀,
      exact hF'K₀ x hx },
    sorry { rintros ⟨t, x⟩ H,
      rw ← apply_F,
      apply hF'K₁ t x (λ hx, H _),
      simp only [prod_mk_mem_set_prod_eq, mem_univ, true_and, not_exists, not_and, K],
      exact image_subset_range (L.φ i) _ hx } } -/
end
