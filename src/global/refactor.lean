
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

section

meta def prove_finiteness : tactic unit := `[intro x, apply set.to_finite]

structure local_prop (X Y : Type*) [topological_space X] :=
(s : X → set X)
(s_fin : ∀ x, (s x).finite . prove_finiteness)
(prop : Π x, (Π x' ∈ s x, germ (𝓝 x') Y) → Prop)

variables {X Y : Type*} [topological_space X]

/-- Evaluate a local property at a point on a given function. -/
def local_prop.eval  (P : local_prop X Y) (x : X) (f : X → Y) : Prop :=
P.prop x (λ x' hx', (f : germ (𝓝 x') Y))

instance : has_coe_to_fun (local_prop X Y) (λ _, X → (X → Y) → Prop) :=
⟨local_prop.eval⟩

/-- A local property depending on a single point. -/
def local_prop.single (P : Π x : X, germ (𝓝 x) Y → Prop) : local_prop X Y :=
{ s := λ x, {x},
  prop := λ x φ, P x (φ _ (mem_singleton x))  }

@[simp]
lemma local_prop.eval_single (P : Π x : X, (germ (𝓝 x) Y → Prop)) (f : X → Y) (x : X) :
  local_prop.single P x f ↔ P x f :=
iff.rfl

/-- A local property depending on a point and its image under a given function. -/
def local_prop.pair (π : X → X)
  (P : Π x : X, germ (𝓝 x) Y → germ (𝓝 $ π x) Y →  Prop) : local_prop X Y :=
{ s := λ x : X, {x, π x},
  prop := λ x φ, P x (φ x (mem_insert _ _)) (φ _ $ mem_insert_iff.mpr $ or.inr $ mem_singleton _) }

/-- The local property asserting `f x = f (π x)`. -/
def local_prop.equality (π : X → X) : local_prop X Y :=
  local_prop.pair π (λ x φ ψ, φ.value = ψ.value)

@[simp]
lemma local_prop.eval_pair {π : X → X}
  {P : Π x : X, germ (𝓝 x) Y → germ (𝓝 $ π x) Y →  Prop} {f : X → Y} {x : X} :
  local_prop.pair π P x f ↔ P x f f :=
iff.rfl

lemma local_prop.equality_iff {π : X → X} (f : X → Y) (x : X) :
  local_prop.equality π x f ↔ f x = f (π x) := iff.rfl

end


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

def restrict_germ_predicate' {X Y : Type*} [topological_space X]
  (P : Π x : X, germ (𝓝 x) Y → Prop) (A : set X) : Π x : X, germ (𝓝 x) Y → Prop :=
λ x φ, quotient.lift_on' φ (λ f, x ∈ A → ∀ᶠ y in 𝓝 x, P y f) begin
  have : ∀ f f' : X → Y, f =ᶠ[𝓝 x] f' → (∀ᶠ y in 𝓝 x, P y f) → ∀ᶠ y in 𝓝 x, P y f',
  { intros f f' hff' hf,
    apply (hf.and $ eventually.eventually_nhds hff').mono,
    rintros y ⟨hy, hy'⟩,
    rwa germ.coe_eq.mpr (eventually_eq.symm hy') },
  exact λ f f' hff', propext $ forall_congr $ λ _, ⟨this f f' hff', this f' f hff'.symm⟩,
end

lemma forall_restrict_germ_predicate'_iff {X Y : Type*} [topological_space X]
  {P : Π x : X, germ (𝓝 x) Y → Prop} {A : set X} {f : X → Y} :
  (∀ x, restrict_germ_predicate' P A x f) ↔ ∀ᶠ x near A, P x f :=
by { rw eventually_nhds_set_iff, exact iff.rfl }

lemma  forall_restrict_germ_predicate'_of_forall {X Y : Type*} [topological_space X]
  {P : Π x : X, germ (𝓝 x) Y → Prop} {A : set X} {f : X → Y} (h : ∀ x, P x f) :
  ∀ x, restrict_germ_predicate' P A x f :=
forall_restrict_germ_predicate'_iff.mpr (eventually_of_forall h)

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

def mk_formal_sol (F : M → one_jet_bundle IM M IX X) (hsec : ∀ x, (F x).1.1 = x)
(hsol : ∀ x, F x ∈ R)
(hsmooth : smooth IM ((IM.prod IX).prod 𝓘(ℝ, EM →L[ℝ] EX)) F) : formal_sol R :=
{ bs := λ m, (F m).1.2,
  ϕ := λ m, (F m).2,
  smooth' := sorry,
  is_sol' := λ m, begin
    convert hsol m,
    refine  one_jet_bundle.ext IM M IX X _ _ _,
    rw hsec,
    all_goals { refl }
    end}

@[simp]
lemma mk_formal_sol_apply (F : M → one_jet_bundle IM M IX X) (hsec : ∀ x, (F x).1.1 = x)
(hsol : ∀ x, F x ∈ R)
(hsmooth : smooth IM ((IM.prod IX).prod 𝓘(ℝ, EM →L[ℝ] EX)) ↿F)  :
  (mk_formal_sol F hsec hsol hsmooth : M → one_jet_bundle IM M IX X) = F :=
begin
  ext x ; try { refl },
  rw hsec,
  refl
end

@[simp]
lemma mk_formal_sol_bs_apply (F : M → one_jet_bundle IM M IX X) (hsec : ∀ x, (F x).1.1 = x)
(hsol : ∀ x, F x ∈ R)
(hsmooth : smooth IM ((IM.prod IX).prod 𝓘(ℝ, EM →L[ℝ] EX)) ↿F)  (x : M) :
  (mk_formal_sol F hsec hsol hsmooth).bs x = (F x).1.2 :=
rfl


def mk_htpy_formal_sol (F : ℝ → M → one_jet_bundle IM M IX X) (hsec : ∀ t x, (F t x).1.1 = x)
(hsol : ∀ t x, F t x ∈ R)
(hsmooth : smooth (𝓘(ℝ).prod IM) ((IM.prod IX).prod 𝓘(ℝ, EM →L[ℝ] EX)) ↿F) : htpy_formal_sol R :=
{ bs := λ t m, (F t m).1.2,
  ϕ := λ t m, (F t m).2,
  smooth' := sorry,
  is_sol' := λ t m, begin
    convert hsol t m,
    refine  one_jet_bundle.ext IM M IX X _ _ _,
    rw hsec,
    all_goals { refl }
    end}

@[simp]
lemma mk_htpy_formal_sol_apply (F : ℝ → M → one_jet_bundle IM M IX X) (hsec : ∀ t x, (F t x).1.1 = x)
(hsol : ∀ t x, F t x ∈ R)
(hsmooth : smooth (𝓘(ℝ).prod IM) ((IM.prod IX).prod 𝓘(ℝ, EM →L[ℝ] EX)) ↿F) (t : ℝ) :
  (mk_htpy_formal_sol F hsec hsol hsmooth t : M → one_jet_bundle IM M IX X) = F t :=
begin
  ext x ; try { refl },
  rw hsec,
  refl
end

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

example {α γ : Type*} (β : α → Type*) : ((Σ a, β a) → γ) ≃ Π a, (β a → γ) :=
{ to_fun := λ f a b, f ⟨a, b⟩,
  inv_fun := λ f p, f p.1 p.2,
  left_inv := begin
    intros f,
    ext ⟨a, b⟩,
    refl
  end,
  right_inv := begin
    intros f,
    ext a,
    refl
  end }


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
  refine ⟨F, λ x, _⟩,
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
.
/- TODO: think whether `∀ x ∈ ⋃ j < i, K j, P₁ x f` should be something more general. -/
lemma inductive_htpy_construction {X Y : Type*} [topological_space X]
  {N : ℕ} {U K : index_type N → set X}
  (P₀ P₁ : Π x : X, germ (𝓝 x) Y → Prop) (P₂ : Π t : ℝ, Π x : X, germ (𝓝 (t, x)) Y → Prop)
  (hP₂ : ∀ a b t x (f : ℝ × X → Y), P₂ (a*t+b) x f → P₂ t x (λ p : ℝ × X, f (a*p.1+b, p.2)))
  (U_fin : locally_finite U) (K_cover : (⋃ i, K i) = univ)
  {f₀ : X → Y} (hf : ∀ x, P₀ x f₀)
  (ind : ∀ (i : index_type N) (f : X → Y), (∀ x, P₀ x f) → (∀ᶠ x near ⋃ j < i, K j, P₁ x f) →
    ∃ F : ℝ → X → Y, (∀ t, ∀ x, P₀ x $ F t) ∧ (∀ᶠ x near ⋃ j ≤ i, K j, P₁ x $ F 1) ∧
                     (∀ t x, P₂ t x ↿F) ∧ (∀ t, ∀ x ∉ U i, F t x = f x) ∧
                     (∀ᶠ t near Iic 0, F t = f) ∧ (∀ᶠ t near Ici 1, F t = F 1)) :
  ∃ F : ℝ → X → Y, F 0 = f₀ ∧ (∀ t x, P₀ x (F t)) ∧ (∀ x, P₁ x (F 1)) ∧ (∀ t x, P₂ t x ↿F) :=
sorry

-- temporary assumptions to avoid stupid case disjunction and instance juggling

variables [nonempty M] [nonempty X] [locally_compact_space M] [locally_compact_space X]

local notation `J¹` := one_jet_bundle IM M IX X

def is_holonomic_germ {x : M} (φ : germ (𝓝 x) J¹) : Prop :=
quotient.lift_on' φ (λ F, mfderiv IM IX (λ x', (F x').1.2) x  = (F x).2)
begin
  letI : setoid (M → J¹) := (𝓝 x).germ_setoid (one_jet_bundle IM M IX X),
  have key : ∀ f g, f ≈ g → (λ (F : M → one_jet_bundle IM M IX X), mfderiv IM IX (λ (x' : M), (F x').fst.snd) x = (F x).snd) f →
  (λ (F : M → one_jet_bundle IM M IX X), mfderiv IM IX (λ (x' : M), (F x').fst.snd) x = (F x).snd) g,
  { intros f g hfg hf,
    have hfg' : (λ x', (f x').1.2) =ᶠ[𝓝 x] (λ x', (g x').1.2),
      from hfg.fun_comp (λ s, s.1.2),
    rw [← hfg'.mfderiv_eq, hf, hfg.self_of_nhds] },
  exact λ f g H, propext ⟨key f g H, key g f H.symm⟩,
end

lemma is_holonomic_germ_mk_formal_sol (F : M → one_jet_bundle IM M IX X) (hsec : ∀ x, (F x).1.1 = x)
(hsol : ∀ x, F x ∈ R)
(hsmooth : smooth IM ((IM.prod IX).prod 𝓘(ℝ, EM →L[ℝ] EX)) ↿F)  (x : M) :
  is_holonomic_germ (F : germ (𝓝 x) J¹) ↔ (mk_formal_sol F hsec hsol hsmooth).is_holonomic_at x :=
iff.rfl

lemma forall₂_and_distrib {α β : Sort*} {p q : α → β → Prop} :
  (∀ x y, p x y ∧ q x y) ↔ (∀ x y, p x y) ∧ ∀ x y, q x y :=
begin
  split ; intros h,
  split ; intros,
  exact (h x y).1,
  exact (h x y).2,
  intros x y,
   exact ⟨h.1 x y, h.2 x y⟩
end

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
    restrict_germ_predicate' (λ x F', F'.value = 𝓕₀ x) A x F ∧
    dist (F.value.1.2) (𝓕₀.bs x) < τ x,

  let P₁ : Π x : M, germ (𝓝 x) J¹ → Prop := λ x F, is_holonomic_germ F,
  let P₂ : Π t : ℝ, Π x : M, germ (𝓝 (t, x)) J¹ → Prop := λ t x F,
    F.cont_mdiff_at' (𝓘(ℝ).prod IM) ((IM.prod IX).prod 𝓘(ℝ, EM →L[ℝ] EX)) ∞,
  have hP₂ : ∀ (a b t : ℝ) (x : M) (f : ℝ × M → one_jet_bundle IM M IX X),
    P₂ (a * t + b) x f → P₂ t x (λ (p : ℝ × M), f (a * p.1 + b, p.2)),
  { intros a b t x f h,
    dsimp only [P₂] at h ⊢,
    change cont_mdiff_at (𝓘(ℝ, ℝ).prod IM) ((IM.prod IX).prod 𝓘(ℝ, EM →L[ℝ] EX)) ∞
      (f ∘ λ (p : ℝ × M), (a * p.1 + b, p.2)) (t, x),
    change cont_mdiff_at (𝓘(ℝ, ℝ).prod IM) ((IM.prod IX).prod 𝓘(ℝ, EM →L[ℝ] EX)) ∞
      f ((λ (p : ℝ × M), (a * p.1 + b, p.2)) (t, x)) at h,
    have : cont_mdiff_at (𝓘(ℝ, ℝ).prod IM) (𝓘(ℝ, ℝ).prod IM) ∞ (λ (p : ℝ × M), (a * p.1 + b, p.2)) (t, x),
    { have h₁ : cont_mdiff_at 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (λ t, a * t + b) t,
      from cont_mdiff_at_iff_cont_diff_at.mpr
        (((cont_diff_at_id : cont_diff_at ℝ ∞ id t).const_smul a).add cont_diff_at_const),
      exact h₁.prod_map cont_mdiff_at_id },
    exact h.comp (t, x) this },
  have init : ∀ x : M, P₀ x (𝓕₀ : M → J¹),
  { refine λ x, ⟨rfl, 𝓕₀.is_sol x, 𝓕₀.smooth x, _, _⟩,
    { revert x,
      exact forall_restrict_germ_predicate'_of_forall (λ x, rfl) },
    { erw dist_self,
      exact τ_pos x } },
  have ind : ∀ (i : index_type L.N) (f : M → J¹), (∀ x, P₀ x f) → (∀ᶠ x near ⋃ j < i, K j, P₁ x f) →
    ∃ F : ℝ → M → J¹, (∀ t, ∀ x, P₀ x $ F t) ∧ (∀ᶠ x near ⋃ j ≤ i, K j, P₁ x $ F 1) ∧
                     (∀ t x, P₂ t x ↿F) ∧ (∀ t, ∀ x ∉ U i, F t x = f x) ∧
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
    rw forall_restrict_germ_predicate'_iff at hf_A,
    let F : formal_sol R := mk_formal_sol f hf_sec hf_sol hf_smooth,
    have hFA : ∀ᶠ x near A, F.is_holonomic_at x,
    { apply (hf_A.and h𝓕₀).eventually_nhds_set.mono (λ x hx, _),
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
      exact ((one_jet_bundle_proj_continuous IM M IX X).comp this.continuous).snd.dist
        𝓕₀.smooth_bs.continuous },
    rcases (L.φ i).improve_formal_sol (L.ψj i) hRample hRopen hA hC η_pos η_cont hFA hFφψ hf₁
      hK₀ hK₁ hK₀K₁ with ⟨F', hF'₀, hF'₁, hF'A, hF'K₁, hF'η, hF'K₀⟩,
    refine ⟨λ t x, F' t x, _, _, _, _, _, _⟩,
    { refine λ t x, ⟨rfl, F'.is_sol, (F' t).smooth x, _, _⟩,
      { revert x,
        rw forall_restrict_germ_predicate'_iff,
        apply (hF'A.and hf_A).mono,
        rintros x ⟨hx, hx'⟩,
        change F' t x = _,
        rw [hx t, ← hx', mk_formal_sol_apply],
        refl },
      { calc dist (F' t x).1.2 (𝓕₀.bs x) ≤ dist (F' t x).1.2 (F.bs x) + dist (F.bs x) (𝓕₀.bs x) : dist_triangle _ _ _
        ... < η x + dist (F.bs x) (𝓕₀.bs x) : add_lt_add_right (hF'η t x) _
        ... = τ x : by simp [η] } },
    { rw [nhds_set_union, eventually_sup] at hF'K₀,
      replace hF'K₀ := hF'K₀.2,
      simp_rw [← L.Union_succ'] at hF'K₀,
      exact hF'K₀ },
    { exact λ t x, F'.smooth (t, x) },
    { intros t x hx,
      rw hF'K₁ t x ((mem_range_of_mem_image _ _).mt hx),
      simp [F] },
    { apply hF'₀.mono (λ x hx, _),
      erw hx,
      ext1 y,
      simp [F] },
    { apply hF'₁.mono (λ x hx, _),
      rw hx } },
  rcases inductive_htpy_construction P₀ P₁ P₂ hP₂ L.lf_φ K_cover init ind with ⟨F, hF₀, hFP₀, hFP₁, hFP₂⟩,
  simp only [P₀, forall₂_and_distrib] at hFP₀,
  rcases hFP₀ with ⟨hF_sec, hF_sol, hF_smooth, hF_A, hF_dist⟩,
  replace hFP₂ :  smooth (𝓘(ℝ, ℝ).prod IM) ((IM.prod IX).prod 𝓘(ℝ, EM →L[ℝ] EX)) ↿F := λ ⟨t, x⟩, hFP₂ t x,
  refine ⟨mk_htpy_formal_sol F hF_sec hF_sol hFP₂, _, _, _, _⟩,
  { intros x,
    rw [mk_htpy_formal_sol_apply, hF₀] },
  { exact hFP₁ },
  { intros x hx t,
    rw mk_htpy_formal_sol_apply,
    exact (forall_restrict_germ_predicate'_iff.mp $ hF_A t).on_set x hx },
  { intros t x,
    change dist (mk_htpy_formal_sol F hF_sec hF_sol hFP₂ t x).1.2 (𝓕₀.bs x) ≤ δ x,
    rw mk_htpy_formal_sol_apply,
    exact (hF_dist t x).le.trans (min_le_left _ _) }
end
