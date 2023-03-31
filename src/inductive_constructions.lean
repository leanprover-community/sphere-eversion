import to_mathlib.data.set.prod
import to_mathlib.data.set.lattice
import to_mathlib.data.nat.basic
import to_mathlib.topology.constructions
import to_mathlib.topology.germ
import to_mathlib.topology.misc

import indexing
import notations

open set filter prod topological_space
open_locale topology unit_interval

/-!
Notes by Patrick:

The goal of this file is to explore how to prove `exists_surrounding_loops` (or rather its version
with `C = U = univ` which is the only needed case) in a way that uncouples the general
topological argument from the things specific to loops. The general lemma is meant to
be something like `inductive_construction'` below.
-/


section inductive_construction
/-!
Notes by Patrick:

In this section, I took lemmas that used to exist when I worked on the inductive construction
refactor. In particular there is the lemma which can't quite be used to prove
`inductive_htpy_construction`, namely `inductive_construction`.

In that lemma, the covering is fixed. Lemma `inductive_construction'` combines this with an argument
using local existence and exhaustions. A technical intermediate statement is
`inductive_construction''`.
-/

lemma index_type.tendsto_coe_at_top (N : ℕ) : tendsto (coe : ℕ → index_type N) at_top at_top :=
tendsto_at_top_at_top.mpr
  (λ i, ⟨indexing.to_nat i, λ n hn,(indexing.from_to i) ▸ indexing.coe_mono hn⟩)

lemma locally_finite.exists_forall_eventually_of_indexing
  {α X ι : Type*} [topological_space X] [linear_order ι] [indexing ι] {f : ℕ → X → α}
  {V : ι → set X} (hV : locally_finite V)
  (h : ∀ n : ℕ, ∀ x ∉ V ((n + 1) : ℕ), f (n + 1) x = f n x)
  (h' : ∀ n : ℕ, ((n+1 : ℕ) : ι) = n → f (n + 1) = f n) :
  ∃ (F : X → α), ∀ (x : X), ∀ᶠ (n : ℕ) in filter.at_top, f n =ᶠ[𝓝 x] F :=
begin
  let π :  ℕ → ι := indexing.from_nat,
  choose U hUx hU using hV,
  choose i₀ hi₀ using λ x, (hU x).bdd_above,
  let n₀ : X → ℕ := indexing.to_nat ∘ i₀,
  have key : ∀ {x} {n}, n ≥ n₀ x → ∀ {y}, y ∈ U x → f n y = f (n₀ x) y,
  { intros x n hn,
    rcases le_iff_exists_add.mp hn with ⟨k, rfl⟩, clear hn,
    intros y hy,
    induction k with k hk,
    { simp },
    { rw ← hk, clear hk,
      have : ∀ n, π n < π (n+1) ∨ π n = π (n+1),
      exact λ n, lt_or_eq_of_le (indexing.mono_from n.le_succ),
      rcases this (n₀ x + k) with H | H ; clear this,
      { have ineq : π (n₀ x + k + 1) > i₀ x,
        { suffices : i₀ x ≤ π (n₀ x + k), from lt_of_le_of_lt this H,
          rw ← indexing.from_to (i₀ x),
          exact indexing.mono_from le_self_add },
        apply h,
        rintro (hy' : y ∈ V (π (n₀ x + k + 1))),
        have := hi₀ x ⟨y, ⟨hy', hy⟩⟩, clear hy hy',
        exact lt_irrefl _ (lt_of_le_of_lt this ineq) },
      { erw [← (h' _ H.symm)],
        refl } } },
  refine ⟨λ x, f (n₀ x) x, λ x, _⟩,
  change ∀ᶠ (n : ℕ) in at_top, f n =ᶠ[𝓝 x] λ (y : X), f (n₀ y) y,
  apply (eventually_gt_at_top (n₀ x)).mono (λ n hn, _),
  apply mem_of_superset (hUx x) (λ y hy, _),
  change f n y = f (n₀ y) y,
  calc f n y = f (n₀ x) y : key hn.le hy
  ... = f (max (n₀ x) (n₀ y)) y : (key (le_max_left _ _) hy).symm
  ... = f (n₀ y) y : key (le_max_right _ _) (mem_of_mem_nhds $ hUx y)
end

lemma inductive_construction_alt {X Y : Type*} [topological_space X]
  {N : ℕ} {U K : index_type N → set X}
  (P₀ : Π x : X, germ (𝓝 x) Y → Prop) (P₁ : Π i : index_type N, Π x : X, germ (𝓝 x) Y → Prop)
  (U_fin : locally_finite U)
  (init : ∃ f : X → Y, ∀ x, P₀ x f)
  (ind : ∀ (i : index_type N) (f : X → Y), (∀ x, P₀ x f) → (∀ j < i, ∀ᶠ x near K j, P₁ j x f) →
    ∃ f' : X → Y, (∀ x, P₀ x f') ∧ (∀ j ≤ i, ∀ᶠ x near K j, P₁ j x f') ∧ ∀ x ∉ U i, f' x = f x) :
    ∃ f : X → Y, (∀ x, P₀ x f) ∧ ∀ j, ∀ᶠ x near K j, P₁ j x f :=
begin
  let P : ℕ → (X → Y) → Prop :=
    λ n f, (∀ x, P₀ x f) ∧ ∀ j : index_type N, j ≤ n → ∀ᶠ x near K j, P₁ j x f,
  let Q : ℕ → (X → Y) → (X → Y) → Prop :=
    λ n f f', ((((n+1:ℕ) : index_type N) = n) → f' = f) ∧ ∀ x ∉ U (n + 1 : ℕ), f' x = f x,
  obtain ⟨f, hf⟩ : ∃ f : ℕ → X → Y, ∀ n, P n (f n) ∧ Q n (f n) (f $ n + 1),
  { apply exists_by_induction',
    { dsimp [P],
      cases init with f₀ hf₀,
      rcases ind 0 f₀ hf₀ _ with ⟨f', h₀f', h₁f', hf'⟩,
      use [f', h₀f', h₁f'],
      simp [index_type.not_lt_zero] },
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
  refine ⟨F, λ x, _, λ j, _⟩,
  { rcases (hF x).exists with ⟨n₀, hn₀⟩,
    simp only [germ.coe_eq.mpr hn₀.symm, h₀f n₀ x] },
  apply eventually_nhds_set_iff.mpr,
  intros x hx,
  rcases ((hF x).and $ (filter.tendsto_at_top.mp (index_type.tendsto_coe_at_top N) j)).exists
    with ⟨n₀, hn₀, hn₀'⟩,
  apply ((eventually_nhds_set_iff.mp (h₁f _ _ hn₀') x hx).and $
         eventually_eventually_eq_nhds.mpr hn₀).mono,
  rintros y ⟨hy, hy'⟩,
  rwa germ.coe_eq.mpr hy'.symm
end

lemma inductive_construction {X Y : Type*} [topological_space X]
  {N : ℕ} {U K : index_type N → set X}
  (P₀ P₁ : Π x : X, germ (𝓝 x) Y → Prop)
  (U_fin : locally_finite U) (K_cover : (⋃ i, K i) = univ)
  (init : ∃ f : X → Y, ∀ x, P₀ x f)
  (ind : ∀ (i : index_type N) (f : X → Y), (∀ x, P₀ x f) → (∀ᶠ x near ⋃ j < i, K j, P₁ x f) →
    ∃ f' : X → Y, (∀ x, P₀ x f') ∧ (∀ᶠ x near ⋃ j ≤ i, K j, P₁ x f') ∧ ∀ x ∉ U i, f' x = f x) :
    ∃ f : X → Y, ∀ x, P₀ x f ∧ P₁ x f :=
begin
  rcases inductive_construction_alt P₀ (λ j, P₁) U_fin init
    (by simpa only [eventually_nhds_set_Union₂] using ind) with ⟨f, h₀f, h₁f⟩,
  refine ⟨f, λ x, ⟨h₀f x, _⟩⟩,
  obtain ⟨j, hj⟩ : ∃ j, x ∈ K j, by simpa using (by simp [K_cover]  : x ∈ ⋃ j, K j),
  exact (h₁f j).on_set _ hj
end

/-- We are given a suitably nice topological space `X` and three local constraints `P₀`,`P₀'` and
`P₁` on maps from `X` to some type `Y`. All maps entering the discussion are required to statisfy
`P₀` everywhere. The goal is to turn a map `f₀` satisfying `P₁` near a compact set `K` into
one satisfying everywhere without changing `f₀` near `K`. The assumptions are:
* For every `x` in `X` there is a map which satisfies `P₁` near `x`
* One can patch two maps `f₁ f₂` satisfying `P₁` on open sets `U₁` and `U₂` respectively
  and such that `f₁` satisfies `P₀'` everywhere into a map satisfying `P₁` on `K₁ ∪ K₂` for any
  compact sets `Kᵢ ⊆ Uᵢ` and `P₀'` everywhere. -/
lemma inductive_construction'' {X Y : Type*} [emetric_space X] [locally_compact_space X]
  [second_countable_topology X]
  (P₀ P₀' P₁ : Π x : X, germ (𝓝 x) Y → Prop)
  {f₀ : X → Y} (hP₀f₀ : ∀ x, P₀ x f₀ ∧ P₀' x f₀ )
  (loc : ∀ x, ∃ f : X → Y, (∀ x, P₀ x f) ∧ ∀ᶠ x' in 𝓝 x, P₁ x' f)
  (ind : ∀ {U₁ U₂ K₁ K₂ : set X} {f₁ f₂ : X → Y}, is_open U₁ → is_open U₂ →
     is_closed K₁ → is_closed K₂ → K₁ ⊆ U₁ → K₂ ⊆ U₂ → (∀ x, P₀ x f₁ ∧ P₀' x f₁) → (∀ x, P₀ x f₂) →
     (∀ x ∈ U₁, P₁ x f₁) → (∀ x ∈ U₂, P₁ x f₂) →
     ∃ f : X → Y, (∀ x, P₀ x f ∧ P₀' x f ) ∧ (∀ᶠ x near K₁ ∪ K₂, P₁ x f) ∧
                  (∀ᶠ x near K₁ ∪ U₂ᶜ, f x = f₁ x)) :
    ∃ f : X → Y, ∀ x, P₀ x f ∧ P₀' x f ∧ P₁ x f :=
begin
  let P : set X → Prop := λ U, ∃ f : X → Y, (∀ x, P₀ x f) ∧ (∀ x ∈ U, P₁ x f),
  have hP₁ : antitone P,
  { rintros U V hUV ⟨f, h, h'⟩,
    exact ⟨f, h, λ x hx, h' x (hUV hx)⟩ },
  have hP₂ : P ∅, from ⟨f₀, λ x, (hP₀f₀ x).1, λ x h, h.elim⟩,
  have hP₃ : ∀ (x : X), x ∈ univ → (∃ (V : set X) (H : V ∈ 𝓝 x), P V),
  { rintros x -,
    rcases loc x with ⟨f, h₀f, h₁f⟩,
    exact ⟨_, h₁f, f, h₀f, λ x, id⟩ },
  rcases exists_locally_finite_subcover_of_locally is_closed_univ hP₁ hP₂ hP₃ with
    ⟨K, (U : index_type 0 →set X) , K_cpct, U_op, hU, hKU, U_loc, hK⟩,
  simp_rw ← and_assoc,
  apply inductive_construction (λ x φ, P₀ x φ ∧ P₀' x φ) P₁ U_loc (eq_univ_of_univ_subset hK)
    ⟨f₀, hP₀f₀⟩,
  rintros (n : ℕ) f h₀f (h₁f : ∀ᶠ x near ⋃ j < n, K j, P₁ x f),
  have cpct : is_closed ⋃ j < n, K j,
  { rw show (⋃ j < n, K j) = ⋃ j ∈ finset.range n, K j, by simp only [finset.mem_range],
    apply (finset.range n).is_closed_bUnion _ (λ j _, (K_cpct j).is_closed) },
  rcases hU n with ⟨f', h₀f', h₁f'⟩,
  rcases mem_nhds_set_iff_exists.mp h₁f with ⟨V, V_op, hKV, h₁V⟩,
  rcases ind V_op (U_op n) cpct (K_cpct n).is_closed
    hKV (hKU n) h₀f h₀f' h₁V h₁f' with ⟨F, h₀F, h₁F, hF⟩,
  simp_rw ← bUnion_le at h₁F,
  exact ⟨F, h₀F, h₁F, λ x hx, hF.on_set x (or.inr hx)⟩
end

/-- We are given a suitably nice topological space `X` and two local constraints `P₀` and `P₁`
on maps from `X` to some type `Y`. All maps entering the discussion are required to statisfy `P₀`
everywhere. The goal is to turn a map `f₀` satisfying `P₁` near a compact set `K` into
one satisfying everywhere without changing `f₀` near `K`. The assumptions are:
* For every `x` in `X` there is a map which satisfies `P₁` near `x`
* One can patch two maps `f₁ f₂` satisfying `P₁` on open sets `U₁` and `U₂` respectively
  into a map satisfying `P₁` on `K₁ ∪ K₂` for any compact sets `Kᵢ ⊆ Uᵢ`.
This is deduced this version from the version where `K` is empty but adding some `P'₀`, see
`inductive_construction''`. -/
lemma inductive_construction' {X Y : Type*} [emetric_space X] [locally_compact_space X]
  [second_countable_topology X]
  (P₀ P₁ : Π x : X, germ (𝓝 x) Y → Prop)
  {K : set X} (hK : is_closed K)
  {f₀ : X → Y} (hP₀f₀ : ∀ x, P₀ x f₀) (hP₁f₀ : ∀ᶠ x near K, P₁ x f₀)
  (loc : ∀ x, ∃ f : X → Y, (∀ x, P₀ x f) ∧ ∀ᶠ x' in 𝓝 x, P₁ x' f)
  (ind : ∀ {U₁ U₂ K₁ K₂ : set X} {f₁ f₂ : X → Y}, is_open U₁ → is_open U₂ →
     is_closed K₁ → is_closed K₂ → K₁ ⊆ U₁ → K₂ ⊆ U₂ → (∀ x, P₀ x f₁) → (∀ x, P₀ x f₂) →
     (∀ x ∈ U₁, P₁ x f₁) → (∀ x ∈ U₂, P₁ x f₂) →
     ∃ f : X → Y, (∀ x, P₀ x f) ∧ (∀ᶠ x near K₁ ∪ K₂, P₁ x f) ∧ (∀ᶠ x near K₁ ∪ U₂ᶜ, f x = f₁ x)) :
    ∃ f : X → Y, (∀ x, P₀ x f ∧ P₁ x f) ∧ ∀ᶠ x near K, f x = f₀ x :=
begin
  let P₀' : Π x : X, germ (𝓝 x) Y → Prop := restrict_germ_predicate (λ x φ, φ.value = f₀ x) K,
  have hf₀ : ∀ x, P₀ x f₀ ∧ P₀' x f₀,
  { exact λ x, ⟨hP₀f₀ x, λ hx, eventually_of_forall (λ x', rfl)⟩ },
  have ind' : ∀ (U₁ U₂ K₁ K₂ : set X) {f₁ f₂ : X → Y}, is_open U₁ → is_open U₂ →
     is_closed K₁ → is_closed K₂ → K₁ ⊆ U₁ → K₂ ⊆ U₂ → (∀ x, P₀ x f₁ ∧ P₀' x f₁) → (∀ x, P₀ x f₂) →
     (∀ x ∈ U₁, P₁ x f₁) → (∀ x ∈ U₂, P₁ x f₂) →
     ∃ f : X → Y, (∀ x, P₀ x f ∧ P₀' x f ) ∧ (∀ᶠ x near K₁ ∪ K₂, P₁ x f) ∧
                  (∀ᶠ x near K₁ ∪ U₂ᶜ, f x = f₁ x),
  { intros U₁ U₂ K₁ K₂ f₁ f₂ U₁_op U₂_op K₁_cpct K₂_cpct hK₁U₁ hK₂U₂ hf₁ hf₂ hf₁U₁ hf₂U₂,
    obtain ⟨h₀f₁, h₀'f₁⟩ := forall_and_distrib.mp hf₁,
    rw forall_restrict_germ_predicate_iff at h₀'f₁,
    rcases (has_basis_nhds_set K).mem_iff.mp (hP₁f₀.germ_congr h₀'f₁) with ⟨U, ⟨U_op, hKU⟩, hU⟩,
    rcases ind (U_op.union U₁_op) U₂_op (hK.union K₁_cpct) K₂_cpct (union_subset_union hKU hK₁U₁)
      hK₂U₂ h₀f₁ hf₂ (λ x hx, hx.elim (λ hx, hU hx) (λ hx, hf₁U₁ x hx)) hf₂U₂ with ⟨f, h₀f, hf, h'f⟩,
    rw [union_assoc, eventually_nhds_set_union] at hf h'f,
    exact ⟨f, λ x, ⟨h₀f x, restrict_germ_predicate_congr (hf₁ x).2 h'f.1⟩, hf.2, h'f.2⟩ },
  rcases inductive_construction'' P₀ P₀' P₁ hf₀ loc ind' with ⟨f, hf⟩,
  simp only [forall_and_distrib, forall_restrict_germ_predicate_iff ] at hf ⊢,
  exact ⟨f, ⟨hf.1, hf.2.2⟩, hf.2.1⟩
end

end inductive_construction
