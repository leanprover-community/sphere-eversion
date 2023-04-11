import to_mathlib.data.set.prod
import to_mathlib.data.set.lattice
import to_mathlib.data.nat.basic
import to_mathlib.topology.constructions
import to_mathlib.topology.germ
import to_mathlib.topology.misc
import to_mathlib.order.filter.basic

import indexing
import notations
import interactive_expr
import tactic.induction

set_option trace.filter_inst_type true

open set filter prod topological_space function
open_locale topology unit_interval

/-!
Notes by Patrick:

The goal of this file is to explore how to prove `exists_surrounding_loops` and the local to global
inductive homotopy construction in a way that uncouples the general
topological argument from the things specific to loops or homotopies of jet sections.

First there is a lemma `inductive_construction` which abstracts the locally ultimately constant
arguments, assuming we work with a fixed covering. It builds on
`locally_finite.exists_forall_eventually_of_index_type`.

From `inductive_construction` alone we deduce `inductive_htpy_construction` which builds a homotopy
in a similar context. This is meant to be used to go from Chapter 2 to Chapter 3.

Combining `inductive_construction` with an argument using local existence and exhaustions, we
get `inductive_construction_of_loc` building a function from local existence and patching
assumptions. It also has a version `relative_inductive_construction_of_loc` which does this
relative to a closed set. This is used for `exists_surrounding_loops`.

This file also contains supporting lemmas about `index_type`. A short term goal will be to
get rid of the `indexing` abstraction and do everything in terms of `index_type`, unless
`indexing` makes those supporting lemmas really cleaner to prove.
-/


section inductive_construction
open order fin

lemma index_type.tendsto_coe_at_top (N : ℕ) : tendsto (coe : ℕ → index_type N) at_top at_top :=
tendsto_at_top_at_top.mpr
  (λ i, ⟨indexing.to_nat i, λ n hn,(indexing.from_to i) ▸ indexing.coe_mono hn⟩)

def index_type.to_nat {N} (i : index_type N) : ℕ := indexing.to_nat i

lemma index_type.zero_le {N} (i : index_type N) : 0 ≤ i :=
by { cases N; dsimp at *; simp }

instance {N : ℕ} : succ_order (index_type N) :=
by { cases N, { exact nat.succ_order }, exact fin.succ_order }

def index_type.succ {N : ℕ} : index_type N → index_type N :=
order.succ

lemma index_type.succ_cast_succ {N} (i : fin N) : @index_type.succ (N+1) i.cast_succ = i.succ :=
begin
  refine (succ_apply _).trans _,
  rw [if_pos (cast_succ_lt_last i), fin.coe_succ_eq_succ, fin.succ_inj],
end

lemma index_type.succ_eq {N} (i : index_type N) : i.succ = i ↔ is_max i :=
order.succ_eq_iff_is_max

lemma index_type.lt_succ  {N : ℕ} (i : index_type N) (h : ¬ is_max i) : i < i.succ :=
order.lt_succ_of_not_is_max h

lemma index_type.le_max {N : ℕ} {i : index_type N} (h : is_max i) (j) : j ≤ i :=
h.is_top j

lemma index_type.le_of_lt_succ  {N : ℕ} (i : index_type N) {j : index_type N} (h : i < j.succ) :
  i ≤ j :=
le_of_lt_succ h

lemma index_type.exists_cast_succ_eq {N : ℕ} (i : fin (N+1)) (hi : ¬ is_max i) :
  ∃ i' : fin N, i'.cast_succ = i :=
begin
  revert hi,
  refine fin.last_cases _ _ i,
  { intro hi, apply hi.elim, intros i hi, exact le_last i },
  intros i hi,
  exact ⟨_, rfl⟩
end

lemma index_type.to_nat_succ {N : ℕ} (i : index_type N) (hi : ¬ is_max i) :
  i.succ.to_nat = i.to_nat + 1 :=
begin
  cases N, { refl },
  rcases i.exists_cast_succ_eq hi with ⟨i, rfl⟩,
  rw [index_type.succ_cast_succ],
  exact coe_succ i
end

@[simp] lemma index_type.not_is_max (n : index_type 0) : ¬ is_max n :=
not_is_max_of_lt $ nat.lt_succ_self n

@[elab_as_eliminator]
lemma index_type.induction_from {N : ℕ} {P : index_type N → Prop} {i₀ : index_type N} (h₀ : P i₀)
  (ih : ∀ i ≥ i₀, ¬ is_max i → P i → P i.succ) : ∀ i ≥ i₀, P i :=
begin
  cases N,
  { intros i h,
    induction h with i hi₀i hi ih,
    { exact h₀ },
    exact ih i hi₀i (index_type.not_is_max i) hi },
  intros i,
  refine fin.induction _ _ i,
  { intro hi, convert h₀, exact (hi.le.antisymm $ fin.zero_le _).symm },
  { intros i hi hi₀i,
    rcases hi₀i.le.eq_or_lt with rfl|hi₀i,
    { exact h₀ },
    rw [← index_type.succ_cast_succ],
    refine ih _ _ _ _,
    { rwa [ge_iff_le, le_cast_succ_iff] },
    { exact not_is_max_of_lt (cast_succ_lt_succ i) },
    { apply hi, rwa [ge_iff_le, le_cast_succ_iff] }
    }
end

@[elab_as_eliminator]
lemma index_type.induction {N : ℕ} {P : index_type N → Prop} (h₀ : P 0)
  (ih : ∀ i, ¬ is_max i → P i → P i.succ) : ∀ i, P i :=
λ i, index_type.induction_from h₀ (λ i _, ih i) i i.zero_le

-- We make `P` and `Q` explicit to help the elaborator when applying the lemma
-- (elab_as_eliminator isn't enough).
lemma index_type.exists_by_induction {N : ℕ} {α : Type*} (P : index_type N → α → Prop)
  (Q : index_type N → α → α → Prop)
  (h₀ : ∃ a, P 0 a)
  (ih : ∀ n a, P n a → ¬ is_max n → ∃ a', P n.succ a' ∧ Q n a a') :
  ∃ f : index_type N → α, ∀ n, P n (f n) ∧ (¬ is_max n → Q n (f n) (f n.succ)) :=
begin
  revert P Q h₀ ih,
  cases N,
  { intros P Q h₀ ih,
    rcases exists_by_induction' P Q h₀ _ with ⟨f, hf⟩,
    exact ⟨f, λ n, ⟨(hf n).1, λ _, (hf n).2⟩⟩,
    simpa using ih },
  { --dsimp only [index_type, index_type.succ],
    intros P Q h₀ ih,
    choose f₀ hf₀ using h₀,
    choose! F hF hF' using ih,
    let G := λ i : fin N, F i.cast_succ,
    let f : fin (N + 1) → α := λ i, fin.induction f₀ G i,
    have key : ∀ i, P i (f i),
    { refine λ i, fin.induction hf₀ _ i,
      intros i hi,
      simp_rw [f, induction_succ, ← index_type.succ_cast_succ],
      apply hF _ _ hi,
      exact not_is_max_of_lt (cast_succ_lt_succ i) },
    refine ⟨f, λ i, ⟨key i, λ hi, _⟩⟩,
    { convert hF' _ _ (key i) hi,
      rcases i.exists_cast_succ_eq hi with ⟨i, rfl⟩,
      simp_rw [index_type.succ_cast_succ, f, induction_succ] } }
end

lemma locally_finite.exists_forall_eventually_of_index_type
  {α X : Type*} [topological_space X] {N : ℕ} {f : index_type N → X → α}
  {V : index_type N → set X} (hV : locally_finite V)
  (h : ∀ n : index_type N, ¬ is_max n → ∀ x ∉ V n.succ, f n.succ x = f n x) :
  ∃ (F : X → α), ∀ (x : X), ∀ᶠ n in filter.at_top, f n =ᶠ[𝓝 x] F :=
begin
  choose U hUx hU using hV,
  choose i₀ hi₀ using λ x, (hU x).bdd_above,
  have key : ∀ {x} {n}, n ≥ i₀ x → ∀ {y}, y ∈ U x → f n y = f (i₀ x) y,
  { intros x,
    apply @index_type.induction_from N (λ i, ∀ {y}, y ∈ U x → f i y = f (i₀ x) y),
    exact λ _ _, rfl,
    intros i hi h'i ih y hy,
    rw [h i h'i, ih hy],
    intros h'y,
    replace hi₀ := mem_upper_bounds.mp (hi₀ x) i.succ ⟨y, h'y, hy⟩,
    exact lt_irrefl _ (((i.lt_succ h'i).trans_le hi₀).trans_le hi) },
  refine ⟨λ x, f (i₀ x) x, λ x, _⟩,
  change ∀ᶠ n in at_top, f n =ᶠ[𝓝 x] λ (y : X), f (i₀ y) y,
  apply (eventually_ge_at_top (i₀ x)).mono (λ n hn, _),
  apply mem_of_superset (hUx x) (λ y hy, _),
  change f n y = f (i₀ y) y,
  calc f n y = f (i₀ x) y : key hn hy
  ... = f (max (i₀ x) (i₀ y)) y : (key (le_max_left _ _) hy).symm
  ... = f (i₀ y) y : key (le_max_right _ _) (mem_of_mem_nhds $ hUx y)
end

local notation `𝓘` := index_type

lemma inductive_construction {X Y : Type*} [topological_space X]
  {N : ℕ} {U : index_type N → set X}
  (P₀ : Π x : X, germ (𝓝 x) Y → Prop) (P₁ : Π i : index_type N, Π x : X, germ (𝓝 x) Y → Prop)
  (P₂ : index_type N → (X → Y) → Prop)
  (U_fin : locally_finite U)
  (init : ∃ f : X → Y, (∀ x, P₀ x f) ∧ P₂ 0 f)
  (ind : ∀ (i : index_type N) (f : X → Y), (∀ x, P₀ x f) → (P₂ i f) → (∀ j < i, ∀ x, P₁ j x f) →
    ∃ f' : X → Y, (∀ x, P₀ x f') ∧ (¬ is_max i → P₂ i.succ f') ∧ (∀ j ≤ i, ∀ x, P₁ j x f') ∧ ∀ x ∉ U i, f' x = f x) :
    ∃ f : X → Y, (∀ x, P₀ x f) ∧ ∀ j, ∀ x, P₁ j x f :=
begin
  let P : 𝓘 N → (X → Y) → Prop :=
    λ n f, (∀ x, P₀ x f) ∧ (¬ is_max n → P₂ n.succ f) ∧ ∀ j ≤ n, ∀ x, P₁ j x f,
  let Q : 𝓘 N → (X → Y) → (X → Y) → Prop :=
    λ n f f', ∀ x ∉ U n.succ, f' x = f x,
  obtain ⟨f, hf⟩ : ∃ f : 𝓘 N → X → Y, ∀ n, P n (f n) ∧ (¬ is_max n → Q n (f n) (f n.succ)),
  { apply index_type.exists_by_induction,
    { rcases init with ⟨f₀, h₀f₀, h₁f₀⟩,
      rcases ind 0 f₀ h₀f₀ h₁f₀ (by simp [index_type.not_lt_zero]) with ⟨f', h₀f', h₂f', h₁f', hf'⟩,
      exact ⟨f', h₀f', h₂f', h₁f'⟩ },
    { rintros n f ⟨h₀f, h₂f, h₁f⟩ hn,
      by_cases hn : is_max n,
      { simp only [P, Q, n.succ_eq.mpr hn],
        exact ⟨f, ⟨h₀f, λ hn', (hn' hn).elim, h₁f⟩, λ _ _, rfl⟩ },
      rcases ind _ f h₀f (h₂f hn) (λ j hj, h₁f _ $ j.le_of_lt_succ hj) with ⟨f', h₀f', h₂f', h₁f', hf'⟩,
      exact ⟨f', ⟨h₀f', h₂f', h₁f'⟩, hf'⟩  } },
  dsimp only [P, Q] at hf,
  simp only [forall_and_distrib] at hf,
  rcases hf with ⟨⟨h₀f, h₂f, h₁f⟩, hfU⟩,
  rcases U_fin.exists_forall_eventually_of_index_type hfU with ⟨F, hF⟩,
  refine ⟨F, λ x, _, λ j, _⟩,
  { rcases (hF x).exists with ⟨n₀, hn₀⟩,
    simp only [germ.coe_eq.mpr hn₀.symm, h₀f n₀ x] },
  intros x,
  rcases ((hF x).and $ eventually_ge_at_top j).exists with ⟨n₀, hn₀, hn₀'⟩,
  exact eventually.germ_congr (h₁f _ _ hn₀' x) hn₀.symm
end

/-- We are given a suitably nice extended metric space `X` and three local constraints `P₀`,`P₀'`
and `P₁` on maps from `X` to some type `Y`. All maps entering the discussion are required to
statisfy `P₀` everywhere. The goal is to turn a map `f₀` satisfying `P₁` near a compact set `K` into
one satisfying everywhere without changing `f₀` near `K`. The assumptions are:
* For every `x` in `X` there is a map which satisfies `P₁` near `x`
* One can patch two maps `f₁ f₂` satisfying `P₁` on open sets `U₁` and `U₂` respectively
  and such that `f₁` satisfies `P₀'` everywhere into a map satisfying `P₁` on `K₁ ∪ K₂` for any
  compact sets `Kᵢ ⊆ Uᵢ` and `P₀'` everywhere. -/
lemma inductive_construction_of_loc {X Y : Type*} [emetric_space X] [locally_compact_space X]
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
    ⟨K, (U : index_type 0 → set X) , K_cpct, U_op, hU, hKU, U_loc, hK⟩,
  have ind' : ∀ (i : 𝓘 0) (f : X → Y), (∀ x, P₀ x f ∧ P₀' x f) →
    (∀ j < i, ∀ x, restrict_germ_predicate P₁ (K j) x ↑f) →
    ∃ f' : X → Y, (∀ (x : X), P₀ x ↑f' ∧ P₀' x ↑f') ∧
                  (∀ j ≤ i, ∀ x, restrict_germ_predicate P₁ (K j) x f') ∧ ∀ x ∉ U i, f' x = f x,
  { simp_rw [forall_restrict_germ_predicate_iff, ← eventually_nhds_set_Union₂],
    rintros (i : ℕ) f h₀f h₁f,
    have cpct : is_closed ⋃ j < i, K j,
    { rw show (⋃ j < i, K j) = ⋃ j ∈ finset.range i, K j, by simp only [finset.mem_range],
      apply (finset.range i).is_closed_bUnion _ (λ j _, (K_cpct j).is_closed) },
    rcases hU i with ⟨f', h₀f', h₁f'⟩,
    rcases mem_nhds_set_iff_exists.mp h₁f with ⟨V, V_op, hKV, h₁V⟩,
    rcases ind V_op (U_op i) cpct (K_cpct i).is_closed hKV (hKU i) h₀f h₀f' h₁V h₁f' with
      ⟨F, h₀F, h₁F, hF⟩,
    simp_rw [← bUnion_le] at h₁F,
    exact ⟨F, h₀F, h₁F, λ x hx, hF.on_set x (or.inr hx)⟩ },
  have := inductive_construction (λ x φ, P₀ x φ ∧ P₀' x φ)
    (λ j : 𝓘 0, restrict_germ_predicate P₁ (K j)) (λ _ _, true) U_loc ⟨f₀, hP₀f₀, trivial⟩,
  simp only [index_type.not_is_max, not_false_iff, forall_true_left, true_and] at this,
  rcases this ind' with ⟨f, h, h'⟩,
  refine ⟨f, λ x, ⟨(h x).1, (h x).2, _⟩⟩,
  rcases mem_Union.mp (hK trivial : x ∈ ⋃ j, K j) with ⟨j, hj⟩,
  exact (h' j x hj).self_of_nhds
end

/-- We are given a suitably nice extended metric space `X` and three local constraints `P₀`,`P₀'`
and `P₁` on maps from `X` to some type `Y`. All maps entering the discussion are required to
statisfy `P₀` everywhere. The goal is to turn a map `f₀` satisfying `P₁` near a compact set `K` into
one satisfying everywhere without changing `f₀` near `K`. The assumptions are:
* For every `x` in `X` there is a map which satisfies `P₁` near `x`
* One can patch two maps `f₁ f₂` satisfying `P₁` on open sets `U₁` and `U₂` respectively
  into a map satisfying `P₁` on `K₁ ∪ K₂` for any compact sets `Kᵢ ⊆ Uᵢ`.
This is deduced this version from the version where `K` is empty but adding some `P'₀`, see
`inductive_construction_of_loc`. -/
lemma relative_inductive_construction_of_loc {X Y : Type*} [emetric_space X] [locally_compact_space X]
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
    rcases (has_basis_nhds_set K).mem_iff.mp (hP₁f₀.germ_congr_set h₀'f₁) with ⟨U, ⟨U_op, hKU⟩, hU⟩,
    rcases ind (U_op.union U₁_op) U₂_op (hK.union K₁_cpct) K₂_cpct (union_subset_union hKU hK₁U₁)
      hK₂U₂ h₀f₁ hf₂ (λ x hx, hx.elim (λ hx, hU hx) (λ hx, hf₁U₁ x hx)) hf₂U₂ with ⟨f, h₀f, hf, h'f⟩,
    rw [union_assoc, eventually_nhds_set_union] at hf h'f,
    exact ⟨f, λ x, ⟨h₀f x, restrict_germ_predicate_congr (hf₁ x).2 h'f.1⟩, hf.2, h'f.2⟩ },
  rcases inductive_construction_of_loc P₀ P₀' P₁ hf₀ loc ind' with ⟨f, hf⟩,
  simp only [forall_and_distrib, forall_restrict_germ_predicate_iff ] at hf ⊢,
  exact ⟨f, ⟨hf.1, hf.2.2⟩, hf.2.1⟩
end

end inductive_construction

section htpy

private noncomputable def T : ℕ → ℝ := λ n, nat.rec 0 (λ k x, x + 1/(2 : ℝ)^(k+1)) n

open_locale big_operators

-- Note this is more painful than Patrick hoped for. Maybe this should be the definition of T.
private lemma T_eq (n : ℕ) : T n = 1- (1/(2: ℝ))^n :=
begin
  have : T n = ∑ k in finset.range n, 1/(2: ℝ)^(k+1),
  { induction n with n hn,
    { simp only [T, finset.range_zero, finset.sum_empty] },
    change T n + _ = _,
    rw [hn, finset.sum_range_succ] },
  simp_rw [this, ← one_div_pow, pow_succ, ← finset.mul_sum, geom_sum_eq (by norm_num : 1/(2:ℝ) ≠ 1) n],
  field_simp,
  norm_num,
  apply div_eq_of_eq_mul,
  apply neg_ne_zero.mpr,
  apply ne_of_gt,
  positivity,
  ring
end

private lemma T_lt (n : ℕ) : T n < 1 :=
begin
  rw T_eq,
  have : (0 : ℝ) < (1 / 2) ^ n, by positivity,
  linarith
end

private lemma T_lt_succ (n : ℕ) : T n < T (n+1) :=
lt_add_of_le_of_pos le_rfl (one_div_pos.mpr (pow_pos zero_lt_two _))

private lemma T_le_succ (n : ℕ) : T n ≤ T (n+1) := (T_lt_succ n).le

private lemma T_succ_sub (n : ℕ) : T (n+1) - T n = 1/2^(n+1) :=
begin
  change T n + _ - T n = _,
  simp
end

private lemma mul_T_succ_sub (n : ℕ) : 2^(n+1)*(T (n+1) - T n) = 1 :=
begin
  rw T_succ_sub,
  field_simp
end

private lemma T_one : T 1 = 1/2 :=
by simp [T]

private lemma T_nonneg (n : ℕ) : 0 ≤ T n :=
begin
  rw [T_eq],
  have : (1 / (2 : ℝ))^n ≤ 1,
  apply pow_le_one ; norm_num,
  linarith,
end

private lemma not_T_succ_le (n : ℕ) : ¬ T (n + 1) ≤ 0 :=
begin
  rw [T_eq, not_le],
  have : (1 / (2 : ℝ)) ^ (n + 1) < 1,
  apply pow_lt_one ; norm_num,
  linarith,
end

lemma inductive_htpy_construction {X Y : Type*} [topological_space X]
  {N : ℕ} {U K : index_type N → set X}
  (P₀ P₁ : Π x : X, germ (𝓝 x) Y → Prop) (P₂ : Π p : ℝ × X, germ (𝓝 p) Y → Prop)
  (hP₂ : ∀ a b (p : ℝ × X) (f : ℝ × X → Y), P₂ (a*p.1+b, p.2) f → P₂ p (λ p : ℝ × X, f (a*p.1+b, p.2)))
  (U_fin : locally_finite U) (K_cover : (⋃ i, K i) = univ)
  {f₀ : X → Y} (init : ∀ x, P₀ x f₀)
  (init' : ∀ p, P₂ p (λ p : ℝ × X, f₀ p.2)) -- Not in the original version
  (ind : ∀ (i : index_type N) (f : X → Y), (∀ x, P₀ x f) → (∀ᶠ x near ⋃ j < i, K j, P₁ x f) →
    ∃ F : ℝ → X → Y, (∀ t, ∀ x, P₀ x $ F t) ∧ (∀ᶠ x near ⋃ j ≤ i, K j, P₁ x $ F 1) ∧
                     (∀ p, P₂ p ↿F) ∧ (∀ t, ∀ x ∉ U i, F t x = f x) ∧
                     (∀ᶠ t near Iic 0, F t = f) ∧ (∀ᶠ t near Ici 1, F t = F 1)) :
  ∃ F : ℝ → X → Y, F 0 = f₀ ∧ (∀ t x, P₀ x (F t)) ∧ (∀ x, P₁ x (F 1)) ∧ (∀ p, P₂ p ↿F) :=
begin
  let PP₀ : Π p : ℝ × X, germ (𝓝 p) Y → Prop := λ p φ, P₀ p.2 φ.slice_right ∧
    (p.1 = 0 → φ.value = f₀ p.2) ∧ P₂ p φ,
  let PP₁ : Π i : index_type N, Π p : ℝ × X, germ (𝓝 p) Y → Prop := λ i p φ,
    p.1 = 1 → restrict_germ_predicate P₁ (K i) p.2 φ.slice_right,
  let PP₂ : index_type N → (ℝ × X → Y) → Prop :=
    λ i f, ∀ x, ∀ t ≥ T i.to_nat, f (t, x) = f (T i.to_nat, x),
  have hPP₀ : ∀ (p : ℝ × X), PP₀ p (λ (p : ℝ × X), f₀ p.2),
  { rintros ⟨t, x⟩,
    exact ⟨init x, λ h, rfl, init' _⟩ },
  have ind' : ∀ i (f : ℝ × X → Y), (∀ p, PP₀ p f) → PP₂ i f → (∀ j < i, ∀ p, PP₁ j p f) →
    ∃ f' : ℝ × X → Y, (∀ p, PP₀ p f') ∧ (¬ is_max i → PP₂ i.succ f') ∧ (∀ j ≤ i, ∀ p, PP₁ j p f') ∧
                      ∀ p ∉ Ici (T i.to_nat) ×ˢ U i, f' p = f p,
  { rintros i F h₀F h₂F h₁F,
    replace h₁F : ∀ᶠ (x : X) near ⋃ j < i, K j, P₁ x (λ x, F (T i.to_nat, x)),
    { rw eventually_nhds_set_Union₂,
      intros j hj,
      have : ∀ x : X, restrict_germ_predicate P₁ (K j) x (λ x', F (1, x')),
        from λ x, h₁F j hj (1, x) rfl,
      apply (forall_restrict_germ_predicate_iff.mp this).germ_congr_set,
      apply eventually_of_forall (λ x, (_ : F (T i.to_nat, x) = F (1, x))),
      rw h₂F _ _ (T_lt _).le },
    rcases ind i (λ x, F (T i.to_nat, x)) (λ x, (h₀F (_, x)).1) h₁F with
      ⟨F', h₀F', h₁F', h₂F', hUF', hpast_F', hfutur_F'⟩ ; clear ind,
    let F'' : ℝ × X → Y :=  λ p : ℝ × X,
        if p.1 ≤ T i.to_nat then F p else F' (2^(i.to_nat+1)*(p.1 - T i.to_nat)) p.2,
    have loc₁ : ∀ p : ℝ × X, p.1 ≤ T i.to_nat → (F'' : germ (𝓝 p) Y)  = F,
    { dsimp only [PP₂] at h₂F,
      rintros ⟨t, x⟩ (ht : t ≤ _),
      rcases eq_or_lt_of_le ht with rfl|ht,
      { apply quotient.sound,
        replace hpast_F' : ↿F' =ᶠ[𝓝 (0, x)] λ q : ℝ × X, F (T i.to_nat, q.2),
        { have : 𝓝 (0 : ℝ) ≤ 𝓝ˢ (Iic 0),
          { exact nhds_le_nhds_set right_mem_Iic },
          apply mem_of_superset (prod_mem_nhds (hpast_F'.filter_mono this) univ_mem),
          rintros ⟨t', x'⟩ ⟨ht', hx'⟩,
          exact (congr_fun ht' x' : _) },
        have lim : tendsto (λ (x : ℝ × X), (2 ^ (i.to_nat + 1) * (x.1 - T i.to_nat), x.2)) (𝓝 (T i.to_nat, x)) (𝓝 (0, x)),
        { rw [nhds_prod_eq, nhds_prod_eq],
          have limt : tendsto (λ t, 2 ^ (i.to_nat + 1) * (t - T i.to_nat)) (𝓝 $ T i.to_nat) (𝓝 0),
          { rw [show (0 : ℝ) = 2^(i.to_nat + 1)*(T i.to_nat - T i.to_nat), by simp],
            apply tendsto.const_mul,
            exact tendsto_id.sub_const _ },
          exact limt.prod_map tendsto_id },
        apply eventually.mono (hpast_F'.comp_fun lim),
        dsimp [F''],
        rintros ⟨t, x⟩ h',
        split_ifs,
        { refl },
        { push_neg at h,
          change ↿F' (2 ^ (i.to_nat + 1) * (t - T i.to_nat), x) = _,
          rw [h', h₂F x t h.le] } },
      { have hp : ∀ᶠ p : ℝ × X in 𝓝 (t, x), p.1 ≤ T i.to_nat,
        { convert (prod_mem_nhds (Iic_mem_nhds ht) univ_mem) using 1,
          simp },
        apply quotient.sound,
        exact hp.mono (λ p hp, if_pos hp) }, },
    have loc₂ : ∀ p : ℝ × X, p.1 > T i.to_nat →
      (F'' : germ (𝓝 p) Y)  = λ p : ℝ × X, F' (2^(i.to_nat+1)*(p.1 - T i.to_nat)) p.2,
    { rintros ⟨t, x⟩ (ht : t > _),
      apply quotient.sound,
      have hp : ∀ᶠ p : ℝ × X in 𝓝 (t, x), ¬ p.1 ≤ T i.to_nat,
      { apply mem_of_superset (prod_mem_nhds (Ioi_mem_nhds ht) univ_mem),
        rintros ⟨t', x'⟩ ⟨ht', hx'⟩,
        simpa using ht' },
      apply hp.mono (λ q hq, _),
      exact if_neg hq },
    refine ⟨F'', _, _, _,_ ⟩,
    { rintros p,
      by_cases ht : p.1 ≤ T i.to_nat,
      { rw loc₁ _ ht,
        apply h₀F },
      { push_neg at ht,
        cases p with t x,
        rw loc₂ _ ht,
        refine ⟨h₀F' (2 ^ (i.to_nat + 1) * (t - T i.to_nat)) x, _, _⟩,
        { rintro (rfl : t = 0),
          exact (lt_irrefl _ ((T_nonneg i.to_nat).trans_lt ht)).elim },
        { simpa only [mul_sub, neg_mul] using hP₂ (2^(i.to_nat+1)) (-2^(i.to_nat+1)*T i.to_nat)
              (t, x) ↿F' (h₂F' _) } } },
    { intros hi x t ht,
      rw i.to_nat_succ hi at ht ⊢,
      have h₂t : ¬ t ≤ T i.to_nat,
      { push_neg,
        exact (T_lt_succ i.to_nat).trans_le ht },
      dsimp only [F''],
      rw [if_neg h₂t, if_neg],
      { rw [hfutur_F'.on_set, mul_T_succ_sub],
        conv { rw mem_Ici, congr, rw ← mul_T_succ_sub i.to_nat },
        exact mul_le_mul_of_nonneg_left (sub_le_sub_right ht _) (pow_nonneg zero_le_two _) },
      { push_neg,
        apply T_lt_succ } },
    { rintros j hj ⟨t, x⟩ (rfl : t = 1),
      replace h₁F' := eventually_nhds_set_Union₂.mp h₁F' j hj,
      rw loc₂ (1, x) (T_lt i.to_nat),
      revert x,
      change ∀ x : X, restrict_germ_predicate P₁ (K j) x (λ x' : X, F' (2 ^ (i.to_nat + 1) * (1 - T i.to_nat)) x'),
      rw forall_restrict_germ_predicate_iff,
      apply h₁F'.germ_congr_set,
      apply eventually_of_forall _,
      apply congr_fun (hfutur_F'.on_set _ _),
      conv { congr, skip, rw ← mul_T_succ_sub i.to_nat },
      exact mul_le_mul_of_nonneg_left (sub_le_sub_right (T_lt _).le _) (pow_nonneg zero_le_two _) },
    { rintros ⟨t, x⟩ htx,
      simp only [prod_mk_mem_set_prod_eq, mem_Ici, not_and_distrib, not_le] at htx,
      cases htx with ht hx,
      { change (↑F'' : germ (𝓝 (t, x)) Y).value = (↑F : germ (𝓝 (t, x)) Y).value,
        rw loc₁ (t, x) ht.le },
      { dsimp only [F''],
        split_ifs with ht ht,
        { refl },
        { rw hUF' _ x hx,
          push_neg at ht,
          rw h₂F x _ ht.le } } } },
  rcases inductive_construction PP₀ PP₁ PP₂ (U_fin.prod_left $ λ i, Ici (T $ indexing.to_nat i))
    ⟨λ p, f₀ p.2, hPP₀, λ x t ht, rfl⟩ ind' with ⟨F, hF,h'F ⟩, clear ind ind' hPP₀,
  refine ⟨curry F, _, _, _, _⟩,
  { exact funext (λ x, (hF (0, x)).2.1 rfl) },
  { exact λ t x, (hF (t, x)).1 },
  { intros x,
    obtain ⟨j, hj⟩ : ∃ j, x ∈ K j, by simpa using (by simp [K_cover] : x ∈ ⋃ j, K j),
    exact (h'F j (1, x) rfl hj).self_of_nhds },
  { intros p,
    convert (hF p).2.2 using 2,
    exact uncurry_curry F },
end
end htpy
