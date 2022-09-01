import tactic.linarith
import algebra.order.with_zero
import topology.locally_finite

import to_mathlib.set_theory.cardinal.basic

/-!
# Indexing types

This is a stupid file introducing a type class for types that will index
locally finite covers of (paracompact) manifolds without having
to discuss according to compactness. The only intended instances
are `ℕ` and `fin (n+1)`.

It also includes a lemma about locally finite cover that doesn't require an indexing
index type but will be used with one.
-/

class indexing (α : Type*) [linear_order α] :=
(from_nat : ℕ → α)
(to_nat : α → ℕ)
(mono_from : monotone from_nat)
(from_to : ∀ a, from_nat (to_nat a) = a)

instance indexing.has_coe (α : Type*) [linear_order α] [indexing α] : has_coe ℕ α :=
⟨indexing.from_nat⟩

instance indexing.nonempty (α : Type*) [linear_order α] [indexing α] : nonempty α :=
⟨indexing.from_nat 0⟩

instance : indexing ℕ :=
{ from_nat := id,
  to_nat := id,
  mono_from := monotone_id,
  from_to := λ n, rfl }

instance (n : ℕ) : indexing (fin $ n + 1) :=
{ from_nat := λ k, if h : k < n + 1 then ⟨k, h⟩ else fin.last n,
  to_nat := coe,
  mono_from := λ k l hkl, begin
    dsimp [fin.of_nat],
    split_ifs ; try { simp [fin.le_last] };
    linarith,
  end,
  from_to := begin
    rintros ⟨k, hk⟩,
    erw dif_pos hk,
    refl
  end }

open_locale topological_space

lemma foo {X : Type*} [topological_space X] {ι : Type*} [linear_order ι] [nonempty ι]
  {s : ι → set X} (h : locally_finite s) :
  ∃ ind : X → ι, ∃ U : X → set X, ∀ x, U x ∈ 𝓝 x ∧ ∀ i > ind x, s i ∩ U x = ∅ :=
begin
  choose V V_in hV using h,
  choose ind hind using (λ x, (hV x).bdd_above),
  refine ⟨ind, V, λ  x, ⟨V_in x, _⟩⟩,
  intros i hi,
  by_contra,
  exact lt_irrefl i (gt_of_gt_of_ge hi $ hind x (set.ne_empty_iff_nonempty.mp h))
end

/-- Our model indexing type depending on `n : ℕ` is `ℕ` if `n = 0` and `fin n` otherwise-/
def index_type (n : ℕ) : Type :=
nat.cases_on n ℕ (λ k, fin $ k + 1)

@[simp] lemma index_type_zero : index_type 0 = ℕ := rfl

@[simp] lemma index_type_succ (n : ℕ) : index_type (n + 1) = fin (n + 1) := rfl

@[simp] lemma index_type_of_zero_lt {n : ℕ} (h : 0 < n) : index_type n = fin n :=
by rw [← nat.succ_pred_eq_of_pos h, index_type_succ]

instance (n : ℕ) : linear_order (index_type n) :=
nat.cases_on n nat.linear_order (λ _, fin.linear_order)

instance (n : ℕ) : indexing (index_type n) :=
nat.cases_on n nat.indexing (λ _, fin.indexing _)

def index_from_nat (N n : ℕ) : index_type N := indexing.from_nat n

instance (N : ℕ) : has_zero (index_type N) := sorry

lemma index_from_nat_zero (N : ℕ) : index_from_nat N 0 = 0 :=
sorry

def index_type_encodable : Π n : ℕ, encodable (index_type n)
| 0 := nat.encodable
| (n + 1) := fin.encodable (n + 1)

lemma set.countable_iff_exists_nonempty_index_type_equiv
  {α : Type*} {s : set α} (hne : s.nonempty) :
  s.countable ↔ ∃ n, nonempty (index_type n ≃ s) :=
begin
  -- Huge golfing opportunity.
  cases @set.finite_or_infinite _ s,
  { refine ⟨λ hh, ⟨h.to_finset.card, _⟩, λ _, h.countable⟩,
    have : 0 < h.to_finset.card,
    { rw finset.card_pos, exact (set.finite.nonempty_to_finset h).mpr hne},
    simp only [this, index_type_of_zero_lt],
    have e₁ := fintype.equiv_fin h.to_finset,
    rw [fintype.card_coe, h.coe_sort_to_finset] at e₁,
    exact ⟨e₁.symm⟩, },
  { refine ⟨λ hh, ⟨0, _⟩, _⟩,
    { simp only [index_type_zero],
      obtain ⟨_i⟩ := set.countable_infinite_iff_nonempty_denumerable.mp ⟨hh, h⟩,
      haveI := _i,
      exact ⟨(denumerable.eqv s).symm⟩, },
    { rintros ⟨n, ⟨fn⟩⟩,
      have hn : n = 0,
      { by_contra hn,
        replace hn : 0 < n := zero_lt_iff.mpr hn,
        simp only [hn, index_type_of_zero_lt] at fn,
        exact set.not_infinite.mpr ⟨fintype.of_equiv (fin n) fn⟩ h, },
      simp only [hn, index_type_zero] at fn,
      exact set.countable_iff_exists_injective.mpr ⟨fn.symm, fn.symm.injective⟩, }, },
end

open filter

/-
Old statement assumed h : ∀ n, {x : X | f (n + 1) x ≠ f n x} ⊆ V (n + 1 : ℕ)
which gives the new style assumption by:
  replace h : ∀ n : ℕ, ∀ x ∉ V (n + 1 : ℕ), f (n+1) x = f n x,
  { intros n x hx,
    contrapose hx,
    simp [h n hx] },
-/

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
