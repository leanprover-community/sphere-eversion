import tactic.linarith
import algebra.order.with_zero
import topology.locally_finite
import data.fin.interval
import data.fin.succ_pred

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

open set

class indexing (α : Type*) [linear_order α] :=
(from_nat : ℕ → α)
(to_nat : α → ℕ)
(mono_from : monotone from_nat)
(from_to : ∀ a, from_nat (to_nat a) = a)

instance indexing.has_coe (α : Type*) [linear_order α] [indexing α] : has_coe ℕ α :=
⟨indexing.from_nat⟩

@[simp]
lemma indexing.coe_to {α : Type*} [linear_order α] [indexing α] (i : α) :
  ((indexing.to_nat i) : α) = i :=
indexing.from_to i

lemma indexing.coe_mono {α : Type*} [linear_order α] [indexing α] {i j : ℕ} (h : i ≤ j) :
  (i : α) ≤ j :=
indexing.mono_from h

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

instance (n : ℕ) : locally_finite_order (index_type n) :=
nat.cases_on n nat.locally_finite_order (λ _, fin.locally_finite_order _)

instance (n : ℕ) : order_bot (index_type n) :=
nat.cases_on n nat.order_bot (λ k, show order_bot $ fin (k + 1), by apply_instance)

instance (n : ℕ) : succ_order (index_type n) :=
nat.cases_on n nat.succ_order (λ k, fin.succ_order)

def index_from_nat (N n : ℕ) : index_type N := indexing.from_nat n

instance (N : ℕ) : has_zero (index_type N) := ⟨indexing.from_nat 0⟩

lemma index_from_nat_zero (N : ℕ) : index_from_nat N 0 = 0 :=
rfl

protected lemma index_type.Iic_zero (n : ℕ) : Iic (0 : index_type n) = {0} :=
nat.cases_on n (by { ext n, simp [@le_zero_iff ℕ] }) (λ k, by { ext n, simp })

@[simp] lemma fin.coe_order_succ {n : ℕ} (a : fin (n+1)) :
  ((order.succ a : fin _) : ℕ) = if (a : ℕ) < n then a + 1 else a :=
begin
  simp_rw [order.succ, fin.succ_eq],
  split_ifs,
  { simp_rw [fin.coe_add_one_of_lt h] },
  { refl }
end

@[simp] lemma fin.coe_order_succ_mk {n m : ℕ} (h : m < n + 1) :
  ((order.succ ⟨m, h⟩ : fin _) : ℕ) = if m < n then m + 1 else m := fin.coe_order_succ _

protected lemma index_from_nat_succ (N m : ℕ) : index_from_nat N (m + 1) =
  order.succ (index_from_nat N m) :=
begin
  refine nat.cases_on N rfl (λ n, _),
  dsimp only [index_from_nat, index_type, index_type.indexing, fin.indexing, index_type.succ_order],
  ext,
  split_ifs with h h' h',
  { rw [fin.coe_order_succ_mk, if_pos (nat.lt_of_succ_lt_succ h)], refl },
  { linarith },
  { obtain rfl : m = n :=
      le_antisymm (nat.le_of_lt_succ h') (nat.le_of_succ_le_succ $ le_of_not_lt h),
    rw [fin.coe_order_succ_mk, if_neg (lt_irrefl _)], refl },
  { rw [fin.coe_order_succ, fin.coe_last, if_neg (lt_irrefl _)] }
end

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

lemma index_type.lt_or_eq_succ (N n : ℕ) :
  (n : index_type N) < (n+1 : ℕ) ∨ (n : index_type N) = (n+1 : ℕ) :=
begin
  rw or_comm,
  exact eq_or_lt_of_le (indexing.mono_from n.le_succ)
end

lemma index_type.le_or_lt_succ {N n : ℕ} (hn : (n : index_type N) < (n+1 : ℕ)) (j : index_type N) :
  j ≤ n ↔ j < (n + 1 : ℕ) :=
begin
  cases N, { exact nat.lt_succ_iff.symm, },
  refine ⟨λ h, lt_of_le_of_lt h hn, λ h, _⟩,
  clear hn,
  obtain ⟨j, hj⟩ := j,
  change _ ≤ indexing.from_nat n,
  change _ < indexing.from_nat (n + 1) at h,
  unfold indexing.from_nat at ⊢ h,
  rcases lt_trichotomy N n with hNn | rfl | hNn,
  { replace hNn : ¬ (n < N + 1) := by simpa using nat.succ_le_iff.mpr hNn,
    simp only [hNn, not_false_iff, dif_neg],
    exact fin.le_last _ },
  { simpa using nat.lt_succ_iff.mp hj },
  { simp only [hNn, add_lt_add_iff_right, dif_pos, fin.mk_lt_mk] at h,
    simpa only [nat.lt.step hNn, dif_pos, fin.mk_le_mk] using nat.lt_succ_iff.mp h }
end

lemma index_type.tendsto_coe_at_top (N : ℕ) : tendsto (coe : ℕ → index_type N) at_top at_top :=
tendsto_at_top_at_top.mpr
  (λ i, ⟨indexing.to_nat i, λ n hn,(indexing.from_to i) ▸ indexing.coe_mono hn⟩)

lemma index_type.not_lt_zero {N : ℕ} (j : index_type N) : ¬ (j < 0) :=
nat.cases_on N nat.not_lt_zero (λ n, fin.not_lt_zero) j
