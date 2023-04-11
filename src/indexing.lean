import tactic.linarith
import algebra.order.with_zero
import topology.locally_finite
import data.fin.interval
import data.fin.succ_pred

import to_mathlib.data.nat.basic
import to_mathlib.set_theory.cardinal.basic

/-!
# Indexing types

This file introduces `index_type : ℕ → Type` such that `index_type 0 = ℕ` and
`index_type (N+1) = fin (N+1)`. Each `index_type N` has a total order and and inductive principle
together with supporting lemmas.
-/

open set

/-- Our model indexing type depending on `n : ℕ` is `ℕ` if `n = 0` and `fin n` otherwise-/
def index_type (n : ℕ) : Type :=
nat.cases_on n ℕ (λ k, fin $ k + 1)

def index_type.from_nat : Π {N : ℕ}, ℕ → index_type N
| 0 := id
| (N+1) := (coe : ℕ → fin (N+1))

def index_type.to_nat : Π {N}, index_type N → ℕ
| 0 := id
| (N+1) := fin.val

@[simp] lemma index_type_zero : index_type 0 = ℕ := rfl

@[simp] lemma index_type_succ (n : ℕ) : index_type (n + 1) = fin (n + 1) := rfl

@[simp] lemma index_type_of_zero_lt {n : ℕ} (h : 0 < n) : index_type n = fin n :=
by rw [← nat.succ_pred_eq_of_pos h, index_type_succ]

instance (n : ℕ) : linear_order (index_type n) :=
nat.cases_on n nat.linear_order (λ _, fin.linear_order)

instance (n : ℕ) : locally_finite_order (index_type n) :=
nat.cases_on n nat.locally_finite_order (λ _, fin.locally_finite_order _)

instance (n : ℕ) : order_bot (index_type n) :=
nat.cases_on n nat.order_bot (λ k, show order_bot $ fin (k + 1), by apply_instance)

instance (N : ℕ) : has_zero (index_type N) := ⟨index_type.from_nat 0⟩

lemma set.countable_iff_exists_nonempty_index_type_equiv
  {α : Type*} {s : set α} (hne : s.nonempty) :
  s.countable ↔ ∃ n, nonempty (index_type n ≃ s) :=
begin
  -- Huge golfing opportunity.
  cases @set.finite_or_infinite _ s,
  { refine ⟨λ hh, ⟨h.to_finset.card, _⟩, λ _, h.countable⟩,
    have : 0 < h.to_finset.card,
    { rw finset.card_pos, exact (set.finite.to_finset_nonempty h).mpr hne},
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

lemma index_type.not_lt_zero {N : ℕ} (j : index_type N) : ¬ (j < 0) :=
nat.cases_on N nat.not_lt_zero (λ n, fin.not_lt_zero) j

open order fin

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
