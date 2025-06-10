import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Nat.SuccPred
import Mathlib.SetTheory.Cardinal.Basic
import SphereEversion.ToMathlib.Data.Nat.Basic
/-!
# Indexing types

This file introduces `IndexType : ℕ → Type` such that `IndexType 0 = ℕ` and
`IndexType (N+1) = Fin (N+1)`. Each `IndexType N` has a total order and and inductive principle
together with supporting lemmas.
-/


open Fin Set

/-- Our model indexing type depending on `n : ℕ` is `ℕ` if `n = 0` and `Fin n` otherwise -/
def IndexType (n : ℕ) : Type :=
  Nat.casesOn n ℕ fun k ↦ Fin <| k + 1

open Fin.NatCast in -- TODO: remove this, by making the cast explicit
def IndexType.fromNat : ∀ {N : ℕ}, ℕ → IndexType N
  | 0 => id
  | N + 1 => (Nat.cast : ℕ → Fin (N + 1))

def IndexType.toNat : ∀ {N}, IndexType N → ℕ
  | 0 => id
  | _ + 1 => Fin.val

@[simp]
theorem indexType_zero : IndexType 0 = ℕ :=
  rfl

@[simp]
theorem indexType_succ (n : ℕ) : IndexType (n + 1) = Fin (n + 1) :=
  rfl

@[simp]
theorem indexType_of_zero_lt {n : ℕ} (h : 0 < n) : IndexType n = Fin n := by
  rw [← Nat.succ_pred_eq_of_pos h, indexType_succ]

set_option hygiene false in
run_cmd
  for n in [`LinearOrder, `LocallyFiniteOrder, `OrderBot, `Zero, `SuccOrder].map Lean.mkIdent do
  Lean.Elab.Command.elabCommand (← `(
    instance : ∀ n, $n (IndexType n)
    | 0 => inferInstanceAs ($n ℕ)
    | (N + 1) => inferInstanceAs ($n (Fin (N + 1)))
  ))

theorem Set.countable_iff_exists_nonempty_indexType_equiv {α : Type*} {s : Set α}
    (hne : s.Nonempty) : s.Countable ↔ ∃ n, Nonempty (IndexType n ≃ s) := by
  -- Huge golfing opportunity.
  obtain (h | h) := s.finite_or_infinite
  · refine ⟨fun _ ↦ ⟨h.toFinset.card, ?_⟩, fun _ ↦ h.countable⟩
    have : 0 < h.toFinset.card := by
      rw [Finset.card_pos]
      exact (Set.Finite.toFinset_nonempty h).mpr hne
    simp only [this, indexType_of_zero_lt]
    have e₁ := Fintype.equivFin h.toFinset
    rw [Fintype.card_coe, h.coeSort_toFinset] at e₁
    exact ⟨e₁.symm⟩
  · refine ⟨fun hh ↦ ⟨0, ?_⟩, ?_⟩
    · simp only [indexType_zero]
      obtain ⟨_i⟩ := Set.countable_infinite_iff_nonempty_denumerable.mp ⟨hh, h⟩
      haveI := _i
      exact ⟨(Denumerable.eqv s).symm⟩
    · rintro ⟨n, ⟨fn⟩⟩
      have hn : n = 0 := by
        by_contra hn
        replace hn : 0 < n := Nat.pos_iff_ne_zero.mpr hn
        simp only [hn, indexType_of_zero_lt] at fn
        exact h (Finite.intro fn.symm)
      simp only [hn, indexType_zero] at fn
      exact Set.countable_iff_exists_injective.mpr ⟨fn.symm, fn.symm.injective⟩

variable {n : ℕ}

theorem IndexType.not_lt_zero (j : IndexType n) : ¬j < 0 :=
  Nat.casesOn n Nat.not_lt_zero (fun _ ↦ Fin.not_lt_zero) j

theorem IndexType.zero_le (i : IndexType n) : 0 ≤ i := by cases n <;> dsimp at * <;> simp

def IndexType.succ {N : ℕ} : IndexType N → IndexType N := Order.succ

theorem IndexType.succ_castSuccEmb (i : Fin n) :
    @IndexType.succ (n + 1) i.castSucc = i.succ :=
  (Fin.orderSucc_apply _).trans (lastCases_castSucc i)

theorem IndexType.succ_eq (i : IndexType n) : i.succ = i ↔ IsMax i :=
  Order.succ_eq_iff_isMax

theorem IndexType.lt_succ (i : IndexType n) (h : ¬IsMax i) : i < i.succ :=
  Order.lt_succ_of_not_isMax h

theorem IndexType.le_max {i : IndexType n} (h : IsMax i) (j) : j ≤ i :=
  h.isTop j

nonrec theorem IndexType.le_of_lt_succ (i : IndexType n) {j : IndexType n}
    (h : i < j.succ) : i ≤ j :=
  Order.le_of_lt_succ h

theorem IndexType.exists_castSucc_eq (i : IndexType (n + 1)) (hi : ¬IsMax i) :
    ∃ i' : Fin n, i'.castSucc = i := by
  revert hi
  refine Fin.lastCases ?_ (fun i _ ↦ ⟨_, rfl⟩) i
  intro hi; apply hi.elim; intro i _; exact le_last i

theorem IndexType.toNat_succ (i : IndexType n) (hi : ¬IsMax i) :
    i.succ.toNat = i.toNat + 1 := by
  cases n; · rfl
  rcases i.exists_castSucc_eq hi with ⟨i, rfl⟩
  rw [IndexType.succ_castSuccEmb]
  exact val_succ i

-- @[simp] can prove this
theorem IndexType.not_isMax (n : IndexType 0) : ¬IsMax n :=
  not_isMax_of_lt <| Nat.lt_succ_self n

@[elab_as_elim]
theorem IndexType.induction_from {P : IndexType n → Prop} {i₀ : IndexType n} (h₀ : P i₀)
    (ih : ∀ i ≥ i₀, ¬IsMax i → P i → P i.succ) : ∀ i ≥ i₀, P i := by
  cases n
  · intro i h
    induction' h with i hi₀i hi ih
    · exact h₀
    exact ih i hi₀i (IndexType.not_isMax i) hi
  intro i
  refine Fin.induction ?_ ?_ i
  · intro hi; convert h₀; exact (hi.le.antisymm <| Fin.zero_le _).symm
  · intro i hi hi₀i
    rcases hi₀i.le.eq_or_lt with (rfl | hi₀i)
    · exact h₀
    rw [← IndexType.succ_castSuccEmb]
    refine ih _ ?_ ?_ ?_
    · rwa [ge_iff_le, le_castSucc_iff]
    · exact not_isMax_of_lt (castSucc_lt_succ i)
    · apply hi; rwa [ge_iff_le, le_castSucc_iff]

@[elab_as_elim]
theorem IndexType.induction {P : IndexType n → Prop} (h₀ : P 0)
    (ih : ∀ i, ¬IsMax i → P i → P i.succ) : ∀ i, P i := fun i ↦
  IndexType.induction_from h₀ (fun i _ ↦ ih i) i i.zero_le

-- We make `P` and `Q` explicit to help the elaborator when applying the lemma
-- (elab_as_eliminator isn't enough).
theorem IndexType.exists_by_induction {α : Type*} (P : IndexType n → α → Prop)
    (Q : IndexType n → α → α → Prop) (h₀ : ∃ a, P 0 a)
    (ih : ∀ n a, P n a → ¬IsMax n → ∃ a', P n.succ a' ∧ Q n a a') :
    ∃ f : IndexType n → α, ∀ n, P n (f n) ∧ (¬IsMax n → Q n (f n) (f n.succ)) := by
  revert P Q h₀ ih
  cases' n with N
  · intro P Q h₀ ih
    rcases exists_by_induction' P Q h₀ (by simpa using ih) with ⟨f, hf⟩
    exact ⟨f, fun n ↦ ⟨(hf n).1, fun _ ↦ (hf n).2⟩⟩
  · -- dsimp only [IndexType, IndexType.succ]
    intro P Q h₀ ih
    choose f₀ hf₀ using h₀
    choose! F hF hF' using ih
    let G := fun i : Fin N ↦ F i.castSucc
    let f : Fin (N + 1) → α := fun i ↦ Fin.induction f₀ G i
    have key : ∀ i, P i (f i) := by
      refine fun i ↦ Fin.induction hf₀ ?_ i
      intro i hi
      simp_rw [f, induction_succ, ← IndexType.succ_castSuccEmb]
      exact hF _ _ hi (not_isMax_of_lt (castSucc_lt_succ i))
    refine ⟨f, fun i ↦ ⟨key i, fun hi ↦ ?_⟩⟩
    convert hF' _ _ (key i) hi
    rcases i.exists_castSucc_eq hi with ⟨i, rfl⟩
    simp_rw [IndexType.succ_castSuccEmb, f, induction_succ]
    rfl
