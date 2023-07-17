import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.WithZero
import Mathlib.Topology.LocallyFinite
import Mathlib.Data.Fin.Interval
import Mathlib.Data.Fin.SuccPred
import SphereEversion.ToMathlib.Data.Nat.Basic
import SphereEversion.ToMathlib.SetTheory.Cardinal.Basic

/-!
# Indexing types

This file introduces `index_type : ℕ → Type` such that `index_type 0 = ℕ` and
`index_type (N+1) = fin (N+1)`. Each `index_type N` has a total order and and inductive principle
together with supporting lemmas.
-/


open Set

/-- Our model indexing type depending on `n : ℕ` is `ℕ` if `n = 0` and `fin n` otherwise-/
def IndexType (n : ℕ) : Type :=
  Nat.casesOn n ℕ fun k => Fin <| k + 1

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

instance (n : ℕ) : LinearOrder (IndexType n) :=
  Nat.casesOn n Nat.linearOrder fun _ => inferInstanceAs (LinearOrder (Fin _))

instance (n : ℕ) : LocallyFiniteOrder (IndexType n) :=
  Nat.casesOn n Nat.locallyFiniteOrder fun _ => Fin.locallyFiniteOrder _

instance (n : ℕ) : OrderBot (IndexType n) :=
  Nat.casesOn n Nat.orderBot fun k => show OrderBot <| Fin (k + 1) by infer_instance

instance (N : ℕ) : Zero (IndexType N) :=
  ⟨IndexType.fromNat 0⟩

theorem Set.countable_iff_exists_nonempty_indexType_equiv {α : Type _} {s : Set α}
    (hne : s.Nonempty) : s.Countable ↔ ∃ n, Nonempty (IndexType n ≃ s) :=
  by
  -- Huge golfing opportunity.
  cases @Set.finite_or_infinite _ s
  · refine' ⟨fun hh => ⟨h.to_finset.card, _⟩, fun _ => h.countable⟩
    have : 0 < h.to_finset.card := by rw [Finset.card_pos];
      exact (Set.Finite.toFinset_nonempty h).mpr hne
    simp only [this, indexType_of_zero_lt]
    have e₁ := Fintype.equivFin h.to_finset
    rw [Fintype.card_coe, h.coe_sort_to_finset] at e₁ 
    exact ⟨e₁.symm⟩
  · refine' ⟨fun hh => ⟨0, _⟩, _⟩
    · simp only [indexType_zero]
      obtain ⟨_i⟩ := set.countable_infinite_iff_nonempty_denumerable.mp ⟨hh, h⟩
      haveI := _i
      exact ⟨(Denumerable.eqv s).symm⟩
    · rintro ⟨n, ⟨fn⟩⟩
      have hn : n = 0 := by
        by_contra hn
        replace hn : 0 < n := zero_lt_iff.mpr hn
        simp only [hn, indexType_of_zero_lt] at fn 
        exact set.not_infinite.mpr ⟨Fintype.ofEquiv (Fin n) fn⟩ h
      simp only [hn, indexType_zero] at fn 
      exact set.countable_iff_exists_injective.mpr ⟨fn.symm, fn.symm.injective⟩

theorem IndexType.not_lt_zero {N : ℕ} (j : IndexType N) : ¬j < 0 :=
  Nat.casesOn N Nat.not_lt_zero (fun _ => Fin.not_lt_zero) j

open Order Fin

theorem IndexType.zero_le {N} (i : IndexType N) : 0 ≤ i := by cases N <;> dsimp at * <;> simp

instance {N : ℕ} : SuccOrder (IndexType N) := by cases N; · exact Nat.succOrder; exact Fin.succOrder

def IndexType.succ {N : ℕ} : IndexType N → IndexType N :=
  Order.succ

theorem IndexType.succ_castSuccEmb {N} (i : Fin N) : @IndexType.succ (N + 1) i.castSucc = i.succ :=
  by
  refine' (succ_apply _).trans _
  rw [if_pos (cast_succ_lt_last i), Fin.coeSucc_eq_succ, Fin.succ_inj]

theorem IndexType.succ_eq {N} (i : IndexType N) : i.succ = i ↔ IsMax i :=
  Order.succ_eq_iff_isMax

theorem IndexType.lt_succ {N : ℕ} (i : IndexType N) (h : ¬IsMax i) : i < i.succ :=
  Order.lt_succ_of_not_isMax h

theorem IndexType.le_max {N : ℕ} {i : IndexType N} (h : IsMax i) (j) : j ≤ i :=
  h.IsTop j

theorem IndexType.le_of_lt_succ {N : ℕ} (i : IndexType N) {j : IndexType N} (h : i < j.succ) :
    i ≤ j :=
  le_of_lt_succ h

theorem IndexType.exists_castSuccEmb_eq {N : ℕ} (i : Fin (N + 1)) (hi : ¬IsMax i) :
    ∃ i' : Fin N, i'.cast_succ = i := by
  revert hi
  refine' Fin.lastCases _ _ i
  · intro hi; apply hi.elim; intro i hi; exact le_last i
  intro i hi
  exact ⟨_, rfl⟩

theorem IndexType.toNat_succ {N : ℕ} (i : IndexType N) (hi : ¬IsMax i) :
    i.succ.toNat = i.toNat + 1 := by
  cases N; · rfl
  rcases i.exists_cast_succ_eq hi with ⟨i, rfl⟩
  rw [IndexType.succ_castSuccEmb]
  exact coe_succ i

@[simp]
theorem IndexType.not_isMax (n : IndexType 0) : ¬IsMax n :=
  not_isMax_of_lt <| Nat.lt_succ_self n

@[elab_as_elim]
theorem IndexType.induction_from {N : ℕ} {P : IndexType N → Prop} {i₀ : IndexType N} (h₀ : P i₀)
    (ih : ∀ i ≥ i₀, ¬IsMax i → P i → P i.succ) : ∀ i ≥ i₀, P i :=
  by
  cases N
  · intro i h
    induction' h with i hi₀i hi ih
    · exact h₀
    exact ih i hi₀i (IndexType.not_isMax i) hi
  intro i
  refine' Fin.induction _ _ i
  · intro hi; convert h₀; exact (hi.le.antisymm <| Fin.zero_le _).symm
  · intro i hi hi₀i
    rcases hi₀i.le.eq_or_lt with (rfl | hi₀i)
    · exact h₀
    rw [← IndexType.succ_castSuccEmb]
    refine' ih _ _ _ _
    · rwa [ge_iff_le, le_cast_succ_iff]
    · exact not_isMax_of_lt (cast_succ_lt_succ i)
    · apply hi; rwa [ge_iff_le, le_cast_succ_iff]

@[elab_as_elim]
theorem IndexType.induction {N : ℕ} {P : IndexType N → Prop} (h₀ : P 0)
    (ih : ∀ i, ¬IsMax i → P i → P i.succ) : ∀ i, P i := fun i =>
  IndexType.induction_from h₀ (fun i _ => ih i) i i.zero_le

-- We make `P` and `Q` explicit to help the elaborator when applying the lemma
-- (elab_as_eliminator isn't enough).
theorem IndexType.exists_by_induction {N : ℕ} {α : Type _} (P : IndexType N → α → Prop)
    (Q : IndexType N → α → α → Prop) (h₀ : ∃ a, P 0 a)
    (ih : ∀ n a, P n a → ¬IsMax n → ∃ a', P n.succ a' ∧ Q n a a') :
    ∃ f : IndexType N → α, ∀ n, P n (f n) ∧ (¬IsMax n → Q n (f n) (f n.succ)) := by
  revert P Q h₀ ih
  cases' N with N
  · intro P Q h₀ ih
    rcases exists_by_induction' P Q h₀ _ with ⟨f, hf⟩
    exact ⟨f, fun n => ⟨(hf n).1, fun _ => (hf n).2⟩⟩
    simpa using ih
  · --dsimp only [index_type, index_type.succ],
    intro P Q h₀ ih
    choose f₀ hf₀ using h₀
    choose! F hF hF' using ih
    let G := fun i : Fin N => F i.castSucc
    let f : Fin (N + 1) → α := fun i => Fin.induction f₀ G i
    have key : ∀ i, P i (f i) := by
      refine' fun i => Fin.induction hf₀ _ i
      intro i hi
      simp_rw [induction_succ, ← IndexType.succ_castSuccEmb]
      apply hF _ _ hi
      exact not_isMax_of_lt (cast_succ_lt_succ i)
    refine' ⟨f, fun i => ⟨key i, fun hi => _⟩⟩
    · convert hF' _ _ (key i) hi
      rcases i.exists_castSucc_eq hi with ⟨i, rfl⟩
      simp_rw [IndexType.succ_castSuccEmb, f, induction_succ]

