import Mathbin.Data.Nat.Basic

-- The next lemma won't be used, it's a warming up exercise for the one below.
-- The next lemma won't be used, it's a warming up exercise for the one below.
-- It could go to mathlib.
-- It could go to mathlib.
theorem exists_by_induction {α : Type _} {P : ℕ → α → Prop} (h₀ : ∃ a, P 0 a)
    (ih : ∀ n a, P n a → ∃ a', P (n + 1) a') : ∃ f : ℕ → α, ∀ n, P n (f n) :=
  by
  choose f₀ hf₀ using h₀
  choose! F hF using ih
  exact ⟨fun n => Nat.recOn n f₀ F, fun n => Nat.rec hf₀ (fun n ih => hF n _ ih) n⟩

-- We make `P` and `Q` explicit to help the elaborator when applying the lemma
-- (elab_as_eliminator isn't enough).
theorem exists_by_induction' {α : Type _} (P : ℕ → α → Prop) (Q : ℕ → α → α → Prop)
    (h₀ : ∃ a, P 0 a) (ih : ∀ n a, P n a → ∃ a', P (n + 1) a' ∧ Q n a a') :
    ∃ f : ℕ → α, ∀ n, P n (f n) ∧ Q n (f n) (f <| n + 1) :=
  by
  choose f₀ hf₀ using h₀
  choose! F hF hF' using ih
  have key : ∀ n, P n (Nat.recOn n f₀ F) := fun n => Nat.rec hf₀ (fun n ih => hF n _ ih) n
  exact ⟨fun n => Nat.recOn n f₀ F, fun n => ⟨key n, hF' n _ (key n)⟩⟩

