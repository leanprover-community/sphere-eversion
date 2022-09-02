import data.nat.basic

-- The next lemma won't be used, it's a warming up exercise for the one below.
-- It could go to mathlib.
lemma exists_by_induction {α : Type*} {P : ℕ → α → Prop}
  (h₀ : ∃ a, P 0 a)
  (ih : ∀ n a, P n a → ∃ a', P (n+1) a') :
  ∃ f : ℕ → α, ∀ n, P n (f n) :=
begin
  choose f₀ hf₀ using h₀,
  choose! F hF using ih,
  exact ⟨λ n, nat.rec_on n f₀ F, λ n, nat.rec hf₀ (λ n ih, hF n _ ih) n⟩
end

-- We make `P` and `Q` explicit to help the elaborator when applying the lemma
-- (elab_as_eliminator isn't enough).
lemma exists_by_induction' {α : Type*} (P : ℕ → α → Prop) (Q : ℕ → α → α → Prop)
  (h₀ : ∃ a, P 0 a)
  (ih : ∀ n a, P n a → ∃ a', P (n+1) a' ∧ Q n a a') :
  ∃ f : ℕ → α, ∀ n, P n (f n) ∧ Q n (f n) (f $ n+1) :=
begin
  choose f₀ hf₀ using h₀,
  choose! F hF hF' using ih,
  have key : ∀ n, P n (nat.rec_on n f₀ F), from λ n, nat.rec hf₀ (λ n ih, hF n _ ih) n,
  exact ⟨λ n, nat.rec_on n f₀ F, λ n, ⟨key n, hF' n _ (key n)⟩⟩
end
