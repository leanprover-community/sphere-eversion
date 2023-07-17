import Mathbin.Data.Set.Finite
import Mathbin.Data.Finite.Set

/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (i «expr ∉ » t) -/
theorem Set.finite_Union' {α ι : Type _} {s : ι → Set α} (hs : ∀ i, (s i).Finite) {t : Set ι}
    (ht₁ : t.Finite) (ht₂ : ∀ (i) (_ : i ∉ t), s i = ∅) : (⋃ i, s i).Finite :=
  by
  suffices (⋃ i, s i) ⊆ ⋃ i ∈ t, s i by exact (ht₁.bUnion fun i hi => hs i).Subset this
  intro x hx
  obtain ⟨i, hx⟩ := set.mem_Union.mp hx
  by_cases h : i ∈ t
  · simp only [Set.mem_iUnion]
    exact ⟨i, h, hx⟩
  · rw [ht₂ i h, Set.mem_empty_iff_false] at hx 
    contradiction

