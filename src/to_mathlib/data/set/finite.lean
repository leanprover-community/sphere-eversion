import data.set.finite
import data.finite.set

lemma equiv.set_finite_iff {α β : Type*} {s : set α} {t : set β} (hst : s ≃ t) :
  s.finite ↔ t.finite :=
by rw [set.finite_iff_finite, set.finite_iff_finite, hst.finite_iff]

lemma set.finite_Union' {α ι : Type*} {s : ι → set α} (hs : ∀ i, (s i).finite) {t : set ι}
  (ht₁ : t.finite) (ht₂ : ∀ i ∉ t, s i = ∅) :
  (⋃ i, s i).finite :=
begin
  suffices : (⋃ i, s i) ⊆ (⋃ i ∈ t, s i),
  { exact (ht₁.bUnion (λ i hi, hs i)).subset this, },
  intros x hx,
  obtain ⟨i, hx⟩ := set.mem_Union.mp hx,
  by_cases h : i ∈ t,
  { simp only [set.mem_Union],
    exact ⟨i, h, hx⟩, },
  { rw [ht₂ i h, set.mem_empty_eq] at hx,
    contradiction, },
end