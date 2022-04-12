import data.real.basic

lemma real.bcsupr_le {ι : Type*} {f : ι → ℝ} {s : set ι} {t : ℝ} (ht : 0 ≤ t)
  (h : ∀ i ∈ s, f i ≤ t) : (⨆ i ∈ s, f i) ≤ t :=
begin
  cases is_empty_or_nonempty ι with hι hι; resetI,
  { simp_rw [real.csupr_empty, ht] },
  refine csupr_le (λ i, _),
  cases is_empty_or_nonempty (i ∈ s) with hi hi; resetI,
  { simp_rw [real.csupr_empty, ht] },
  refine csupr_le (λ hi, h i hi),
end

lemma real.bcsupr_nonneg {ι : Type*} {f : ι → ℝ} {s : set ι} (h : ∀ i ∈ s, 0 ≤ f i) :
  0 ≤ (⨆ i ∈ s, f i) :=
begin
  rcases s.eq_empty_or_nonempty with rfl|hs,
  { simp [real.csupr_empty] },
  cases hs with i hi,
  by_cases h1s : bdd_above (set.range (λ i, ⨆ (H : i ∈ s), f i)),
  { refine le_trans _ (le_csupr h1s i),
    by_cases h2s : bdd_above (set.range (λ (hi : i ∈ s), f i)),
    refine (h i hi).trans (le_csupr h2s hi),
    exact (real.Sup_of_not_bdd_above h2s).symm.le },
  exact (real.Sup_of_not_bdd_above h1s).symm.le
end

