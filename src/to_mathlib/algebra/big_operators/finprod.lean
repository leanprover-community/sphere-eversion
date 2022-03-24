import algebra.big_operators.finprod

open_locale big_operators
open function

variables {α M : Type*} [comm_monoid M]

@[to_additive] lemma finprod_eq_prod_of_mul_support_to_finset_subset'
  (f : α → M) {s : finset α} (h : mul_support f ⊆ (s : set α)) :
  ∏ᶠ i, f i = ∏ i in s, f i :=
begin
  have h' : (s.finite_to_set.subset h).to_finset ⊆ s,
  { erw [← finset.coe_subset, set.coe_to_finset],
    exact h, },
  exact finprod_eq_prod_of_mul_support_to_finset_subset _ _ h',
end
