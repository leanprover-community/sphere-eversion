import algebra.periodic

variables {α β γ : Type*} {f : α → β} {c : α} [has_add α]

namespace function

open_locale big_operators

@[to_additive]
lemma periodic.smul [has_scalar γ β] (h : periodic f c) (a : γ) :
  periodic (a • f) c :=
by simp * at *

@[to_additive]
lemma periodic.prod [comm_monoid β] {ι : Type*} {f : ι → α → β} {s : finset ι}
  (hf : ∀ i, periodic (f i) c) :
  periodic (∏ i in s, f i) c :=
begin
  classical,
  induction s using finset.induction with i s hi ih,
  { simp, },
  { rw finset.prod_insert hi,
    exact (hf i).mul ih, },
end

end function
