import logic.equiv.local_equiv

open set

lemma local_equiv.range_eq_target_of_source_eq_univ {α β : Type*}
  (e : local_equiv α β) (h : e.source = univ) :
  range e = e.target :=
by { rw [← image_univ, ← h], exact e.image_source_eq_target, }
