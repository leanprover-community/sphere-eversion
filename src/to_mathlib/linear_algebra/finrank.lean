import linear_algebra.finite_dimensional

open finite_dimensional

variables {K : Type*} {V : Type*} [division_ring K] [add_comm_group V] [module K V]

-- this exists in the affine setting, `finrank_vector_span_insert_le`
lemma finrank_span_insert_le (s : set V) (a : V) :
  finrank K (submodule.span K (insert a s)) ≤ finrank K (submodule.span K s) + 1 :=
sorry

lemma finrank_span_singleton_le (a : V) : finrank K (K ∙ a) ≤ 1 :=
sorry
