import linear_algebra.determinant

open_locale big_operators

variables {R : Type*} [comm_ring R] {M : Type*} [add_comm_group M] [module R M] {ι : Type*}
  [decidable_eq ι] [fintype ι]

-- rename existing `basis.det_units_smul` to make room for this
lemma basis.det_units_smul' (e : basis ι R M) (w : ι → Rˣ) :
  (e.units_smul w).det = (∏ i, w i : R) • e.det :=
sorry
