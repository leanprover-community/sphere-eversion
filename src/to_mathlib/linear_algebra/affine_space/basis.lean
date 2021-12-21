import linear_algebra.affine_space.basis

open_locale big_operators

namespace affine_basis

variables {ι R M : Type*} [fintype ι] [ring R] [add_comm_group M] [module R M]

/-- A variant of `affine_basis.affine_combination_coord_eq_self` for the special case when the
affine space is a module so we can talk about linear combinations. -/
lemma linear_combination_coord_eq_self (b : affine_basis ι R M) (m : M) :
  ∑ i, (b.coord i m) • (b.points i) = m :=
begin
  have hb := b.affine_combination_coord_eq_self m,
  rwa finset.univ.affine_combination_eq_linear_combination _ _ (b.sum_coord_apply_eq_one m) at hb,
end

end affine_basis