import linear_algebra.determinant

open_locale big_operators

variables {R : Type*} [comm_ring R] {M : Type*} [add_comm_group M] [module R M] {ι : Type*}
  [decidable_eq ι] [fintype ι]

lemma basis.coord_units_smul (e : basis ι R M) (w : ι → Rˣ) (i : ι) :
  (e.units_smul w).coord i = (w i)⁻¹ • e.coord i :=
begin
  apply e.ext,
  intros j,
  transitivity ((e.units_smul w).coord i) ((w j)⁻¹ • (e.units_smul w) j),
  { congr,
    simp [basis.units_smul, ← mul_smul], },
  simp only [basis.coord_apply, linear_map.smul_apply, basis.repr_self, units.smul_def, map_smul,
    finsupp.single_apply],
  split_ifs with h h,
  { simp [h] },
  { simp }
end

lemma basis.repr_units_smul (e : basis ι R M) (w : ι → Rˣ) (v : M) (i : ι) :
  (e.units_smul w).repr v i = (w i)⁻¹ • e.repr v i :=
congr_arg (λ f : M →ₗ[R] R, f v) (e.coord_units_smul w i)

-- rename existing `basis.det_units_smul` to make room for this
lemma basis.det_units_smul' (e : basis ι R M) (w : ι → Rˣ) :
  (e.units_smul w).det = (↑(∏ i, w i)⁻¹ : R) • e.det :=
begin
  ext f,
  change matrix.det (λ i j, (e.units_smul w).repr (f j) i)
    = (↑(∏ i, w i)⁻¹ : R) • matrix.det (λ i j, e.repr (f j) i),
  simp only [e.repr_units_smul],
  convert matrix.det_mul_column (λ i, (↑((w i)⁻¹) : R)) (λ i j, e.repr (f j) i),
  simp [← finset.prod_inv_distrib]
end
