import linear_algebra.determinant
import linear_algebra.matrix
import linear_algebra.multilinear

noncomputable theory

variables {ι ι' : Type*} {κ : Type*} {R : Type*} {K : Type*}
          {M : Type*} {M' : Type*} {V : Type*} {V' : Type*}

variables [fintype ι] [decidable_eq ι]
variables [comm_ring R] [add_comm_group M] [add_comm_group M']
variables [module R M] [module R M']

open matrix set function linear_map 
open_locale matrix big_operators

open equiv equiv.perm finset

lemma det_update_column_add {n : Type*} [fintype n] [decidable_eq n] {α : Type*} [comm_ring α]  
  (M : matrix n n α) (j : n) (u v : n → α) :
  det (update_column M j $ u + v) = det (update_column M j u) + det (update_column M j v) :=
begin
  simp only [det],
  have : ∀ σ : perm n, ∏ i, M.update_column j (u + v) (σ i) i = ∏ i, M.update_column j u (σ i) i +
                                                                ∏ i, M.update_column j v (σ i) i,
  { intros σ,
    simp only [update_column_apply, prod_ite, filter_eq', 
               finset.prod_singleton, finset.mem_univ, if_true, pi.add_apply, add_mul] },
  rw [← sum_add_distrib],
  apply sum_congr rfl,
  intros x _,
  rw [this, mul_add]
end

lemma det_update_row_add {n : Type*} [fintype n] [decidable_eq n] {α : Type*} [comm_ring α]  
  (M : matrix n n α) (j : n) (u v : n → α) :
  det (update_row M j $ u + v) = det (update_row M j u) + det (update_row M j v) :=
begin
  rw [← det_transpose, ← update_column_transpose, det_update_column_add],
  simp [update_column_transpose, det_transpose]
end

lemma det_update_column_smul {n : Type*} [fintype n] [decidable_eq n] {α : Type*} [comm_ring α]  
  (M : matrix n n α) (j : n) (s : α) (u : n → α) :
  det (update_column M j $ s • u) = s*det (update_column M j u) :=
begin
  simp only [det],
  have : ∀ σ : perm n, ∏ i, M.update_column j (s • u) (σ i) i = s * ∏ i, M.update_column j u (σ i) i,
  { intros σ,
    simp only [update_column_apply, prod_ite, filter_eq', finset.prod_singleton, finset.mem_univ,
               if_true, algebra.id.smul_eq_mul, pi.smul_apply],
    ring },
  rw mul_sum,
  apply sum_congr rfl,
  intros x _,
  rw this,
  ring
end

lemma det_update_row_smul {n : Type*} [fintype n] [decidable_eq n] {α : Type*} [comm_ring α]  
  (M : matrix n n α) (j : n) (s : α) (u : n → α) :
  det (update_row M j $ s • u) = s*det (update_row M j u) :=
begin
  rw [← det_transpose, ← update_column_transpose, det_update_column_smul],
  simp [update_column_transpose, det_transpose]
end

def linear_equiv_matrix_apply {M₁ M₂ ι κ : Type*}
  [add_comm_group M₁] [module R M₁]
  [add_comm_group M₂] [module R M₂]
  [decidable_eq ι] [fintype ι] [fintype κ]
  {v₁ : ι → M₁} {v₂ : κ → M₂} (hv₁ : is_basis R v₁) (hv₂ : is_basis R v₂) (f : M₁ →ₗ[R] M₂) (i : κ) (j : ι) :
  linear_equiv_matrix hv₁ hv₂ f i j = equiv_fun_basis hv₂ (f (v₁ j)) i :=
by simp only [linear_equiv_matrix, to_matrix, to_matrixₗ, ite_smul,
  linear_equiv.trans_apply, linear_equiv.arrow_congr_apply,
  linear_equiv.coe_coe, linear_equiv_matrix'_apply, finset.mem_univ, if_true,
  one_smul, zero_smul, finset.sum_ite_eq, equiv_fun_basis_symm_apply]

def linear_equiv_matrix_apply' {ι κ M₁ M₂ : Type*}
  [add_comm_group M₁] [module R M₁]
  [add_comm_group M₂] [module R M₂]
  [decidable_eq ι] [fintype ι] [fintype κ]
  {v₁ : ι → M₁} {v₂ : κ → M₂} (hv₁ : is_basis R v₁) (hv₂ : is_basis R v₂) (f : M₁ →ₗ[R] M₂) (i : κ) (j : ι) :
  linear_equiv_matrix hv₁ hv₂ f i j = hv₂.repr (f (v₁ j)) i :=
linear_equiv_matrix_apply hv₁ hv₂ f i j

variables {M'' : Type*} [add_comm_group M''] [module R M''] [module R M'']

lemma linear_equiv.eq_of_linear_map_eq {f f' : M ≃ₗ[R] M'} (h : (f : M →ₗ[R] M') = f') : f = f' :=
begin
  ext x,
  change (f : M →ₗ[R] M') x = (f' : M →ₗ[R] M') x,
  erw h
end

lemma equiv_of_is_basis_comp {ι'' : Type*} {v : ι → M} {v' : ι' → M'} {v'' : ι'' → M''} 
(hv : is_basis R v) (hv' : is_basis R v') (hv'' : is_basis R v'')
  (e : ι ≃ ι') (f : ι' ≃ ι'' ) : 
  equiv_of_is_basis hv hv'' (e.trans f) =  (equiv_of_is_basis hv hv' e).trans (equiv_of_is_basis hv' hv'' f) :=
begin
  apply linear_equiv.eq_of_linear_map_eq,
  apply hv.ext,
  intros i,
  simp [equiv_of_is_basis]
end

@[simp] lemma equiv_of_is_basis_refl {v : ι → M} (hv : is_basis R v) : 
  equiv_of_is_basis hv hv (equiv.refl ι) = linear_equiv.refl R M :=
begin
  apply linear_equiv.eq_of_linear_map_eq,
  apply hv.ext,
  intros i,
  simp [equiv_of_is_basis]  
end

lemma equiv_of_is_basis_symm {v : ι → M} {v' : ι' → M'} (hv : is_basis R v) (hv' : is_basis R v') (e : ι ≃ ι') : 
  (equiv_of_is_basis hv hv' e).trans (equiv_of_is_basis hv' hv e.symm) = linear_equiv.refl R M :=
by simp [← equiv_of_is_basis_comp]

@[simp]
lemma linear_equiv_matrix_id {v : ι → M} (hv : is_basis R v) : linear_equiv_matrix hv hv id = 1 :=
begin
  ext i j,
  simp [linear_equiv_matrix_apply, equiv_fun_basis, matrix.one_apply, finsupp.single, eq_comm]  
end

@[simp] lemma linear_equiv.trans_symm (f : M ≃ₗ[R] M') : f.trans f.symm = linear_equiv.refl R M:=
by { ext x, simp }

@[simp, norm_cast] lemma linear_equiv.refl_to_linear_map : (linear_equiv.refl R M : M →ₗ[R] M) = id :=
rfl

@[simp, norm_cast]
lemma linear_equiv.comp_coe (f :  M ≃ₗ[R] M') (f' :  M' ≃ₗ[R] M'') : 
  (f' : M' →ₗ[R] M'').comp (f : M →ₗ[R] M') = (f.trans f' : M →ₗ[R] M''):=
rfl

lemma linear_equiv.is_unit_det (f : M ≃ₗ[R] M') {v : ι → M} {v' : ι → M'} (hv : is_basis R v) (hv' : is_basis R v') :
  is_unit (linear_equiv_matrix hv hv' f).det :=
begin
  apply is_unit_det_of_left_inverse,
  simpa using (linear_equiv_matrix_comp hv hv' hv f.symm f).symm
end

local notation `Mat` := linear_equiv_matrix

@[simp] lemma linear_equiv_matrix_symm_one {v : ι → M} (hv : is_basis R v) : 
  (linear_equiv_matrix hv hv).symm 1 = id :=
begin
  rw ← linear_equiv_matrix_id hv,
  change ((Mat hv hv).trans (Mat hv hv).symm) id = id,
  simp
end

@[simp, norm_cast] lemma linear_map_id_coe : ((linear_map.id : M →ₗ[R] M) : M → M) = id :=
by { ext x, refl }

lemma linear_equiv_matrix_symm_mul {ι κ μ : Type*} [fintype ι] [fintype κ] [fintype μ]
  [decidable_eq ι] [decidable_eq κ] [decidable_eq μ]
  {v : ι → M} {v' : κ → M'} {v'' : μ → M''} 
  (hv : is_basis R v) (hv' : is_basis R v') (hv'' : is_basis R v'')
  (A : matrix ι κ R) (B : matrix κ μ R) : 
  (linear_equiv_matrix hv'' hv).symm (A ⬝ B) =
  ((linear_equiv_matrix hv' hv).symm A).comp ((linear_equiv_matrix hv'' hv').symm B) :=
begin
  suffices :  A ⬝ B = (linear_equiv_matrix hv'' hv)
     (((linear_equiv_matrix hv' hv).symm A).comp $ (linear_equiv_matrix hv'' hv').symm B),
  { rw this,
    change (Mat hv'' hv).trans (Mat hv'' hv).symm _ = _,
    simp },
  rw linear_equiv_matrix_comp hv'' hv' hv,
  simp
end

lemma function.left_inverse_iff_comp {α β : Type*} (f : α → β) (g : β → α) : left_inverse f g ↔ f ∘ g = id :=
⟨λ h, funext $ h, λ h x, congr_fun h x⟩

lemma function.right_inverse_iff_comp {α β : Type*} (f : α → β) (g : β → α) : right_inverse f g ↔ g ∘ f = id :=
⟨λ h, funext $ h, λ h x, congr_fun h x⟩

@[norm_cast] 
lemma linear_map.comp_coe (f : M →ₗ[R] M')(g : M' →ₗ[R] M'') : (g : M' → M'') ∘ (f : M → M') = g.comp f :=
rfl

/-- Builds a linear equivalence from a linear map whose determinant in some bases is a unit. -/
def linear_equiv.of_is_unit_det {f : M →ₗ[R] M'} {v : ι → M} {v' : ι → M'} {hv : is_basis R v} {hv' : is_basis R v'} 
  (h : is_unit (linear_equiv_matrix hv hv' f).det) : M ≃ₗ[R] M' :=
{ to_fun := f,
  map_add' := f.map_add,
  map_smul' := f.map_smul,
  inv_fun := (linear_equiv_matrix hv' hv).symm (linear_equiv_matrix hv hv' f)⁻¹,
  left_inv := begin
    rw function.left_inverse_iff_comp,
    have : f = (linear_equiv_matrix hv hv').symm (linear_equiv_matrix hv hv' f),
    { rw ← linear_equiv.trans_apply,
      simp },
    conv_lhs { congr, skip, rw this },
    rw [linear_map.comp_coe, ← linear_equiv_matrix_symm_mul],
    simp [h]
  end,
  right_inv := begin
    rw function.right_inverse_iff_comp,
    have : f = (linear_equiv_matrix hv hv').symm (linear_equiv_matrix hv hv' f),
    { change f = (linear_equiv_matrix hv hv').trans (linear_equiv_matrix hv hv').symm f,
      simp },
    conv_lhs { congr, rw this },
    rw [linear_map.comp_coe, ← linear_equiv_matrix_symm_mul],
    simp [h]
  end }
variables {e : ι → M} (he : is_basis R e)
def is_basis.to_matrix (v : ι → M) : matrix ι ι R := linear_equiv_matrix he he (he.constr v)


lemma is_basis.to_matrix_apply (v : ι → M) (i j : ι) : he.to_matrix v j i = he.repr (v i) j :=
by simp [is_basis.to_matrix, linear_equiv_matrix_apply']

@[simp] lemma is_basis.to_matrix_self : he.to_matrix e = 1 :=
begin
  rw is_basis.to_matrix,
  ext i j,
  simp [linear_equiv_matrix_apply, equiv_fun_basis, matrix.one_apply, finsupp.single, eq_comm]
end

lemma to_matrix.update_eq {v : ι → M} (i : ι) (x : M) :
  he.to_matrix (function.update v i x) = matrix.update_column (he.to_matrix v) i (he.repr x) :=
begin
  ext j k,
  rw [is_basis.to_matrix, linear_equiv_matrix_apply' he he (he.constr (update v i x)),
      update_column_apply, constr_basis, he.to_matrix_apply],
  split_ifs, 
  { rw [h, update_same i x v] },
  { rw update_noteq h },
end

def is_basis.det : multilinear_map R (λ i : ι, M) R := 
{ to_fun := λ v, det (he.to_matrix v),
  map_add' := begin
    intros v i x y,
    simp only [to_matrix.update_eq, linear_map.map_add],
    apply det_update_column_add
  end,
  map_smul' := begin
    intros u i c x,
    simp only [to_matrix.update_eq, algebra.id.smul_eq_mul, map_smul_eq_smul_map],
    apply det_update_column_smul
  end }

lemma is_basis.det_apply (v : ι → M) : he.det v = det (he.to_matrix v) := rfl

lemma is_bases.det_self : he.det e = 1 :=
by simp [he.det_apply]


lemma is_basis.iff_det (v : ι → M) : is_basis R v ↔ is_unit (he.det v) :=
begin
  split,
  { intro hv,
    change is_unit (linear_equiv_matrix he he (equiv_of_is_basis he hv $ equiv.refl ι)).det,
    apply linear_equiv.is_unit_det },
  { intro h,
    convert linear_equiv.is_basis he (linear_equiv.of_is_unit_det h),
    ext i, 
    exact (constr_basis he).symm },
end
