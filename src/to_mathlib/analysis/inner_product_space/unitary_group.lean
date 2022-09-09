import analysis.inner_product_space.pi_L2
import linear_algebra.unitary_group

noncomputable theory

section star_ring
variables {n : Type*} [decidable_eq n] [fintype n] {α : Type*}
  [comm_ring α] [star_ring α]

lemma matrix.mem_unitary_group_iff' {A : matrix n n α} :
  A ∈ matrix.unitary_group n α ↔ star A * A = 1 :=
begin
  refine ⟨and.left, λ hA, ⟨hA, _⟩⟩,
  rwa [matrix.mul_eq_mul, matrix.mul_eq_one_comm] at hA,
end

lemma matrix.det_of_mem_unitary {A : matrix n n α} (hA : A ∈ matrix.unitary_group n α) :
  A.det ∈ unitary α :=
begin
  split,
  { simpa [star, matrix.det_transpose] using congr_arg matrix.det hA.1 },
  { simpa [star, matrix.det_transpose] using congr_arg matrix.det hA.2 },
end

end star_ring

variables {ι : Type*} [fintype ι] [decidable_eq ι]

section
variables {𝕜 : Type*} [is_R_or_C 𝕜]
variables {F : Type*} [inner_product_space 𝕜 F] (a b : orthonormal_basis ι 𝕜 F)

lemma orthonormal_basis.to_matrix_orthonormal_basis_mem_unitary :
  a.to_basis.to_matrix b ∈ matrix.unitary_group ι 𝕜 :=
begin
  rw matrix.mem_unitary_group_iff',
  ext i j,
  convert a.repr.inner_map_map (b i) (b j),
  rw orthonormal_iff_ite.mp b.orthonormal i j,
  refl,
end

lemma orthonormal_basis.det_to_matrix_orthonormal_basis :
  a.to_basis.det b ∈ unitary 𝕜 :=
matrix.det_of_mem_unitary (a.to_matrix_orthonormal_basis_mem_unitary b)

end

section
variables {E : Type*} [inner_product_space ℝ E] (a b : orthonormal_basis ι ℝ E)

lemma orthonormal_basis.to_matrix_orthonormal_basis_mem_orthogonal :
  a.to_basis.to_matrix b ∈ matrix.orthogonal_group ι ℝ :=
a.to_matrix_orthonormal_basis_mem_unitary b

lemma orthonormal_basis.det_to_matrix_orthonormal_basis_real :
  a.to_basis.det b = 1 ∨ a.to_basis.det b = -1 :=
begin
  rw ← sq_eq_one_iff,
  simpa [unitary, sq] using a.det_to_matrix_orthonormal_basis b
end

end
