/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import analysis.inner_product_space.gram_schmidt_ortho
import linear_algebra.matrix.block

/-! # Additions to the mathlib theory of Gram-Schmidt orthogonalization -/

open finite_dimensional submodule finset
open_locale big_operators

variables (𝕜 : Type*) [is_R_or_C 𝕜]
variables {E : Type*} [inner_product_space 𝕜 E]
variables {ι : Type*} [linear_order ι] [locally_finite_order_bot ι] [is_well_order ι (<)]

local notation `⟪`x`, `y`⟫` := @inner 𝕜 _ _ x y

variables {𝕜}
variables [fintype ι] [finite_dimensional 𝕜 E] (h : finrank 𝕜 E = fintype.card ι) (f : ι → E)
include h

/-- Given an indexed family `f : ι → E` of vectors in an inner product space `E`, for which the
size of the index set is the dimension of `E`, produce an orthonormal basis for `E` which agrees
with the orthonormal set produced by the Gram-Schmidt orthonormalization process on the elements of
`ι` for which this process gives a nonzero number. -/
noncomputable def gram_schmidt_orthonormal_basis' : orthonormal_basis ι 𝕜 E :=
((gram_schmidt_orthonormal' f).exists_orthonormal_basis_extension_of_card_eq h).some

lemma gram_schmidt_orthonormal_basis'_apply {f : ι → E} {i : ι}
  (hi : gram_schmidt_normed 𝕜 f i ≠ 0) :
  gram_schmidt_orthonormal_basis' h f i = gram_schmidt_normed 𝕜 f i :=
((gram_schmidt_orthonormal' f).exists_orthonormal_basis_extension_of_card_eq h).some_spec i hi

lemma gram_schmidt_orthonormal_basis'_apply_of_orthogonal {f : ι → E}
  (hf : pairwise (λ i j, ⟪f i, f j⟫ = 0)) {i : ι} (hi : f i ≠ 0) :
  gram_schmidt_orthonormal_basis' h f i = (∥f i∥⁻¹ : 𝕜) • f i :=
begin
  have H : gram_schmidt_normed 𝕜 f i = (∥f i∥⁻¹ : 𝕜) • f i,
  { rw [gram_schmidt_normed, gram_schmidt_of_orthogonal 𝕜 hf] },
  rw [gram_schmidt_orthonormal_basis'_apply h, H],
  simpa [H] using hi,
end

lemma inner_gram_schmidt_orthonormal_basis'_eq_zero {f : ι → E} {i : ι}
  (hi : gram_schmidt_normed 𝕜 f i = 0) (j : ι) :
  ⟪gram_schmidt_orthonormal_basis' h f i, f j⟫ = 0 :=
begin
  apply inner_right_of_mem_orthogonal_singleton,
  suffices : span 𝕜 (gram_schmidt_normed 𝕜 f '' Iic j) ≤ (𝕜 ∙ gram_schmidt_orthonormal_basis' h f i)ᗮ,
  { apply this,
    rw span_gram_schmidt_normed,
    simpa using mem_span_gram_schmidt 𝕜 f (le_refl j) },
  rw span_le,
  rintros - ⟨k, -, rfl⟩,
  apply mem_orthogonal_singleton_of_inner_left,
  by_cases hk : gram_schmidt_normed 𝕜 f k = 0,
  { simp [hk] },
  rw ← gram_schmidt_orthonormal_basis'_apply h hk,
  have : k ≠ i,
  { rintros rfl,
    exact hk hi },
  exact (gram_schmidt_orthonormal_basis' h f).orthonormal.2 this,
end

lemma gram_schmidt_orthonormal_basis'_inv_triangular {i j : ι} (hij : i < j) :
  ⟪gram_schmidt_orthonormal_basis' h f j, f i⟫ = 0 :=
begin
  by_cases hi : gram_schmidt_normed 𝕜 f j = 0,
  { rw inner_gram_schmidt_orthonormal_basis'_eq_zero h hi },
  { simp [gram_schmidt_orthonormal_basis'_apply h hi, gram_schmidt_normed, inner_smul_left,
      gram_schmidt_inv_triangular 𝕜 f hij] }
end

lemma gram_schmidt_orthonormal_basis'_inv_triangular' {i j : ι} (hij : i < j) :
  (gram_schmidt_orthonormal_basis' h f).repr (f i) j = 0 :=
by simpa [orthonormal_basis.repr_apply_apply]
  using gram_schmidt_orthonormal_basis'_inv_triangular h f hij

/-- Given an indexed family `f : ι → E` of vectors in an inner product space `E`, for which the
size of the index set is the dimension of `E`, the matrix of coefficients of `f` with respect to the
orthonormal basis `gram_schmidt_orthonormal_basis'` constructed from `f` is upper-triangular. -/
lemma gram_schmidt_orthonormal_basis'_inv_block_triangular :
  ((gram_schmidt_orthonormal_basis' h f).to_basis.to_matrix f).block_triangular id :=
λ i j, gram_schmidt_orthonormal_basis'_inv_triangular' h f

lemma gram_schmidt_orthonormal_basis'_det :
  (gram_schmidt_orthonormal_basis' h f).to_basis.det f
  = ∏ i, ⟪gram_schmidt_orthonormal_basis' h f i, f i⟫ :=
begin
  convert matrix.det_of_upper_triangular (gram_schmidt_orthonormal_basis'_inv_block_triangular h f),
  ext i,
  exact ((gram_schmidt_orthonormal_basis' h f).repr_apply_apply (f i) i).symm,
end
