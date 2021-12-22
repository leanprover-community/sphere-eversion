import linear_algebra.affine_space.affine_map
import analysis.normed_space.basic

open affine_map

variables {E : Type*} [normed_group E] [normed_space ℝ E]

notation `|`x`|` := abs x

lemma exists_homothety_mem_of_mem_interior (x : E) {s : set E} {y : E} (hy : y ∈ interior s) :
  ∃ ε > (0 : ℝ), ∀ (δ : ℝ), |δ| < ε → homothety x (1 + δ) y ∈ s :=
begin
  cases eq_or_ne y x with h h, { use 1, simp [h.symm, interior_subset hy], },
  have hxy : 0 < ∥y - x∥, { rwa [norm_pos_iff, sub_ne_zero], },
  obtain ⟨u, hu₁, hu₂, hu₃⟩ := mem_interior.mp hy,
  obtain ⟨ε, hε, hyε⟩ := metric.is_open_iff.mp hu₂ y hu₃,
  refine ⟨ε / ∥y - x∥, div_pos hε hxy, _⟩,
  intros δ hδ,
  apply hu₁,
  apply hyε,
  simp [homothety_apply, dist_eq_norm, norm_smul, real.norm_eq_abs, (lt_div_iff hxy).mp hδ,
    abs_of_pos hε],
end

lemma homothety_image_subset_of_open
  (x : E) {s : set E} (hs : is_open s) {t : set E} (h : t ⊆ s) (ht : t.finite) :
  ∃ ε > (0 : ℝ), homothety x (1 + ε) '' t ⊆ s :=
begin
  rcases t.eq_empty_or_nonempty with rfl | hne, { use 1, simp, },
  haveI : fintype t := ht.fintype,
  rw [← t.nonempty_coe_sort, ← finset.univ_nonempty_iff] at hne,
  have h' : ∀ y : t, (y : E) ∈ interior s,
  { rw interior_eq_iff_open.mpr hs,
    exact λ y, h y.property },
  choose f f_pos hf using λ y, exists_homothety_mem_of_mem_interior x (h' y),
  let ft : finset ℝ := finset.image f finset.univ,
  have ftne : ft.nonempty, by simp [hne],
  let ε := ft.min' ftne,
  use ε / 2,
  obtain ⟨y, -, hy : f y = ε⟩ := finset.mem_image.mp (ft.min'_mem ftne),
  have hε : 0 < ε := hy ▸ f_pos y,
  refine ⟨half_pos hε, _⟩,
  rw set.image_subset_iff,
  intros z hz,
  apply hf ⟨z, hz⟩,
  calc abs (ε / 2) = ε / 2 : abs_of_pos (half_pos hε)
   ... < ε : half_lt_self hε
   ... ≤ f ⟨z, hz⟩ : ft.min'_le (f ⟨z, hz⟩) (finset.mem_image.mpr ⟨⟨z, hz⟩, finset.mem_univ _, rfl⟩)
end
