import linear_algebra.affine_space.affine_map
import analysis.normed_space.basic

open affine_map

-- TODO Drop this lemma once bump Mathlib since it contains
-- https://github.com/leanprover-community/mathlib/pull/9360
@[simp] lemma affine_map.homothety_apply_same
  {k V P : Type*} [comm_ring k] [add_comm_group V] [module k V] [add_torsor V P]
  (c : P) (r : k) : homothety c r c = c :=
line_map_same_apply c r

variables {E : Type*} [normed_group E] [normed_space ℝ E]

lemma exists_homothety_mem_of_mem_interior (x : E) {s : set E} {y : E} (hy : y ∈ interior s) :
  ∃ ε > (0 : ℝ), ∀ (δ : ℝ), ∥δ∥ < ε → homothety x (1 + δ) y ∈ s :=
begin
  cases eq_or_ne y x with h h, { use 1, simp [h.symm, interior_subset hy], },
  have hxy : 0 < ∥y - x∥, { rwa [norm_pos_iff, sub_ne_zero], },
  obtain ⟨u, hu₁, hu₂, hu₃⟩ := mem_interior.mp hy,
  obtain ⟨ε, hε, hyε⟩ := metric.is_open_iff.mp hu₂ y hu₃,
  refine ⟨ε / ∥y - x∥, div_pos hε hxy, _⟩,
  intros δ hδ,
  apply hu₁,
  apply hyε,
  simp [homothety_apply, dist_eq_norm, norm_smul, ε.norm_eq_abs, (lt_div_iff hxy).mp hδ,
    abs_of_pos hε],
end

lemma homothety_image_subset_of_open
  (x : E) {s : set E} (hs : is_open s) {t : finset E} (h : ↑t ⊆ s) :
  ∃ ε > (0 : ℝ), homothety x (1 + ε) '' t ⊆ s :=
begin
  rcases t.eq_empty_or_nonempty with rfl | hne, { use 1, simp, },
  have h' : ∀ (y : t), ↑y ∈ interior s, { rw interior_eq_iff_open.mpr hs, exact λ y, h y.property },
  let f : t → ℝ := λ y, classical.some (exists_homothety_mem_of_mem_interior x (h' y)),
  let ft := finset.image f finset.univ,
  have ftne : ft.nonempty, { simp [hne] },
  let ε := ft.min' ftne,
  use ε / 2,
  let f_spec := λ y, classical.some_spec (exists_homothety_mem_of_mem_interior x (h' y)),
  obtain ⟨y, -, hy⟩ := finset.mem_image.mp (ft.min'_mem ftne),
  have hy' : 0 < f y, { exact (exists_prop.mp (f_spec y)).1, },
  change f y = ε at hy,
  rw ← hy,
  refine ⟨half_pos hy', _⟩,
  rw set.image_subset_iff,
  intros z hz,
  rw set.mem_preimage,
  apply (exists_prop.mp (f_spec ⟨z, hz⟩)).2,
  change _ < f ⟨z, hz⟩,
  suffices : f y ≤ f ⟨z, hz⟩,
  { rw [normed_field.norm_div, real.norm_two, real.norm_eq_abs, abs_of_pos hy'],
    exact lt_of_lt_of_le (half_lt_self hy') this, },
  rw hy,
  apply ft.min'_le,
  simp,
end
