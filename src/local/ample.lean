import analysis.convex.hull
import data.real.basic
import topology.connected
import topology.path_connected
import topology.algebra.affine
import linear_algebra.dimension
import linear_algebra.affine_space.midpoint
import data.matrix.notation
import analysis.convex.topology

import to_mathlib.topology.misc

/-!
# Ample subsets of real vector spaces

In this file we study ample set in real vector spaces. A set is ample if all its connected
component have full convex hull. We then prove this property is invariant under a number of affine
geometric operations.

As trivial examples, the empty set and the univ set are ample. After proving those fact,
the second part of the file proves that a linear subspace with codimension at least 2 has a
ample complement. This is the crucial geometric ingredient which allows to apply convex integration
to the theory of immersions in positive codimension.

All vector spaces in the file (and more generally in this folder) are real vector spaces.

## Implementation notes

The definition of ample subset asks for a vector space structure and a topology on the ambiant type
without any link between those structures, but we will only be using these for finite dimensional
vector spaces with their natural topology.
-/


/-! ## Definition and invariance -/
open set affine_map

open_locale convex matrix

variables {E F : Type*} [add_comm_group F] [module ℝ F] [topological_space F]
variables [add_comm_group E] [module ℝ E] [topological_space E]

/-- A subset of a topological real vector space is ample if the convex hull of each of its
connected components is the full space. -/
def ample_set (s : set F) : Prop :=
∀ x ∈ s, convex_hull ℝ (connected_component_in s x) = univ

/-- images of ample sets under continuous linear equivalences are ample. -/
lemma ample_set.image {s : set E} (h : ample_set s) (L : E ≃L[ℝ] F) : ample_set (L '' s) :=
begin
  intros x hx,
  rw [L.image_eq_preimage] at hx,
  have : L '' connected_component_in s (L.symm x) = connected_component_in (L '' s) x,
  { conv_rhs { rw [← L.apply_symm_apply x] },
    exact L.to_homeomorph.image_connected_component_in hx },
  rw [← this],
  refine (L.to_linear_equiv.to_linear_map.convex_hull_image _).trans _,
  rw [h (L.symm x) hx, image_univ],
  exact L.to_linear_equiv.to_equiv.range_eq_univ,
end

/-- preimages of ample sets under continuous linear equivalences are ample. -/
lemma ample_set.preimage {s : set F} (h : ample_set s) (L : E ≃L[ℝ] F) : ample_set (L ⁻¹' s) :=
by { rw [← L.image_symm_eq_preimage], exact h.image L.symm }

open_locale pointwise
/-- Translating a ample set is ample.
We basically mimic `ample_set.image`. We could prove the common generalization using
continuous affine equivalences -/
lemma ample_set.vadd [has_continuous_add E] {s : set E} (h : ample_set s) {y : E} :
  ample_set (y +ᵥ s) :=
begin
  intros x hx,
  simp_rw [mem_vadd_set] at hx,
  obtain ⟨x, hx, rfl⟩ := hx,
  have : y +ᵥ connected_component_in s x = connected_component_in (y +ᵥ s) (y +ᵥ x),
  { exact (homeomorph.add_left y).image_connected_component_in hx },
  rw [← this],
  refine ((affine_equiv.const_vadd ℝ E y).to_affine_map.image_convex_hull _).symm.trans _,
  rw [h x hx, image_univ],
  exact (affine_equiv.to_equiv _).range_eq_univ,
end

/-! ## Trivial examples -/

/-- A whole vector space is ample. -/
lemma ample_set_univ {F : Type*} [normed_add_comm_group F] [normed_space ℝ F] :
  ample_set (univ : set F) :=
begin
  intros x _,
  rw [connected_component_in_univ, preconnected_space.connected_component_eq_univ, convex_hull_univ]
end

/-- The empty set in a vector space is ample. -/
lemma ample_set_empty {F : Type*} [add_comm_group F] [module ℝ F] [topological_space F] :
  ample_set (∅ : set F) :=
λ _ h, false.elim h

/-! ## Codimension at least 2 subspaces have ample complement. -/

section lemma_2_13

local notation `π` := submodule.linear_proj_of_is_compl _ _
local attribute [instance, priority 100] topological_add_group.path_connected

/-- Given two complementary subspaces `p` and `q` in `F`, if the complement of `{0}`
is path connected in `p` then the complement of `q` is path connected in `F`. -/
lemma is_path_connected_compl_of_is_path_connected_compl_zero [topological_add_group F]
  [has_continuous_smul ℝ F] {p q : submodule ℝ F} (hpq : is_compl p q)
  (hpc : is_path_connected ({0}ᶜ : set p)) : is_path_connected (qᶜ : set F) :=
begin
  rw is_path_connected_iff at ⊢ hpc,
  split,
  { rcases hpc.1 with ⟨a, ha⟩,
    exact ⟨a, mt (submodule.eq_zero_of_coe_mem_of_disjoint hpq.disjoint) ha⟩ },
  { intros x hx y hy,
    have : π hpq x ≠ 0 ∧ π hpq y ≠ 0,
    { split;
      intro h;
      rw submodule.linear_proj_of_is_compl_apply_eq_zero_iff hpq at h;
      [exact hx h, exact hy h] },
    rcases hpc.2 (π hpq x) this.1 (π hpq y) this.2 with ⟨γ₁, hγ₁⟩,
    let γ₂ := path_connected_space.some_path (π hpq.symm x) (π hpq.symm y),
    let γ₁' : path (_ : F) _ := γ₁.map continuous_subtype_coe,
    let γ₂' : path (_ : F) _ := γ₂.map continuous_subtype_coe,
    refine ⟨(γ₁'.add γ₂').cast
      (submodule.linear_proj_add_linear_proj_of_is_compl_eq_self hpq x).symm
      (submodule.linear_proj_add_linear_proj_of_is_compl_eq_self hpq y).symm, _⟩,
    intros t,
    rw [path.cast_coe, path.add_apply],
    change (γ₁ t : F) + (γ₂ t : F) ∉ q,
    rw [← submodule.linear_proj_of_is_compl_apply_eq_zero_iff hpq, linear_map.map_add,
        submodule.linear_proj_of_is_compl_apply_right hpq, add_zero,
        submodule.linear_proj_of_is_compl_apply_eq_zero_iff hpq],
    exact mt (submodule.eq_zero_of_coe_mem_of_disjoint hpq.disjoint) (hγ₁ t) }
end

/-- For `x` and `y` in a real vector space, if `x ≠ 0` and `0` is in the segment from
`x` to `y` then `y` is on the line spanned by `x`.  -/
lemma mem_span_of_zero_mem_segment {x y : F} (hx : x ≠ 0) (h : (0 : F) ∈ [x -[ℝ] y]) :
  y ∈ submodule.span ℝ ({x} : set F) :=
begin
  rw segment_eq_image at h,
  rcases h with ⟨t, ht, htxy⟩,
  rw submodule.mem_span_singleton,
  dsimp only at htxy,
  use (t-1)/t,
  have : t ≠ 0,
  { intro h,
    rw h at htxy,
    refine hx _,
    simpa using htxy },
  rw [← smul_eq_zero_iff_eq' (neg_ne_zero.mpr $ inv_ne_zero this),
      smul_add, smul_smul, smul_smul, ← neg_one_mul, mul_assoc, mul_assoc,
      inv_mul_cancel this, mul_one, neg_one_smul, add_neg_eq_zero] at htxy,
  convert htxy,
  ring
end

variables [topological_add_group F] [has_continuous_smul ℝ F]

/-- For `x` and `y` in a real vector space, if `x ≠ 0` and `y` is not on the line
spanned by `x` then `x` and `y` can be joined by a path in the complement of `{0}`.  -/
lemma joined_in_compl_zero_of_not_mem_span
  {x y : F} (hx : x ≠ 0) (hy : y ∉ submodule.span ℝ ({x} : set F)) :
  joined_in ({0}ᶜ : set F) x y :=
begin
  refine joined_in.of_line line_map_continuous.continuous_on
    (line_map_apply_zero _ _) (line_map_apply_one _ _) _,
  rw ← segment_eq_image_line_map,
  exact λ t ht (h' : t = 0), (mt (mem_span_of_zero_mem_segment hx) hy) (h' ▸ ht)
end

/-- In a vector space whose dimension is at least 2, the complement of
`{0}` is ample. -/
lemma is_path_connected_compl_zero_of_two_le_dim
  (hdim : 2 ≤ module.rank ℝ F) : is_path_connected ({0}ᶜ : set F) :=
begin
  rw is_path_connected_iff,
  split,
  { suffices : 0 < module.rank ℝ F,
      by rwa dim_pos_iff_exists_ne_zero at this,
    exact lt_of_lt_of_le (by norm_num) hdim },
  { intros x hx y hy,
    by_cases h : y ∈ submodule.span ℝ ({x} : set F),
    { suffices : ∃ z, z ∉ submodule.span ℝ ({x} : set F),
      { rcases this with ⟨z, hzx⟩,
        have hzy : z ∉ submodule.span ℝ ({y} : set F),
          from λ h', hzx (submodule.mem_span_singleton_trans h' h),
        exact (joined_in_compl_zero_of_not_mem_span hx hzx).trans
          (joined_in_compl_zero_of_not_mem_span hy hzy).symm },
      by_contra h',
      push_neg at h',
      rw ← submodule.eq_top_iff' at h',
      rw [← dim_top ℝ, ← h'] at hdim,
      suffices : (2 : cardinal) ≤ 1,
        from not_le_of_lt (by norm_num) this,
      have := hdim.trans (dim_span_le _),
      rwa cardinal.mk_singleton at this },
    { exact joined_in_compl_zero_of_not_mem_span hx h } }
end

/-- Let `E` be a linear subspace in a real vector space. If `E` has codimension at
least two then its complement is path-connected. -/
lemma is_path_connected_compl_of_two_le_codim
  {E : submodule ℝ F} (hcodim : 2 ≤ module.rank ℝ (F⧸E)) :
  is_path_connected (Eᶜ : set F) :=
begin
  rcases E.exists_is_compl with ⟨E', hE'⟩,
  refine is_path_connected_compl_of_is_path_connected_compl_zero hE'.symm _,
  refine is_path_connected_compl_zero_of_two_le_dim _,
  rwa ← (E.quotient_equiv_of_is_compl E' hE').dim_eq
end

/-- Let `E` be a linear subspace in a real vector space. If `E` has codimension at
least two then its complement is connected. -/
lemma is_connected_compl_of_two_le_codim
  {E : submodule ℝ F} (hcodim : 2 ≤ module.rank ℝ (F⧸E)) :
  is_connected (Eᶜ : set F) :=
(is_path_connected_compl_of_two_le_codim hcodim).is_connected

/-- Let `E` be a linear subspace in a real vector space. If `E` has codimension at
least two then its complement is a path-connected space. -/
lemma connected_space_compl_of_two_le_codim
  {E : submodule ℝ F} (hcodim : 2 ≤ module.rank ℝ (F⧸E)) :
  connected_space (Eᶜ : set F) :=
is_connected_iff_connected_space.mp (is_connected_compl_of_two_le_codim hcodim)

lemma submodule.connected_component_in_eq_self_of_two_le_codim (E : submodule ℝ F)
  (hcodim : 2 ≤ module.rank ℝ (F⧸E)) {x : F} (hx : x ∉ E) :
  connected_component_in (E : set F)ᶜ x = Eᶜ :=
is_preconnected.connected_component_in (is_connected_compl_of_two_le_codim hcodim).2 hx

/-- Let `E` be a linear subspace in a real vector space. If `E` has codimension at
least two then its complement is ample. -/
lemma ample_of_two_le_codim [topological_add_group F] [has_continuous_smul ℝ F]
  {E : submodule ℝ F} (hcodim : 2 ≤ module.rank ℝ (F⧸E)) :
  ample_set (Eᶜ : set F) :=
begin
  haveI : connected_space (Eᶜ : set F) := connected_space_compl_of_two_le_codim hcodim,
  intros x hx,
  rw [E.connected_component_in_eq_self_of_two_le_codim hcodim hx, eq_univ_iff_forall],
  intro y,
  by_cases h : y ∈ E,
  { rcases E.exists_is_compl with ⟨E', hE'⟩,
    rw (E.quotient_equiv_of_is_compl E' hE').dim_eq at hcodim,
    have hcodim' : 0 < module.rank ℝ E' := lt_of_lt_of_le (by norm_num) hcodim,
    rw dim_pos_iff_exists_ne_zero at hcodim',
    rcases hcodim' with ⟨z, hz⟩,
    have : y ∈ [y+(-z) -[ℝ] y+z],
    { rw ← sub_eq_add_neg,
      exact mem_segment_sub_add y z },
    refine (convex_convex_hull ℝ (Eᶜ : set F)).segment_subset _ _ this ;
    refine subset_convex_hull ℝ (Eᶜ : set F) _;
    change _ ∉ E;
    rw submodule.add_mem_iff_right _ h;
    try {rw submodule.neg_mem_iff};
    exact mt (submodule.eq_zero_of_coe_mem_of_disjoint hE'.symm.disjoint) hz },
  { exact subset_convex_hull ℝ (Eᶜ : set F) h }
end

end lemma_2_13
