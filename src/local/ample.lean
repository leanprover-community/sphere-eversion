import analysis.convex.hull
import data.real.basic
import topology.connected
import topology.path_connected
import topology.algebra.affine
import linear_algebra.dimension
import linear_algebra.affine_space.midpoint
import data.matrix.notation
import analysis.convex.topology

/-!
# Ample subsets of real vector spaces

## Implementation notes

The definition of ample subset asks for a vector space structure and a topology on the ambiant type
without any link between those structures, but we will only be using these for finite dimensional
vector spaces with their natural topology.
-/

open set affine_map

open_locale convex matrix

variables {F : Type*} [add_comm_group F] [module ℝ F] [topological_space F]

/-- A subset of a topological real vector space is ample if the convex hull of each of its 
connected components is the full space. -/
def ample_set (s : set F) := 
∀ x : s, convex_hull ℝ (subtype.val '' (connected_component x)) = univ

section lemma_2_13

local notation `π` := submodule.linear_proj_of_is_compl _ _

-- #10709
lemma submodule.eq_linear_proj_add_linear_proj_of_is_compl {p q : submodule ℝ F} 
  (hpq : is_compl p q) (x : F) : 
  x = π hpq x + π hpq.symm x :=
begin
  rcases submodule.exists_unique_add_of_is_compl hpq x with ⟨u, v, rfl, -⟩,
  simp only [ linear_map.map_add, add_zero, submodule.linear_proj_of_is_compl_apply_right, 
              zero_add, submodule.linear_proj_of_is_compl_apply_left ],
end

-- #10709
lemma submodule.not_mem_of_is_compl_of_ne_zero {p q : submodule ℝ F} (hpq : is_compl p q)
  {a : p} (ha : a ≠ 0) : (a : F) ∉ q :=
begin
  intro h,
  have h' : (a : F) ∈ p := submodule.coe_mem a,
  have h'' : (a : F) ∈ p ⊓ q := submodule.mem_inf.mpr ⟨h', h⟩,
  rw [hpq.inf_eq_bot, submodule.mem_bot, submodule.coe_eq_zero] at h'',
  exact ha h''
end

lemma is_path_connected_compl_of_is_path_connected_compl_zero [topological_add_group F] 
  [has_continuous_smul ℝ F] {p q : submodule ℝ F} (hpq : is_compl p q) 
  (hpc : is_path_connected ({0}ᶜ : set p)) : is_path_connected (qᶜ : set F) :=
begin
  rw is_path_connected_iff at ⊢ hpc,
  split,
  { rcases hpc.1 with ⟨a, ha⟩,
    exact ⟨a, submodule.not_mem_of_is_compl_of_ne_zero hpq ha⟩ },
  { intros x y hx hy, 
    have : π hpq x ≠ 0 ∧ π hpq y ≠ 0,
    { split;
      intro h;
      rw submodule.linear_proj_of_is_compl_apply_eq_zero_iff hpq at h;
      [exact hx h, exact hy h] },
    rcases hpc.2 (π hpq x) (π hpq y) this.1 this.2 with ⟨γ₁, hγ₁⟩,
    let γ₂ := path_connected_space.some_path (π hpq.symm x) (π hpq.symm y),
    let γ₁' : path (_ : F) _ := γ₁.map continuous_subtype_coe,
    let γ₂' : path (_ : F) _ := γ₂.map continuous_subtype_coe,
    refine ⟨(γ₁'.add γ₂').cast (submodule.eq_linear_proj_add_linear_proj_of_is_compl hpq x)
      (submodule.eq_linear_proj_add_linear_proj_of_is_compl hpq y), _⟩,
    intros t,
    rw [path.cast_coe, path.add_apply],
    change (γ₁ t : F) + (γ₂ t : F) ∉ q,
    rw [← submodule.linear_proj_of_is_compl_apply_eq_zero_iff hpq, linear_map.map_add,
        submodule.linear_proj_of_is_compl_apply_right hpq, add_zero, 
        submodule.linear_proj_of_is_compl_apply_eq_zero_iff hpq],
    exact submodule.not_mem_of_is_compl_of_ne_zero hpq (hγ₁ t) }
end

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

lemma joined_in_compl_zero_of_not_mem_span [topological_add_group F] [has_continuous_smul ℝ F] 
  {x y : F} (hx : x ≠ 0) (hy : y ∉ submodule.span ℝ ({x} : set F)) : 
  joined_in ({0}ᶜ : set F) x y :=
begin
  refine joined_in.of_line line_map_continuous.continuous_on 
    (line_map_apply_zero _ _) (line_map_apply_one _ _) _,
  rw ← segment_eq_image_line_map,
  exact λ t ht (h' : t = 0), (mt (mem_span_of_zero_mem_segment hx) hy) (h' ▸ ht)
end

-- #10943
lemma submodule.mem_span_trans {x y z : F} (hxy : x ∈ submodule.span ℝ ({y} : set F)) 
  (hyz : y ∈ submodule.span ℝ ({z} : set F)) :
  x ∈ submodule.span ℝ ({z} : set F) :=
begin
  rw [← set_like.mem_coe, ← singleton_subset_iff] at *,
  exact submodule.subset_span_trans hxy hyz
end

lemma is_path_connected_compl_zero_of_two_le_dim [topological_add_group F] [has_continuous_smul ℝ F] 
  (hdim : 2 ≤ module.rank ℝ F) : is_path_connected ({0}ᶜ : set F) :=
begin
  rw is_path_connected_iff,
  split,
  { suffices : 0 < module.rank ℝ F,
      by rwa dim_pos_iff_exists_ne_zero at this,
    exact lt_of_lt_of_le (by norm_num) hdim },
  { intros x y hx hy,
    by_cases h : y ∈ submodule.span ℝ ({x} : set F),
    { suffices : ∃ z, z ∉ submodule.span ℝ ({x} : set F),
      { rcases this with ⟨z, hzx⟩, 
        have hzy : z ∉ submodule.span ℝ ({y} : set F),
          from λ h', hzx (submodule.mem_span_trans h' h),
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

lemma is_path_connected_compl_of_two_le_codim [topological_add_group F] [has_continuous_smul ℝ F] 
  {E : submodule ℝ F} (hcodim : 2 ≤ module.rank ℝ (F⧸E)) : 
  is_path_connected (Eᶜ : set F) := 
begin
  rcases E.exists_is_compl with ⟨E', hE'⟩,
  refine is_path_connected_compl_of_is_path_connected_compl_zero hE'.symm _,
  refine is_path_connected_compl_zero_of_two_le_dim _,
  rwa ← (E.quotient_equiv_of_is_compl E' hE').dim_eq
end

lemma is_connected_compl_of_two_le_codim [topological_add_group F] [has_continuous_smul ℝ F] 
  {E : submodule ℝ F} (hcodim : 2 ≤ module.rank ℝ (F⧸E)) : 
  is_connected (Eᶜ : set F) := 
(is_path_connected_compl_of_two_le_codim hcodim).is_connected

lemma connected_space_compl_of_two_le_codim [topological_add_group F] [has_continuous_smul ℝ F] 
  {E : submodule ℝ F} (hcodim : 2 ≤ module.rank ℝ (F⧸E)) : 
  connected_space (Eᶜ : set F) := 
is_connected_iff_connected_space.mp (is_connected_compl_of_two_le_codim hcodim)

lemma ample_of_two_le_codim [topological_add_group F] [has_continuous_smul ℝ F] 
  {E : submodule ℝ F} (hcodim : 2 ≤ module.rank ℝ (F⧸E)) : 
  ample_set (Eᶜ : set F) := 
begin
  haveI : connected_space (Eᶜ : set F) := connected_space_compl_of_two_le_codim hcodim,
  intro x,
  rw [preconnected_space.connected_component_eq_univ, image_univ, subtype.range_val, 
      eq_univ_iff_forall],
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
    refine (convex_convex_hull ℝ (Eᶜ : set F)).segment_subset _ _ this;
    refine subset_convex_hull ℝ (Eᶜ : set F) _;
    change _ ∉ E; 
    rw submodule.add_mem_iff_right _ h;
    try {rw submodule.neg_mem_iff};
    exact submodule.not_mem_of_is_compl_of_ne_zero hE'.symm hz },
  { exact subset_convex_hull ℝ (Eᶜ : set F) h }
end

end lemma_2_13