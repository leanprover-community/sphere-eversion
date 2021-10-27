import analysis.convex.hull
import data.real.basic
import topology.connected
import topology.path_connected
import topology.algebra.affine
import linear_algebra.dimension
import data.matrix.notation
import ..to_mathlib.topology.algebra.instances

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

lemma continuous_line_map [topological_add_group F] [has_continuous_smul ℝ F] (a b : F) : 
  continuous (line_map a b : ℝ → F) := 
begin
  change continuous (λ x, line_map a b x),
  conv {congr, funext, rw line_map_apply_module},
  continuity
end

lemma segment_eq_image_line_map {a b : F} : [a -[ℝ] b] = line_map a b '' unit_interval :=
begin
  convert segment_eq_image ℝ a b,
  ext,
  exact line_map_apply_module _ _ _
end

lemma convex.is_path_connected' [topological_add_group F] [has_continuous_smul ℝ F] {s : set F} 
  (hconv : convex ℝ s) (hne : s.nonempty) :
  is_path_connected s :=
begin
  refine is_path_connected_iff.mpr ⟨hne, _⟩,
  intros x y x_in y_in,
  have H := hconv.segment_subset x_in y_in,
  rw segment_eq_image_line_map at H,
  exact joined_in.of_line (continuous_line_map x y).continuous_on (line_map_apply_zero _ _) 
    (line_map_apply_one _ _) H
end

instance foo [topological_add_group F] [has_continuous_smul ℝ F] : path_connected_space F :=
path_connected_space_iff_univ.mpr $ convex_univ.is_path_connected' ⟨(0 : F), trivial⟩

local notation `π` := submodule.linear_proj_of_is_compl _ _

def continuous_map.prod_mk {α β₁ β₂ : Type*} [topological_space α] [topological_space β₁] 
  [topological_space β₂] (f : C(α, β₁)) (g : C(α, β₂)) : 
  C(α, β₁ × β₂) :=
{ to_fun := (λ x, (f x, g x)),
  continuous_to_fun := continuous.prod_mk f.continuous g.continuous }

def continuous_map.prod_map {α₁ α₂ β₁ β₂ : Type*} [topological_space α₁] [topological_space α₂] 
  [topological_space β₁] [topological_space β₂] (f : C(α₁, α₂)) (g : C(β₁, β₂)) : 
  C(α₁ × β₁, α₂ × β₂) :=
{ to_fun := prod.map f g,
  continuous_to_fun := continuous.prod_map f.continuous g.continuous }

noncomputable def path.prod {α β : Type*} [topological_space α] [topological_space β] 
  {x₁ y₁ : α} {x₂ y₂ : β} (γ₁ : path x₁ y₁) (γ₂ : path x₂ y₂) :  path (x₁, x₂) (y₁, y₂) :=
{ to_continuous_map := continuous_map.prod_mk γ₁.to_continuous_map γ₂.to_continuous_map,
  source' := by dsimp [continuous_map.prod_mk]; rwa [γ₁.source, γ₂.source],
  target' := by dsimp [continuous_map.prod_mk]; rwa [γ₁.target, γ₂.target] }

noncomputable def path.add [topological_add_group F] {x₁ x₂ y₁ y₂ : F} (γ₁ : path x₁ y₁) 
  (γ₂ : path x₂ y₂) : path (x₁ + x₂) (y₁ + y₂) :=
(γ₁.prod γ₂).map continuous_add

lemma path.add_apply [topological_add_group F] {x₁ x₂ y₁ y₂ : F} (γ₁ : path x₁ y₁) 
  (γ₂ : path x₂ y₂) (t : unit_interval) : (γ₁.add γ₂) t = γ₁ t + γ₂ t := rfl

lemma submodule.eq_linear_proj_add_linear_proj_of_is_compl {p q : submodule ℝ F} 
  (hpq : is_compl p q) (x : F) : 
  x = π hpq x + π hpq.symm x :=
begin
  rcases submodule.exists_unique_add_of_is_compl hpq x with ⟨u, v, rfl, -⟩,
  simp only [ linear_map.map_add, add_zero, submodule.linear_proj_of_is_compl_apply_right, 
              zero_add, submodule.linear_proj_of_is_compl_apply_left ],
end

lemma submodule.not_mem_of_is_compl_of_ne_zero {p q : submodule ℝ F} (hpq : is_compl p q)
  {a : p} (ha : a ≠ 0) : (a : F) ∉ q :=
begin
  intro h,
  have h' : (a : F) ∈ p := submodule.coe_mem a,
  have h'' : (a : F) ∈ p ⊓ q := submodule.mem_inf.mpr ⟨h', h⟩,
  rw [hpq.inf_eq_bot, submodule.mem_bot, submodule.coe_eq_zero] at h'',
  exact ha h''
end

--lemma submodule.linear_proj_add_linear_proj_eq_id_of_is_compl {p q : submodule ℝ F} 
--  (hpq : is_compl p q) : p.subtype.comp (π hpq) + q.subtype.comp (π hpq.symm) = linear_map.id :=
--begin
--  ext x,
--  exact submodule.
--end

--lemma joined_in_of_is_compl [topological_add_group F] {p q : submodule ℝ F} (hpq : is_compl p q) 
--  (x y : F) (S : set F) (hp : joined_in (p.subtype ⁻¹' S) (π hpq x) (π hpq y)) 
--  (hq : joined_in (q.subtype ⁻¹' S) (π hpq.symm x) (π hpq.symm y)) :
--  joined_in S x y :=
--begin
--  rcases hp with ⟨γ₁, hγ₁⟩,
--  rcases hq with ⟨γ₂, hγ₂⟩,
--  let γ₁' : path (_ : F) _ := γ₁.map continuous_subtype_coe,
--  let γ₂' : path (_ : F) _ := γ₂.map continuous_subtype_coe,
--  refine ⟨(γ₁'.add γ₂').cast (submodule.eq_linear_proj_add_linear_proj_of_is_compl hpq x)
--    (submodule.eq_linear_proj_add_linear_proj_of_is_compl hpq y), _⟩,
--  intro t,
--  rw [path.cast_coe, path.add_apply], 
--  sorry
--end

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
  refine joined_in.of_line (continuous_line_map _ _).continuous_on 
    (line_map_apply_zero _ _) (line_map_apply_one _ _) _,
  rw ← segment_eq_image_line_map,
  exact λ t ht (h' : t = 0), (mt (mem_span_of_zero_mem_segment hx) hy) (h' ▸ ht)
end

lemma is_path_connected_compl_zero_of_two_le_dim [topological_add_group F] [has_continuous_smul ℝ F] 
  (hdim : 2 ≤ module.rank ℝ F) : is_path_connected ({0}ᶜ : set F) :=
begin
  have fact₁ : (1 : cardinal) < 2 := by norm_num,
  have fact₀ : (0 : cardinal) < 2 := cardinal.zero_lt_one.trans fact₁,
  rw is_path_connected_iff,
  split,
  { suffices : 0 < module.rank ℝ F,
      by rwa dim_pos_iff_exists_ne_zero at this,
    exact lt_of_lt_of_le fact₀ hdim },
  { intros x y hx hy,
    by_cases h : y ∈ submodule.span ℝ ({x} : set F),
    { suffices : ∃ z, z ∉ submodule.span ℝ ({x} : set F),
      { rcases this with ⟨z, hzx⟩, 
        suffices hzy : z ∉ submodule.span ℝ ({y} : set F),
          from (joined_in_compl_zero_of_not_mem_span hx hzx).trans
            (joined_in_compl_zero_of_not_mem_span hy hzy).symm,
        rw submodule.mem_span_singleton at ⊢ hzx h,
        rcases h with ⟨a, ha⟩,
        exact λ ⟨b, hb⟩, hzx ⟨b * a, by rwa [mul_smul, ha]⟩ },
      by_contra h',
      push_neg at h',
      rw ← submodule.eq_top_iff' at h',
      rw [← dim_top ℝ, ← h'] at hdim,
      suffices : (2 : cardinal) ≤ 1,
        from not_le_of_lt fact₁ this,
      have := hdim.trans (dim_span_le _),
      rwa cardinal.mk_singleton at this },
    { exact joined_in_compl_zero_of_not_mem_span hx h } }
end

lemma is_path_connected_compl_of_two_le_codim [topological_add_group F] [has_continuous_smul ℝ F] 
  {E : submodule ℝ F} (hcodim : 2 ≤ module.rank ℝ E.quotient) : 
  is_path_connected (Eᶜ : set F) := 
begin
  rcases E.exists_is_compl with ⟨E', hE'⟩,  
  refine is_path_connected_compl_of_is_path_connected_compl_zero hE'.symm _,
  refine is_path_connected_compl_zero_of_two_le_dim _,
  rwa ← (E.quotient_equiv_of_is_compl E' hE').dim_eq
end

--lemma is_path_connected_compl_of_two_le_codim [topological_add_group F] [has_continuous_smul ℝ F] 
--  {E : submodule ℝ F} (hcodim : 2 ≤ module.rank ℝ E.quotient) : 
--  is_path_connected (Eᶜ : set F) := 
--begin
--  rcases E.exists_is_compl with ⟨E', hE'⟩,
--  rw is_path_connected_iff,
--  split,
--  { rw set.nonempty_compl,
--    intro h,
--    sorry },
--  { haveI : topological_add_group E := sorry,
--    haveI : has_continuous_smul ℝ E := sorry,
--    haveI : topological_add_group E' := sorry,
--    haveI : has_continuous_smul ℝ E' := sorry,
--    intros x y hx hy,
--    suffices : joined_in ({0}ᶜ : set E') (π hE'.symm x) (π hE'.symm y),
--    { rcases this with ⟨γ₁, hγ₁⟩,
--      let γ₂ := path_connected_space.some_path (π hE' x) (π hE' y),
--      let γ₁' : path (_ : F) _ := γ₁.map continuous_subtype_coe,
--      let γ₂' : path (_ : F) _ := γ₂.map continuous_subtype_coe,
--      refine ⟨(γ₁'.add γ₂').cast (submodule.eq_linear_proj_add_linear_proj_of_is_compl hE'.symm x)
--        (submodule.eq_linear_proj_add_linear_proj_of_is_compl hE'.symm y), _⟩,
--      intros t ht,
--      rw [path.cast_coe, path.add_apply] at ht,
--      change (γ₁ t : F) + γ₂ t ∈ E at ht,
--      rw [← submodule.linear_proj_of_is_compl_apply_eq_zero_iff hE'.symm, linear_map.map_add,
--          submodule.linear_proj_of_is_compl_apply_right hE'.symm, add_zero, 
--          submodule.linear_proj_of_is_compl_apply_eq_zero_iff hE'.symm] at ht,
--      have ht' : (γ₁ t : F) ∈ E' := submodule.coe_mem (γ₁ t),
--      have ht : (γ₁ t : F) ∈ E ⊓ E' := submodule.mem_inf.mpr ⟨ht, ht'⟩,
--      rw hE'.inf_eq_bot at ht,
--      change γ₁ t = 0 at ht, } }
--end

--lemma is_path_connected_compl_of_two_le_codim [topological_add_group F] [has_continuous_smul ℝ F] 
--  {E : submodule ℝ F} (hcodim : 2 ≤ module.rank ℝ E.quotient) : 
--  is_path_connected (Eᶜ : set F) := 
--begin
--  rcases E.exists_is_compl with ⟨E', hE'⟩,
--  rw is_path_connected_iff,
--  split,
--  { rw set.nonempty_compl,
--    intro h,
--    sorry },
--  { intros x y hx hy,
--    rcases submodule.exists_unique_add_of_is_compl hE' x with ⟨u, u', huu', -⟩,
--    rcases submodule.exists_unique_add_of_is_compl hE' y with ⟨v, v', hvv', -⟩,
--    have : u' ≠ 0,
--    { intro h,
--      rw h at huu',
--      rw [submodule.coe_zero, add_zero] at huu',
--      rw ← huu' at hx,
--      exact hx u.2 },
--    have : v' ≠ 0,
--    { intro h,
--      rw h at hvv',
--      rw [submodule.coe_zero, add_zero] at hvv',
--      rw ← hvv' at hy,
--      exact hy v.2 },
--    suffices : joined_in (Eᶜ : set F) (u' : F) (v' : F),
--    { refine joined_in.trans _ (this.trans _);
--      { refine joined_in.of_line line_map_continuous.continuous_on 
--          (line_map_apply_zero _ _) (line_map_apply_one _ _) _,
--        rw ← segment_eq_image_line_map,
--        intros x hx, }, },
--    by_cases hz : (0 : F) ∈ [x -[ℝ] y], }
--end

end lemma_2_13