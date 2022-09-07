import to_mathlib.geometry.manifold.sphere
-- import global.twist_one_jet_sec
import local.parametric_h_principle
import global.rotation
import interactive_expr
set_option trace.filter_inst_type true

/-!
This is a stop-gap file to prove sphere eversion from the local verson of the h-principle.
Contents:
relation of immersions
formal solution of sphere eversion
sphere eversion
-/
noncomputable theory

open metric finite_dimensional set function rel_loc
open_locale topological_space

section sphere_eversion

variables
{E : Type*} [inner_product_space ℝ E]
{E' : Type*} [inner_product_space ℝ E']
{F : Type*} [inner_product_space ℝ F]


local notation `𝕊²` := sphere (0 : E) 1
local notation (name := module_span_printing_only) `{.` x `}ᗮ` := (submodule.span ℝ {x})ᗮ
local notation `{.` x `}ᗮ` := (submodule.span ℝ ({x} : set E))ᗮ

/-- A map between vector spaces is a immersion viewed as a map on the sphere, when its
derivative at `x ∈ 𝕊²` is injective on the orthogonal complement of `x`
(the tangent space to the sphere). Note that this implies `f` is differentiable at every point
`x ∈ 𝕊²` since otherwise `D f x = 0`.
-/
def sphere_immersion (f : E → E') : Prop :=
∀ x ∈ 𝕊², inj_on (D f x) {.x}ᗮ

variables (E E')

local notation `B` := ball (0 : E) 2⁻¹

/-- The relation of immersions for unit spheres into a vector space. -/
def immersion_sphere_rel : rel_loc E E' :=
{w : one_jet E E' | w.1 ∉ B → inj_on w.2.2 {.w.1}ᗮ }

local notation `R` := immersion_sphere_rel E E'

variables {E E'}

lemma mem_loc_immersion_rel {w : one_jet E E'} :
  w ∈ immersion_sphere_rel E E' ↔ w.1 ∉ B → inj_on w.2.2 {.w.1}ᗮ :=
iff.rfl

@[simp] lemma mem_loc_immersion_rel' {x y φ} :
  (⟨x, y, φ⟩ : one_jet E E') ∈ immersion_sphere_rel E E' ↔ x ∉ B → inj_on φ  {.x}ᗮ :=
iff.rfl

lemma sphere_immersion_of_sol (f : E → E') :
  (∀ x ∈ 𝕊², (x, f x, fderiv ℝ f x) ∈ immersion_sphere_rel E E') →  sphere_immersion f :=
begin
  intros h x x_in,
  have : x ∉ B,
  { rw mem_sphere_zero_iff_norm at x_in,
    norm_num [x_in] },
  exact h x x_in this
end

variables [finite_dimensional ℝ E] [finite_dimensional ℝ E']

lemma loc_immersion_rel_open :
  is_open (immersion_sphere_rel E E') :=
begin
  sorry
  -- simp_rw [charted_space.is_open_iff HJ (immersion_rel I M I' M'), chart_at_image_immersion_rel_eq],
  -- refine λ σ, (ψJ σ).open_target.inter _,
  -- convert is_open_univ.prod continuous_linear_map.is_open_injective,
  -- { ext, simp, },
  -- { apply_instance, },
  -- { apply_instance, },
end


lemma ample_set_univ {F : Type*} [add_comm_group F] [module ℝ F] [topological_space F] :
  ample_set (univ : set F) :=
begin
  intros x _,
  convert convex_hull_univ,
  sorry
end

lemma ample_set_empty {F : Type*} [add_comm_group F] [module ℝ F] [topological_space F] :
  ample_set (∅ : set F) :=
λ _ h, false.elim h


local notation `S` := (immersion_sphere_rel E E').slice


lemma rel_loc.ample_slice_of_forall {E : Type*} [normed_add_comm_group E] [normed_space ℝ E] {F : Type*}
  [normed_add_comm_group F] [normed_space ℝ F] (Rel : rel_loc E F) {x y φ} (p : dual_pair' E)
  (h : ∀ w, (x, y, p.update φ w) ∈ Rel) : ample_set (Rel.slice p (x, y, φ)) :=
begin
  rw show Rel.slice p (x, y, φ) = univ, from eq_univ_of_forall h,
  exact ample_set_univ
end

lemma rel_loc.ample_slice_of_forall_not {E : Type*} [normed_add_comm_group E] [normed_space ℝ E] {F : Type*}
  [normed_add_comm_group F] [normed_space ℝ F] (Rel : rel_loc E F) {x y φ} (p : dual_pair' E)
  (h : ∀ w, (x, y, p.update φ w) ∉ Rel) : ample_set (Rel.slice p (x, y, φ)) :=
begin
  rw show Rel.slice p (x, y, φ) = ∅, from eq_empty_iff_forall_not_mem.mpr h,
  exact ample_set_empty
end


-- we need inj_on_update_iff (see `injective_update_iff` in dual_pair)
lemma loc_immersion_rel_ample (h : finrank ℝ E ≤ finrank ℝ E') :
  (immersion_sphere_rel E E').is_ample :=
begin
  rintro p ⟨x, y, φ⟩,
  by_cases hx : x ∈ B,
  sorry { apply rel_loc.ample_slice_of_forall,
    intros w,
    simp [hx]  },
  { by_cases H : p.π.ker = {.x}ᗮ,
    sorry { have key : ∀ w, eq_on (p.update φ w) φ {.x}ᗮ,
      { intros w x,
        rw ← H,
        exact p.update_ker_pi φ w },
      by_cases hφ : inj_on φ {.x}ᗮ,
      { apply rel_loc.ample_slice_of_forall,
        intros w hx,
        apply hφ.congr,
        exact (key w).symm  },
      { apply rel_loc.ample_slice_of_forall_not,
        intros w hx',
        apply hφ, clear hφ,
        replace hx := mem_loc_immersion_rel'.mp hx' hx, clear hx',
        apply hx.congr,
        exact key w }, },
    {
      sorry }, },
  -- exact ample_of_two_le_codim hcodim,
end


variables (E) [fact (finrank ℝ E = 3)]

/- The relation of immersion of a two-sphere into its ambient Euclidean space. -/
local notation `𝓡_imm` := immersion_sphere_rel E E

section assume_finite_dimensional

variables [finite_dimensional ℝ E] -- no way of inferring this from the `fact`

lemma is_closed_pair : is_closed ({0, 1} : set ℝ) :=
(by simp : ({0, 1} : set ℝ).finite).is_closed

lemma smooth_bs : 𝒞 ∞ (λ p : ℝ × E, ((1-p.1) • p.2 + p.1 • (-p.2) : E)) :=
begin
  sorry
  -- refine (cont_mdiff.smul _ _).add (cont_mdiff_fst.smul _),
  -- { exact (cont_diff_const.sub cont_diff_id).cont_mdiff.comp cont_mdiff_fst },
  -- { exact cont_mdiff_coe_sphere.comp cont_mdiff_snd },
  -- { exact (cont_diff_neg.cont_mdiff.comp cont_mdiff_coe_sphere).comp cont_mdiff_snd },
end

variables {E} (ω : orientation ℝ E (fin 3))

include ω
def formal_eversion_aux : htpy_jet_sec E E :=
sorry
-- family_join
--   (smooth_bs E) $
--   family_twist
--     (drop (one_jet_ext_sec ⟨(coe : 𝕊² → E), cont_mdiff_coe_sphere⟩))
--     (λ p : ℝ × 𝕊², rot_aux ω.volume_form (p.1, p.2))
--     begin
--       intros p,
--       have : smooth_at (𝓘(ℝ, ℝ × E)) 𝓘(ℝ, E →L[ℝ] E) (rot_aux ω.volume_form) (p.1, p.2),
--       { rw ← rot_eq_aux,
--         refine (cont_diff_rot ω.volume_form _).cont_mdiff_at,
--         exact ne_zero_of_mem_unit_sphere p.2 },
--       refine this.comp p (smooth.smooth_at _),
--       exact smooth_fst.prod_mk (cont_mdiff_coe_sphere.comp smooth_snd),
--     end

/-- A formal eversion of a two-sphere into its ambient Euclidean space. -/
def formal_eversion : htpy_formal_sol 𝓡_imm :=
{ is_sol := begin
    sorry
    -- intros t x,
    -- let s : tangent_space (𝓡 2) x →L[ℝ] E := mfderiv (𝓡 2) 𝓘(ℝ, E) (λ y : 𝕊², (y:E)) x,
    -- change injective (rot_aux ω.volume_form (t, x) ∘ s),
    -- have : set.univ.inj_on s,
    -- { rw ← set.injective_iff_inj_on_univ,
    --   exact mfderiv_coe_sphere_injective E x },
    -- rw set.injective_iff_inj_on_univ,
    -- refine set.inj_on.comp _ this (set.maps_to_range _ _),
    -- rw [← continuous_linear_map.range_coe, range_mfderiv_coe_sphere E, ← rot_eq_aux],
    -- exact ω.inj_on_rot t x,
  end,
  .. formal_eversion_aux ω }

lemma formal_eversion_zero (x : E) : (formal_eversion ω).f 0 x = x :=
sorry -- show (1-0 : ℝ) • (x : E) + (0 : ℝ) • (-x : E) = x, by simp

lemma formal_eversion_one (x : E) : (formal_eversion ω).f 1 x = -x :=
sorry -- show (1-1 : ℝ) • (x : E) + (1 : ℝ) • (-x : E) = -x, by simp

lemma formal_eversion_hol_at_zero {x : E} :
  (formal_eversion ω 0).is_holonomic_at x :=
begin
  sorry
  -- change mfderiv (𝓡 2) 𝓘(ℝ, E) (λ y : 𝕊², ((1:ℝ) - 0) • (y:E) + (0:ℝ) • -y) x
  --   = (rot_aux ω.volume_form (0, x)).comp (mfderiv (𝓡 2) 𝓘(ℝ, E) (λ y : 𝕊², (y:E)) x),
  -- simp only [←rot_eq_aux, rot_zero, continuous_linear_map.id_comp],
  -- congr,
  -- ext y,
  -- simp,
end

lemma formal_eversion_hol_at_one {x : E} :
  (formal_eversion ω 1).is_holonomic_at x :=
begin
  sorry
  -- change mfderiv (𝓡 2) 𝓘(ℝ, E) (λ y : 𝕊², ((1:ℝ) - 1) • (y:E) + (1:ℝ) • -y) x
  --   = (rot_aux ω.volume_form (1, x)).comp (mfderiv (𝓡 2) 𝓘(ℝ, E) (λ y : 𝕊², (y:E)) x),
  -- transitivity mfderiv (𝓡 2) 𝓘(ℝ, E) (-(λ y : 𝕊², (y:E))) x,
  -- { congr' 2,
  --   ext y,
  --   simp, },
  -- ext v,
  -- simp only [mfderiv_neg, ←rot_eq_aux, continuous_linear_map.coe_comp', comp_app,
  --   continuous_linear_map.neg_apply],
  -- rw rot_one,
  -- convert continuous_linear_map.mem_range_self _ _,
  -- rw range_mfderiv_coe_sphere E,
end

lemma formal_eversion_hol_near_zero_one :
  ∀ᶠ (s : ℝ) near {0, 1}, ∀ x : E, (formal_eversion ω s).is_holonomic_at x :=
sorry

end assume_finite_dimensional

theorem sphere_eversion_of_loc (E : Type*) [inner_product_space ℝ E] [fact (finrank ℝ E = 3)] :
  ∃ f : ℝ → E → E,
  (𝒞 ∞ (uncurry f)) ∧
  (f 0 = λ x, x) ∧
  (f 1 = λ x, -x) ∧
  ∀ t, sphere_immersion (f t) :=
begin
  classical,
  borelize E,
  have rankE := fact.out (finrank ℝ E = 3),
  haveI : finite_dimensional ℝ E := finite_dimensional_of_finrank_eq_succ rankE,
  let ω : orientation ℝ E (fin 3) :=
    (fin_std_orthonormal_basis (fact.out _ : finrank ℝ E = 3)).to_basis.orientation,
  have ineq_rank : finrank ℝ (euclidean_space ℝ (fin 2)) < finrank ℝ E := by simp [rankE],
  let ε : 𝕊² → ℝ := λ x, 1,
  have hε_pos : ∀ x, 0 < ε x := λ x, zero_lt_one,
  have hε_cont : continuous ε := continuous_const,
  haveI : nontrivial E := nontrivial_of_finrank_eq_succ (fact.out _ : finrank ℝ E = 3),
  haveI : nonempty ↥(sphere 0 1 : set E) :=
    (normed_space.sphere_nonempty.mpr zero_le_one).to_subtype,
  obtain ⟨f, h₁, h₂, h₃⟩ :=
    (formal_eversion ω).exists_sol loc_immersion_rel_open (loc_immersion_rel_ample le_rfl)
    zero_lt_one _ is_closed_pair 𝕊² (is_compact_sphere 0 1) (formal_eversion_hol_near_zero_one ω),
  have := h₂.nhds_set_forall_mem,
  refine ⟨f, h₁, _, _, _⟩,
  { ext x, rw [this 0 (by simp), formal_eversion_zero] },
  { ext x, rw [this 1 (by simp), formal_eversion_one] },
  { intro t, apply sphere_immersion_of_sol, intros x hx, exact h₃.nhds_set_forall_mem x hx t }
end

end sphere_eversion
