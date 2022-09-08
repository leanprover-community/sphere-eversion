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

-- section twist

-- variables
-- {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
-- {F : Type*} [normed_add_comm_group F] [normed_space ℝ F]
-- {G : Type*} [normed_add_comm_group G] [normed_space ℝ G]
-- {P : Type*} [normed_add_comm_group P] [normed_space ℝ P]
-- {V : Type*} [normed_add_comm_group V] [normed_space ℝ V]
-- {V' : Type*} [normed_add_comm_group V'] [normed_space ℝ V']


-- def family_twist
--   (f : jet_sec E F)
--   (g : P × E → (F →L[ℝ] G))
--   (hg : cont_diff ℝ ∞ g) :
--   family_jet_sec E G P :=
-- { f := sorry,
--   φ := λ s x, g (s, x) ∘L (f x).2,
--   f_diff := sorry,
--   φ_diff := sorry }
-- -- { to_fun := λ p, ⟨p.2, (i p).comp (s p.2).2⟩,
-- --   is_sec' := λ p, rfl,
-- --   smooth' := begin
-- --     intro x₀,
-- --     refine smooth_at_snd.one_jet_eucl_bundle_mk _,
-- --     simp_rw [continuous_linear_map.comp_assoc],
-- --     have : smooth_at (J.prod I) _ (λ x : N × M, _) x₀ := s.smooth.comp smooth_snd x₀,
-- --     simp_rw [smooth_at_one_jet_eucl_bundle, s.is_sec] at this,
-- --     exact (i_smooth x₀).clm_comp this.2
-- --   end }


-- end twist

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

open submodule rel_loc

lemma mem_slice_iff_of_not_mem {x : E} {w : E'} {φ : E →L[ℝ] E'} {p : dual_pair' E}
  (hx : x ∉ B) (y : E') : w ∈ slice R p (x, y, φ) ↔ inj_on (p.update φ w) {.x}ᗮ :=
begin
  change (x ∉ ball (0 : E) 2⁻¹ → inj_on (p.update φ w) {.x}ᗮ) ↔ inj_on (p.update φ w) {.x}ᗮ,
  simp [hx]
end

lemma slice_eq_of_not_mem {x : E} {w : E'} {φ : E →L[ℝ] E'} {p : dual_pair' E}
  (hx : x ∉ B) (y : E') : slice R p (x, y, φ) = {w | inj_on (p.update φ w) {.x}ᗮ} :=
by { ext w, rw mem_slice_iff_of_not_mem hx y, exact iff.rfl }

local notation `dim` := finrank ℝ

-- In the next lemma the assumption `dim E = n + 1` is for convenience
-- using `finrank_orthogonal_span_singleton`. We could remove it to treat empty spheres...
lemma loc_immersion_rel_ample (n : ℕ) [fact (dim E = n+1)] (h : finrank ℝ E ≤ finrank ℝ E') :
  (immersion_sphere_rel E E').is_ample :=
begin
  rw is_ample_iff,
  rintro ⟨x, y, φ⟩ p h_mem,
  by_cases hx : x ∈ B,
  sorry { apply ample_slice_of_forall,
    intros w,
    simp [hx]  },
  { have hφ : inj_on φ {.x}ᗮ := h_mem hx, clear h_mem,
    by_cases H : p.π.ker = {.x}ᗮ,
    sorry { have key : ∀ w, eq_on (p.update φ w) φ {.x}ᗮ,
      { intros w x,
        rw ← H,
        exact p.update_ker_pi φ w },
      exact ample_slice_of_forall _ p  (λ w _, hφ.congr (key w).symm) },
    { obtain ⟨v', hv', hπv'⟩ : ∃ v : E, {.x}ᗮ = (p.π.ker ⊓ {.x}ᗮ) ⊔ span ℝ {v} ∧ p.π v = 1,
      {
        sorry },
      let p' : dual_pair' E := { π := p.π, v := v', pairing := hπv' },
      apply ample_slice_of_ample_slice (show p'.π = p.π, from rfl),
      have : slice R p' (x, y, φ) = (map φ (p.π.ker ⊓ {.x}ᗮ))ᶜ,
      sorry { ext w,
        rw mem_slice_iff_of_not_mem hx y,
        -- we need inj_on_update_iff (see `injective_update_iff` in dual_pair)
        --rw inj_on_iff_injective,
        --have := p'.injective_update_iff,
        sorry },
      rw [this],
      apply ample_of_two_le_codim,
      let Φ := φ.to_linear_map,
      suffices : 2 ≤ dim (E' ⧸ map Φ (p.π.ker ⊓ {.x}ᗮ)),
      sorry { rw ← finrank_eq_dim,
        exact_mod_cast this },
      apply le_of_add_le_add_right,
      rw submodule.finrank_quotient_add_finrank (map Φ $ p.π.ker ⊓ {.x}ᗮ),
      have := finrank_map_le ℝ Φ (p.π.ker ⊓ {.x}ᗮ),
      have : dim (p.π.ker ⊓ {.x}ᗮ : submodule ℝ E) + 1 = n,
      sorry { have hx₀ : x ≠ 0, sorry,
        have eq₁ : dim {.x}ᗮ = n, sorry, -- from finrank_orthogonal_span_singleton hx₀,
        have eq₂ := submodule.dim_sup_add_dim_inf_eq (p.π.ker ⊓ {.x}ᗮ) (span ℝ {v'}),
        have : v' ≠ 0, sorry,
        have eq₃ : dim (span ℝ {v'}) = 1, sorry,
        have : p.π.ker ⊓ {.x}ᗮ ⊓ span ℝ {v'} = (⊥ : submodule ℝ E), sorry,
        rw [← hv', eq₁, eq₃, this] at eq₂,
        simpa using eq₂.symm },
      have : dim E = n+1, from fact.out _,
      linarith } }
end


variables (E) [fact (dim E = 3)]

/- The relation of immersion of a two-sphere into its ambient Euclidean space. -/
local notation `𝓡_imm` := immersion_sphere_rel E E

section assume_finite_dimensional

variables [finite_dimensional ℝ E] -- no way of inferring this from the `fact`

lemma is_closed_pair : is_closed ({0, 1} : set ℝ) :=
(by simp : ({0, 1} : set ℝ).finite).is_closed

variables {E} (ω : orientation ℝ E (fin 3))

include ω
def loc_formal_eversion_aux : htpy_jet_sec E E :=
{ f := λ (t : ℝ) (x : E), (1 - 2 * t) • x, -- (1 - 2 * s) • x
  φ := λ t x, rot_aux ω.volume_form (t, x) -
    (2 * t) • ⟪x, x⟫_ℝ⁻¹ • (continuous_linear_map.to_span_singleton ℝ x ∘L innerSL x),
  f_diff := begin
  sorry
  -- refine (cont_mdiff.smul _ _).add (cont_mdiff_fst.smul _),
  -- { exact (cont_diff_const.sub cont_diff_id).cont_mdiff.comp cont_mdiff_fst },
  -- { exact cont_mdiff_coe_sphere.comp cont_mdiff_snd },
  -- { exact (cont_diff_neg.cont_mdiff.comp cont_mdiff_coe_sphere).comp cont_mdiff_snd },
  end,
  φ_diff := sorry }
-- sorry
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
def loc_formal_eversion : htpy_formal_sol 𝓡_imm :=
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
  .. loc_formal_eversion_aux ω }

lemma loc_formal_eversion_f (t : ℝ) :
  (loc_formal_eversion ω t).f = λ x : E, ((1 : ℝ) - 2 * t) • x :=
rfl

lemma loc_formal_eversion_φ (t : ℝ) (x : E) (v : E) :
  (loc_formal_eversion ω t).φ x v = rot_aux ω.volume_form (t, x) v -
    (2 * t) • ⟪x, x⟫_ℝ⁻¹ • ⟪x, v⟫_ℝ • x :=
rfl

lemma loc_formal_eversion_zero (x : E) : (loc_formal_eversion ω).f 0 x = x :=
show ((1 : ℝ) - 2 * 0) • (x : E) = x, by simp

lemma loc_formal_eversion_one (x : E) : (loc_formal_eversion ω).f 1 x = -x :=
show ((1 : ℝ) - 2 * 1) • (x : E) = -x, by simp [show (1 : ℝ) - 2 = -1, by norm_num]

lemma loc_formal_eversion_hol_at_zero {x : E} :
  (loc_formal_eversion ω 0).is_holonomic_at x :=
by simp_rw [jet_sec.is_holonomic_at, loc_formal_eversion_f, continuous_linear_map.ext_iff,
    loc_formal_eversion_φ, ← rot_eq_aux, rot_zero, mul_zero, zero_smul, sub_zero,
    show (has_smul.smul (1 : ℝ) : E → E) = id, from funext (one_smul ℝ), fderiv_id,
    eq_self_iff_true, implies_true_iff]

lemma loc_formal_eversion_hol_at_one {x : E} :
  (loc_formal_eversion ω 1).is_holonomic_at x :=
begin
  simp_rw [jet_sec.is_holonomic_at, loc_formal_eversion_f, continuous_linear_map.ext_iff,
    loc_formal_eversion_φ],
  intro v,
  simp_rw [← rot_eq_aux],
  simp_rw [mul_one, show (1 : ℝ) - 2 = -1, by norm_num,
    show (has_smul.smul (-1 : ℝ) : E → E) = λ x, - x, from funext (λ v, by rw [neg_smul, one_smul]),
    fderiv_neg, fderiv_id', continuous_linear_map.neg_apply, continuous_linear_map.id_apply],
  -- write `v` as `a • x + v'` with `v' ⊥ x`
  obtain ⟨a, v, hv, rfl⟩ : ∃ (a : ℝ) (v' : E), ⟪x, v'⟫_ℝ = 0 ∧ v = a • x + v',
  { sorry },
  have h2v : v ∈ {.x}ᗮ,
  { sorry, },
  simp_rw [continuous_linear_map.map_add, continuous_linear_map.map_smul, rot_one _ x h2v,
    rot_self],
  rcases eq_or_ne x 0 with rfl|hx,
  { simp },
  have hx : ⟪x, x⟫_ℝ ≠ 0,
  { rwa [ne.def, inner_self_eq_zero] },
  simp_rw [neg_add, inner_add_right, hv, add_zero, inner_smul_right, mul_smul,
    smul_comm_class.smul_comm a, inv_smul_smul₀ hx, add_sub_right_comm, ← mul_smul, ← sub_smul,
    ← neg_smul],
  ring_nf
end

lemma loc_formal_eversion_hol_near_zero_one :
  ∀ᶠ (s : ℝ) near {0, 1}, ∀ x : E, (loc_formal_eversion ω s).is_holonomic_at x :=
sorry

end assume_finite_dimensional

open_locale unit_interval

set_option trace.filter_inst_type false
theorem sphere_eversion_of_loc (E : Type*) [inner_product_space ℝ E] [fact (dim E = 3)] :
  ∃ f : ℝ → E → E,
  (𝒞 ∞ (uncurry f)) ∧
  (f 0 = λ x, x) ∧
  (f 1 = λ x, -x) ∧
  ∀ t ∈ I, sphere_immersion (f t) :=
begin
  classical,
  borelize E,
  have rankE := fact.out (dim E = 3),
  haveI : finite_dimensional ℝ E := finite_dimensional_of_finrank_eq_succ rankE,
  let ω : orientation ℝ E (fin 3) :=
    (fin_std_orthonormal_basis (fact.out _ : dim E = 3)).to_basis.orientation,
  obtain ⟨f, h₁, h₂, h₃⟩ :=
    (loc_formal_eversion ω).exists_sol loc_immersion_rel_open (loc_immersion_rel_ample 2 le_rfl)
    zero_lt_one _ is_closed_pair 𝕊² (is_compact_sphere 0 1) (loc_formal_eversion_hol_near_zero_one ω),
  refine ⟨f, h₁, _, _, _⟩,
  { ext x, rw [h₂ 0 (by simp), loc_formal_eversion_zero] },
  { ext x, rw [h₂ 1 (by simp), loc_formal_eversion_one] },
  { exact λ t ht, sphere_immersion_of_sol _ (λ x hx, h₃ x hx t ht) },
end

end sphere_eversion
