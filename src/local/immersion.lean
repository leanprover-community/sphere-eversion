import to_mathlib.geometry.manifold.sphere
import local.h_principle
-- import global.twist_one_jet_sec
-- maybe parametric global
import global.rotation
import interactive_expr
set_option trace.filter_inst_type true

/-!
This is a stop-gap file to prove sphere eversion from the local verson of the h-principle.
Contents:
parametricity
-/
noncomputable theory

open metric finite_dimensional set function rel_loc
open_locale topological_space

section general

section parametric_h_principle


variables {E : Type*} [normed_add_comm_group E] [normed_space ℝ E] [finite_dimensional ℝ E]
          {F : Type*} [normed_add_comm_group F] [normed_space ℝ F] [measurable_space F] [borel_space F]
          [finite_dimensional ℝ F]
          {G : Type*} [normed_add_comm_group G] [normed_space ℝ G]

variables [finite_dimensional ℝ E] [finite_dimensional ℝ F]

variables {R : rel_loc E F} (h_op: is_open R) (h_ample: R.is_ample) (L : landscape E)
variables {ε : ℝ} (ε_pos : 0 < ε)

include h_op h_ample ε_pos

/- not the full local h-principle sphere eversion,
but just a homotopy of solutions from a homotopy of formal solutions
We don't use the `L.C` in the statement, since we want a set in `ℝ`, not in `E`. -/
lemma rel_loc.htpy_formal_sol.exists_sol (𝓕 : R.htpy_formal_sol) (C : set ℝ) (hC : is_closed C)
  (h_hol : ∀ᶠ t near C, ∀ x, (𝓕 t).is_holonomic_at x) :
  ∃ f : ℝ → E → F,
    (𝒞 ∞ $ uncurry f) ∧
    (∀ᶠ t near C, ∀ x, f t x = 𝓕.f t x) ∧
    (∀ x, x ∉ L.K₁ → ∀ t, f t x = 𝓕.f t x) ∧
    (∀ᶠ x near L.K₀, ∀ t, ∥f t x - 𝓕.f t x∥ ≤ ε) ∧
    (∀ᶠ x near L.K₀, ∀ t, (x, f t x, D (f t) x) ∈ R) :=
begin
  sorry
end

end parametric_h_principle

variables
{E : Type*} [inner_product_space ℝ E]
{E' : Type*} [inner_product_space ℝ E']
{F : Type*} [inner_product_space ℝ F]


/-- A map between vector spaces is a immersion when viewed as a map on the sphere, when its
derivative at `x` near the sphere is injective of the orthogonal complement of `x`
(the tangent space to the sphere).
-/
def sphere_immersion (f : E → E') : Prop :=
∀ᶠ x in 𝓝ˢ (sphere (0 : E) 1), inj_on (D f x) (submodule.span ℝ ({x} : set E))ᗮ

variables (E E')
/-- The relation of immersions for maps between two manifolds. -/
def loc_immersion_rel : rel_loc E E' :=
{w | w.1 ≠ 0 → inj_on w.2.2 (submodule.span ℝ ({w.1} : set E))ᗮ } -- how do we deal exactly with 0?

variables {E E'}

lemma sphere_immersion_iff (f : E → E') :
  sphere_immersion f ↔ ∀ᶠ x in 𝓝ˢ (sphere (0 : E) 1), (x, f x, fderiv ℝ f x) ∈ loc_immersion_rel E E' :=
sorry --by simp_rw [sphere_immersion, loc_immersion_rel, mem_set_of]

variables [finite_dimensional ℝ E] [finite_dimensional ℝ E']

lemma immersion_rel_open :
  is_open (loc_immersion_rel E E') :=
begin
  sorry
  -- simp_rw [charted_space.is_open_iff HJ (immersion_rel I M I' M'), chart_at_image_immersion_rel_eq],
  -- refine λ σ, (ψJ σ).open_target.inter _,
  -- convert is_open_univ.prod continuous_linear_map.is_open_injective,
  -- { ext, simp, },
  -- { apply_instance, },
  -- { apply_instance, },
end

lemma immersion_rel_ample (h : finrank ℝ E ≤ finrank ℝ E') :
  (loc_immersion_rel E E').is_ample :=
begin
  sorry
  -- rw [rel_mfld.ample_iff],
  -- rintros ⟨⟨m, m'⟩, φ : tangent_space I m →L[ℝ] tangent_space I' m'⟩
  --         (p : dual_pair' (tangent_space I m)) (hφ : injective φ),
  -- haveI : finite_dimensional ℝ (tangent_space I m) := (by apply_instance : finite_dimensional ℝ E),
  -- have hcodim := p.two_le_rank_of_rank_lt_rank h φ,
  -- rw [immersion_rel_slice_eq I I' hφ],
  -- exact ample_of_two_le_codim hcodim,
end

end general

section sphere_eversion

variables (E : Type*) [inner_product_space ℝ E] {n : ℕ} [fact (finrank ℝ E = 3)]

local notation `𝕊²` := sphere (0 : E) 1

/- The relation of immersion of a two-sphere into its ambient Euclidean space. -/
local notation `𝓡_imm` := loc_immersion_rel E E

section preparation

variables [finite_dimensional ℝ E] -- no way of inferring this from the `fact`

def sphere_landscape : landscape E :=
{ C := ∅,
  K₀ := 𝕊²,
  K₁ := closed_ball 0 2,
  hC := is_closed_empty,
  hK₀ := is_compact_sphere 0 1,
  hK₁ := is_compact_closed_ball 0 2,
  h₀₁ := sphere_subset_closed_ball.trans $
    (closed_ball_subset_ball $ show (1 : ℝ) < 2, by norm_num).trans
    (interior_closed_ball _ (show (2 : ℝ) ≠ 0, by norm_num)).symm.subset }

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

end preparation

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
  obtain ⟨f, h₁, h₂, -, h₄, h₅⟩ :=
    (formal_eversion ω).exists_sol immersion_rel_open (immersion_rel_ample le_rfl)
    (sphere_landscape E) zero_lt_one _ is_closed_pair (formal_eversion_hol_near_zero_one ω),
  have := h₂.nhds_set_forall_mem,
  refine ⟨f, h₁, _, _, _⟩,
  { ext x, rw [this 0 (by simp), formal_eversion_zero] },
  { ext x, rw [this 1 (by simp), formal_eversion_one] },
  { sorry }
end

end sphere_eversion
