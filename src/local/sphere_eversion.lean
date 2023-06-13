import to_mathlib.analysis.inner_product_space.rotation
import to_mathlib.analysis.inner_product_space.dual
import local.parametric_h_principle

/-!
This is file proves the existence of a sphere eversion from the local verson of the h-principle.

We define the relation of immersions `R = immersion_sphere_rel ⊆ J¹(E, F)` which consist of all
`(x, y, ϕ)` such that if `x` is outside a ball around the origin with chosen radius `R < 1` then
`ϕ` must be injective on `(ℝ ∙ x)ᗮ` (the orthogonal complement of the span of `x`).
We show that `R` is open and ample.

Furthermore, we define a formal solution of sphere eversion that is holonomic near `0` and `1`.
We have to be careful since we're not actually working on the sphere,
but in the ambient space `E ≃ ℝ³`.
See `loc_formal_eversion` for the choice and constaints of the solution.

Finally, we obtain the existence of sphere eversion from the parametric local h-principle,
proven in `local.parametric_h_principle`.
-/
noncomputable theory

open metric finite_dimensional set function rel_loc filter (hiding mem_map) inner_product_space
  submodule linear_map (ker)
open_locale topology real_inner_product_space

section sphere_eversion

variables
{E : Type*} [normed_add_comm_group E] [inner_product_space ℝ E]
{F : Type*} [normed_add_comm_group F] [inner_product_space ℝ F]

local notation `𝕊²` := sphere (0 : E) 1
local notation `dim` := finrank ℝ
local notation `pr[`x`]ᗮ` := orthogonal_projection (ℝ ∙ x)ᗮ
local notation (name := dot_print_only) R ` ∙ `:1000 x := submodule.span R {x}
local notation (name := dot_local) R ` ∙ `:1000 x :=
  submodule.span R (@singleton _ _ set.has_singleton x)
local notation `B` := ball (0 : E) 0.9

/-- A map between vector spaces is a immersion viewed as a map on the sphere, when its
derivative at `x ∈ 𝕊²` is injective on the orthogonal complement of `x`
(the tangent space to the sphere). Note that this implies `f` is differentiable at every point
`x ∈ 𝕊²` since otherwise `D f x = 0`.
-/
def sphere_immersion (f : E → F) : Prop :=
∀ x ∈ 𝕊², inj_on (D f x) (ℝ ∙ x)ᗮ

variables (E F)

/-- The relation of immersionsof a two-sphere into its ambient Euclidean space. -/
def immersion_sphere_rel : rel_loc E F :=
{w : one_jet E F | w.1 ∉ B → inj_on w.2.2 (ℝ ∙ w.1)ᗮ }

local notation `R` := immersion_sphere_rel E F

variables {E F}

@[simp] lemma mem_loc_immersion_rel {x y φ} :
  (⟨x, y, φ⟩ : one_jet E F) ∈ immersion_sphere_rel E F ↔ x ∉ B → inj_on φ (ℝ ∙ x)ᗮ :=
iff.rfl

lemma sphere_immersion_of_sol (f : E → F) :
  (∀ x ∈ 𝕊², (x, f x, fderiv ℝ f x) ∈ immersion_sphere_rel E F) → sphere_immersion f :=
begin
  intros h x x_in,
  have : x ∉ B,
  { rw mem_sphere_zero_iff_norm at x_in,
    norm_num [x_in] },
  exact h x x_in this
end

lemma mem_slice_iff_of_not_mem {x : E} {w : F} {φ : E →L[ℝ] F} {p : dual_pair E}
  (hx : x ∉ B) (y : F) : w ∈ slice R p (x, y, φ) ↔ inj_on (p.update φ w) (ℝ ∙ x)ᗮ :=
begin
  change (x ∉ B → inj_on (p.update φ w) (ℝ ∙ x)ᗮ) ↔ inj_on (p.update φ w) (ℝ ∙ x)ᗮ,
  simp_rw [eq_true_intro hx, true_implies_iff]
end

section assume_finite_dimensional

variables [finite_dimensional ℝ E]

-- The following is extracted from `loc_immersion_rel_open` because it is slow to typecheck
lemma loc_immersion_rel_open_aux {x₀ : E} {y₀ : F} {φ₀ : E →L[ℝ] F} (hx₀ : x₀ ∉ B)
  (H : inj_on φ₀ (ℝ ∙ x₀)ᗮ) :
  ∀ᶠ (p : one_jet E F) in 𝓝 (x₀, y₀, φ₀), ⟪x₀, p.1⟫ ≠ 0 ∧
  injective ((p.2.2.comp $ (subtypeL (ℝ ∙ p.1)ᗮ).comp pr[p.1]ᗮ).comp (ℝ ∙ x₀)ᗮ.subtypeL) :=
begin
  -- This is true at (x₀, y₀, φ₀) and is an open condition because `p ↦ ⟪x₀, p.1⟫` and
  -- `p ↦ (p.2.2.comp $ (subtypeL (ℝ ∙ p.1)ᗮ).comp pr[p.1]ᗮ).comp j₀` are continuous
  set j₀ := subtypeL (ℝ ∙ x₀)ᗮ,
  let f : one_jet E F → ℝ × ((ℝ ∙ x₀)ᗮ →L[ℝ] F) :=
      λ p, (⟪x₀, p.1⟫, (p.2.2.comp $ (subtypeL (ℝ ∙ p.1)ᗮ).comp pr[p.1]ᗮ).comp j₀),
  let P : ℝ × ((ℝ ∙ x₀)ᗮ →L[ℝ] F) → Prop :=
      λ q, q.1 ≠ 0 ∧ injective q.2,
  have x₀_ne : x₀ ≠ 0,
  { refine λ hx₀', hx₀ _,
    rw hx₀',
    apply mem_ball_self,
    norm_num },
  -- The following suffices looks stupid but is much faster than using the change tactic.
  suffices : ∀ᶠ (p : one_jet E F) in 𝓝 (x₀, y₀, φ₀), P (f p), { exact this },
  apply continuous_at.eventually,
  { refine (continuous_at_const.inner continuous_at_fst).prod _,
    apply continuous_at.compL,
    { apply continuous_at.compL,
      exact continuous_at_snd.comp continuous_at_snd,
      -- Faster than change.
      suffices : continuous_at ((λ x, (ℝ ∙ x)ᗮ.subtypeL.comp pr[x]ᗮ) ∘ prod.fst) (x₀, y₀, φ₀),
      { exact this },
      apply continuous_at.comp _ continuous_at_fst,
      exact continuous_at_orthogonal_projection_orthogonal x₀_ne },
    exact continuous_at_const },
  { exact (continuous_fst.is_open_preimage _ is_open_compl_singleton).inter
          (continuous_snd.is_open_preimage _ continuous_linear_map.is_open_injective) },
  { split,
    { change ⟪x₀, x₀⟫ ≠ 0,
      apply (inner_self_eq_zero.not).mpr x₀_ne },
    { change injective (φ₀ ∘ (coe ∘ (pr[x₀]ᗮ ∘ coe))),
      rw [orthogonal_projection_comp_coe, comp.right_id],
      exact inj_on_iff_injective.mp H } }
end

lemma loc_immersion_rel_open : is_open (immersion_sphere_rel E F) :=
begin
  dsimp only [immersion_sphere_rel],
  rw is_open_iff_mem_nhds,
  rintros ⟨x₀, y₀, φ₀⟩ (H : x₀ ∉ B → inj_on φ₀ (ℝ ∙ x₀)ᗮ),
  change ∀ᶠ (p : one_jet E F) in 𝓝 (x₀, y₀, φ₀), _,
  by_cases hx₀ : x₀ ∈ B,
  { have : ∀ᶠ (p : one_jet E F) in 𝓝 (x₀, y₀, φ₀), p.1 ∈ B,
    { rw nhds_prod_eq,
      apply (is_open_ball.eventually_mem hx₀).prod_inl },
    apply this.mono,
    rintros ⟨x, y, φ⟩ (hx : x ∈ B) (Hx : x ∉ B),
    exact (Hx hx).elim },
  { replace H := H hx₀,
    set j₀ := subtypeL (ℝ ∙ x₀)ᗮ,
    let f : one_jet E F → ℝ × ((ℝ ∙ x₀)ᗮ →L[ℝ] F) :=
      λ p, (⟪x₀, p.1⟫, (p.2.2.comp $ (subtypeL (ℝ ∙ p.1)ᗮ).comp pr[p.1]ᗮ).comp j₀),
    let P : ℝ × ((ℝ ∙ x₀)ᗮ →L[ℝ] F) → Prop :=
      λ q, q.1 ≠ 0 ∧ injective q.2,
    have : ∀ᶠ (p : one_jet E F) in 𝓝 (x₀, y₀, φ₀), P (f p),
    { exact loc_immersion_rel_open_aux hx₀ H },
    apply this.mono, clear this,
    rintros ⟨x, y, φ⟩ ⟨hxx₀ : ⟪x₀, x⟫ ≠ 0, Hφ⟩ (hx : x ∉ B),
    dsimp only [P, f] at Hφ,
    change inj_on φ (ℝ ∙ x)ᗮ,
    have : range ((subtypeL (ℝ ∙ x)ᗮ) ∘ pr[x]ᗮ ∘ j₀) = (ℝ ∙ x)ᗮ,
    { rw function.surjective.range_comp,
      exact subtype.range_coe,
      exact (orthogonal_projection_orthogonal_line_iso hxx₀).surjective },
    rw ← this, clear this,
    exact function.injective.inj_on_range Hφ },
end

variables [finite_dimensional ℝ F]

-- In the next lemma the assumption `dim E = n + 1` is for convenience
-- using `finrank_orthogonal_span_singleton`. We could remove it to treat empty spheres...
lemma loc_immersion_rel_ample (n : ℕ) [fact (dim E = n+1)] (h : finrank ℝ E ≤ finrank ℝ F) :
  (immersion_sphere_rel E F).is_ample :=
begin
  classical, -- gives a minor speedup
  rw is_ample_iff,
  rintro ⟨x, y, φ⟩ p h_mem,
  by_cases hx : x ∈ B,
  { apply ample_slice_of_forall,
    intros w,
    simp only [hx, mem_loc_immersion_rel, not_true, is_empty.forall_iff] },
  have x_ne : x ≠ 0,
  { rintro rfl,
    apply hx,
    apply mem_ball_self,
    norm_num1 },
  have hφ : inj_on φ (ℝ ∙ x)ᗮ := h_mem hx, clear h_mem,
  let u : E := (inner_product_space.to_dual ℝ E).symm p.π,
  have u_ne : u ≠ 0,
  { exact (inner_product_space.to_dual ℝ E).symm.apply_ne_zero p.pi_ne_zero },
  by_cases H : ker p.π = (ℝ ∙ x)ᗮ,
  { have key : ∀ w, eq_on (p.update φ w) φ (ℝ ∙ x)ᗮ,
    { intros w x,
      rw ← H,
      exact p.update_ker_pi φ w },
    exact ample_slice_of_forall _ p (λ w _, hφ.congr (key w).symm) },
  obtain ⟨v', v'_in, hv', hπv'⟩ :
    ∃ v' : E, v' ∈ (ℝ ∙ x)ᗮ ∧ (ℝ ∙ x)ᗮ = (ker p.π ⊓ (ℝ ∙ x)ᗮ) ⊔ (ℝ ∙ v') ∧ p.π v' = 1,
  { have ne_z : p.π (pr[x]ᗮ u) ≠ 0,
    { rw ← to_dual_symm_apply,
      change ¬ ⟪u, pr[x]ᗮ u⟫ = 0,
      rw inner_projection_self_eq_zero_iff.not,
      contrapose! H,
      rw orthogonal_orthogonal at H,
      rw [← orthogonal_span_to_dual_symm, span_singleton_eq_span_singleton_of_ne u_ne H],
      apply_instance },
    have ne_z' : (p.π $ pr[x]ᗮ u)⁻¹ ≠ 0,
    { exact inv_ne_zero ne_z },
    refine ⟨(p.π $ pr[x]ᗮ u)⁻¹ • pr[x]ᗮ u, (ℝ ∙ x)ᗮ.smul_mem _ (pr[x]ᗮ u).2, _, _⟩,
    { have := orthogonal_line_inf_sup_line u x,
      rw [← orthogonal_span_to_dual_symm p.π,
        span_singleton_smul_eq ne_z'.is_unit],
      exact (orthogonal_line_inf_sup_line u x).symm },
    rw [p.π.map_smul, smul_eq_mul, inv_mul_cancel ne_z] },
  let p' : dual_pair E := { π := p.π, v := v', pairing := hπv' },
  apply ample_slice_of_ample_slice (show p'.π = p.π, from rfl),
  suffices : slice R p' (x, y, φ) = (map φ (ker p.π ⊓ (ℝ ∙ x)ᗮ))ᶜ,
  { rw [this],
    apply ample_of_two_le_codim,
    let Φ := φ.to_linear_map,
    suffices : 2 ≤ dim (F ⧸ map Φ (ker p.π ⊓ (ℝ ∙ x)ᗮ)),
    { rw ← finrank_eq_rank,
      exact_mod_cast this },
    apply le_of_add_le_add_right,
    rw submodule.finrank_quotient_add_finrank (map Φ $ ker p.π ⊓ (ℝ ∙ x)ᗮ),
    have : dim (ker p.π ⊓ (ℝ ∙ x)ᗮ : submodule ℝ E) + 1 = n,
    { have eq := submodule.finrank_sup_add_finrank_inf_eq (ker p.π ⊓ (ℝ ∙ x)ᗮ) (span ℝ {v'}),
      have eq₁ : dim (ℝ ∙ x)ᗮ = n, from finrank_orthogonal_span_singleton x_ne,
      have eq₂ : ker p.π ⊓ (ℝ ∙ x)ᗮ ⊓ span ℝ {v'} = (⊥ : submodule ℝ E),
      { erw [inf_left_right_swap, inf_comm, ← inf_assoc, p'.inf_eq_bot, bot_inf_eq] },
      have eq₃ : dim (span ℝ {v'}) = 1, apply finrank_span_singleton p'.v_ne_zero,
      rw [← hv', eq₁, eq₃, eq₂] at eq,
      simpa only [finrank_bot] using eq.symm },
    have : dim E = n+1, from fact.out _,
    linarith [finrank_map_le Φ (ker p.π ⊓ (ℝ ∙ x)ᗮ)] },
  ext w,
  rw mem_slice_iff_of_not_mem hx y,
  rw inj_on_iff_injective,
  let j := (ℝ ∙ x)ᗮ.subtypeL,
  let p'' : dual_pair (ℝ ∙ x)ᗮ := ⟨p.π.comp j, ⟨v', v'_in⟩, hπv'⟩,
  have eq : ((ℝ ∙ x)ᗮ : set E).restrict (p'.update φ w) = (p''.update (φ.comp j) w),
  { ext z,
    simp only [dual_pair.update, restrict_apply, continuous_linear_map.add_apply,
      continuous_linear_map.coe_comp', coe_subtypeL', submodule.coe_subtype, comp_app, coe_mk] },
  have eq' : map (φ.comp j) (ker p''.π) = map φ (ker p.π ⊓ (ℝ ∙ x)ᗮ),
  { have : map ↑j (ker p''.π) = ker p.π ⊓ (ℝ ∙ x)ᗮ,
    { ext z,
      simp only [mem_map, linear_map.mem_ker, continuous_linear_map.coe_comp',
                coe_subtypeL', submodule.coe_subtype, comp_app, mem_inf],
      split,
      { rintros ⟨t, ht, rfl⟩,
        rw [continuous_linear_map.coe_coe, subtypeL_apply],
        exact ⟨ht, t.2⟩ },
      { rintros ⟨hz, z_in⟩,
        exact ⟨⟨z, z_in⟩, hz, rfl⟩ }, },
    erw [← this, map_comp],
    refl },
  rw [eq, p''.injective_update_iff, mem_compl_iff, eq'],
  exact iff.rfl,
  rw ← show ((ℝ ∙ x)ᗮ : set E).restrict φ = φ.comp j, by { ext, refl },
  exact hφ.injective
end

end assume_finite_dimensional

/-- The main ingredient of the linear map in the formal eversion of the sphere. -/
def loc_formal_eversion_aux_φ [fact (dim E = 3)] (ω : orientation ℝ E (fin 3))
  (t : ℝ) (x : E) : E →L[ℝ] E :=
ω.rot (t, x) - (2 * t) • (submodule.subtypeL (ℝ ∙ x) ∘L orthogonal_projection (ℝ ∙ x))

section assume_finite_dimensional

variables [fact (dim E = 3)] [finite_dimensional ℝ E] (ω : orientation ℝ E (fin 3))

lemma smooth_at_loc_formal_eversion_aux_φ {p : ℝ × E} (hx : p.2 ≠ 0) :
  cont_diff_at ℝ ∞ (uncurry (loc_formal_eversion_aux_φ ω)) p :=
begin
  refine (ω.cont_diff_rot hx).sub _,
  refine cont_diff_at.smul (cont_diff_at_const.mul cont_diff_at_fst) _,
  exact (cont_diff_at_orthogonal_projection_singleton hx).comp p cont_diff_at_snd
end

/-- A formal eversion of `𝕊²`, viewed as a homotopy. -/
def loc_formal_eversion_aux : htpy_jet_sec E E :=
{ f := λ (t : ℝ) (x : E), (1 - 2 * smooth_step t) • x,
  φ := λ t x, smooth_step (‖x‖ ^ 2) • loc_formal_eversion_aux_φ ω (smooth_step t) x,
  f_diff := cont_diff.smul (cont_diff_const.sub $ cont_diff_const.mul $
    smooth_step.smooth.comp cont_diff_fst) cont_diff_snd,
  φ_diff := begin
    refine cont_diff_iff_cont_diff_at.mpr (λ x, _),
    cases eq_or_ne x.2 0 with hx hx,
    { refine cont_diff_at_const.congr_of_eventually_eq _, exact 0,
      have : ((λ x, ‖x‖ ^ 2) ⁻¹' Iio (1/4)) ∈ 𝓝 (0 : E),
      { refine is_open.mem_nhds _ _,
        exact (is_open_Iio.preimage (cont_diff_norm_sq ℝ : 𝒞 ∞ _).continuous),
        simp_rw [mem_preimage, norm_zero, zero_pow two_pos, mem_Iio],
        norm_num },
      have : ((λ x, smooth_step (‖x‖ ^ 2)) ⁻¹' {0}) ∈ 𝓝 (0 : E),
      { refine mem_of_superset this _,
        rw @preimage_comp _ _ _ _ smooth_step,
        refine preimage_mono _,
        intros x hx,
        rw [mem_preimage, mem_singleton_iff, smooth_step.of_lt hx] },
      have : ((λ p : ℝ × E, smooth_step (‖p.2‖ ^ 2)) ⁻¹' {0}) ∈ 𝓝 x,
      { rw [← hx] at this, exact continuous_at_snd.preimage_mem_nhds this },
      refine eventually_of_mem this _,
      rintro ⟨t, x⟩ hx,
      simp_rw [mem_preimage, mem_singleton_iff] at hx,
      show smooth_step (‖x‖ ^ 2) • loc_formal_eversion_aux_φ ω (smooth_step t) x = 0,
      simp_rw [hx, zero_smul] },
    refine cont_diff_at.smul _ _,
    refine (smooth_step.smooth.comp $ (cont_diff_norm_sq ℝ).comp cont_diff_snd).cont_diff_at,
    exact (smooth_at_loc_formal_eversion_aux_φ ω
      (show (prod.map smooth_step id x).2 ≠ 0, from hx)).comp x
      (smooth_step.smooth.prod_map cont_diff_id).cont_diff_at,
     end }

/-- A formal eversion of `𝕊²` into its ambient Euclidean space.
The corresponding map `E → E` is roughly a linear homotopy from `id` at `t = 0` to `- id` at
`t = 1`. The continuous linear maps are roughly rotations with angle `t * π`. However, we have to
keep track of a few complications:
* We need the formal solution to be holonomic near `0` and `1`.
  Therefore, we compose the above maps with a smooth step function that is constant `0` near `t = 0`
  and constant `1` near `t = 1`.
* We need to modify the derivative of `ω.rot` to also have the right behavior on `(ℝ ∙ x)`
  at `t = 1` (it is the identity, but it should be `-id`). Therefore, we subtract
  `(2 * t) • (submodule.subtypeL (ℝ ∙ x) ∘L orthogonal_projection (ℝ ∙ x))`,
  which is `2t` times the identity on `(ℝ ∙ x)`.
* We have to make sure the family of continuous linear map is smooth at `x = 0`. Therefore, we
  multiply the family with a factor of `smooth_step (‖x‖ ^ 2)`.
-/
def loc_formal_eversion : htpy_formal_sol (immersion_sphere_rel E E) :=
{ is_sol := begin
    intros t x,
    change x ∉ B →
      inj_on (smooth_step (‖x‖ ^ 2) • loc_formal_eversion_aux_φ ω (smooth_step t) x) (ℝ ∙ x)ᗮ,
    intros hx,
    have h2x : smooth_step (‖x‖ ^ 2) = 1,
    { refine smooth_step.of_gt _,
      rw [mem_ball, not_lt, dist_zero_right] at hx,
      refine (show (3 : ℝ)/4 < 0.9 ^ 2, by norm_num).trans_le _,
      rwa [sq_le_sq, show |(0.9 : ℝ)| = 0.9, by norm_num, abs_norm] },
    rw [h2x, one_smul],
    have h3x : x ≠ 0,
    { rintro rfl, apply hx, exact mem_ball_self (by norm_num) },
    refine (eq_on.inj_on_iff _).mpr (ω.inj_on_rot_of_ne (smooth_step t) h3x),
    intros v hv,
    simp_rw [loc_formal_eversion_aux_φ, continuous_linear_map.sub_apply,
      continuous_linear_map.smul_apply, continuous_linear_map.comp_apply,
      orthogonal_projection_mem_subspace_orthogonal_complement_eq_zero hv,
      _root_.map_zero, smul_zero, sub_zero],
  end,
  .. loc_formal_eversion_aux ω }

@[simp]
lemma loc_formal_eversion_f (t : ℝ) :
  (loc_formal_eversion ω t).f = λ x : E, ((1 : ℝ) - 2 * smooth_step t) • x :=
rfl

lemma loc_formal_eversion_φ (t : ℝ) (x : E) (v : E) :
  (loc_formal_eversion ω t).φ x v = smooth_step (‖x‖ ^ 2) •
    (ω.rot (smooth_step t, x) v -
    (2 * smooth_step t) • orthogonal_projection (ℝ ∙ x) v) :=
rfl

lemma loc_formal_eversion_zero (x : E) : (loc_formal_eversion ω 0).f x = x :=
by simp

lemma loc_formal_eversion_one (x : E) : (loc_formal_eversion ω 1).f x = -x :=
by simp [show (1 : ℝ) - 2 = -1, by norm_num]

lemma loc_formal_eversion_hol_at_zero {t : ℝ} (ht : t < 1/4) {x : E}
  (hx : smooth_step (‖x‖ ^ 2) = 1) : (loc_formal_eversion ω t).is_holonomic_at x :=
by simp_rw [jet_sec.is_holonomic_at, loc_formal_eversion_f, continuous_linear_map.ext_iff,
    loc_formal_eversion_φ, smooth_step.of_lt ht, hx, ω.rot_zero, mul_zero, zero_smul, sub_zero,
    show (has_smul.smul (1 : ℝ) : E → E) = id, from funext (one_smul ℝ), fderiv_id, function.id_def,
    eq_self_iff_true, implies_true_iff]

lemma loc_formal_eversion_hol_at_one {t : ℝ} (ht : 3/4 < t) {x : E}
  (hx : smooth_step (‖x‖ ^ 2) = 1) : (loc_formal_eversion ω t).is_holonomic_at x :=
begin
  simp_rw [jet_sec.is_holonomic_at, loc_formal_eversion_f, continuous_linear_map.ext_iff,
    loc_formal_eversion_φ, smooth_step.of_gt ht, hx],
  intro v,
  simp_rw [mul_one, show (1 : ℝ) - 2 = -1, by norm_num,
    show (has_smul.smul (-1 : ℝ) : E → E) = λ x, - x, from funext (λ v, by rw [neg_smul, one_smul]),
    fderiv_neg, fderiv_id', continuous_linear_map.neg_apply, continuous_linear_map.id_apply],
  obtain ⟨v', hv', v, hv, rfl⟩ := submodule.exists_sum_mem_mem_orthogonal (ℝ ∙ x) v,
  simp_rw [continuous_linear_map.map_add, ω.rot_one _ hv, ω.rot_eq_of_mem_span (1, x) hv'],
  simp_rw [neg_add, submodule.coe_add, orthogonal_projection_eq_self_iff.mpr hv',
    orthogonal_projection_mem_subspace_orthogonal_complement_eq_zero hv, submodule.coe_zero,
    add_zero, two_smul, one_smul],
  abel
end

lemma loc_formal_eversion_hol :
  ∀ᶠ (p : ℝ × E) near {0, 1} ×ˢ 𝕊², (loc_formal_eversion ω p.1).is_holonomic_at p.2 :=
begin
  have : (Iio (1/4 : ℝ) ∪ Ioi (3/4)) ×ˢ ((λ x, ‖x‖ ^ 2) ⁻¹' Ioi (3/4)) ∈
    𝓝ˢ (({0, 1} : set ℝ) ×ˢ 𝕊²),
  { refine (is_open.mem_nhds_set _).mpr _,
    exact (is_open_Iio.union is_open_Ioi).prod
      (is_open_Ioi.preimage (cont_diff_norm_sq ℝ : 𝒞 ∞ _).continuous),
    rintro ⟨s, x⟩ ⟨hs, hx⟩,
    refine ⟨_, _⟩,
    simp_rw [mem_insert_iff, mem_singleton_iff] at hs,
    rcases hs with rfl|rfl,
    exact or.inl (show (0 : ℝ) < 1 / 4, by norm_num),
    exact or.inr (show (3 / 4 : ℝ) < 1, by norm_num),
    simp_rw [mem_sphere_zero_iff_norm] at hx,
    simp_rw [mem_preimage, hx, one_pow, mem_Ioi],
    norm_num },
  have : (Iio (1/4 : ℝ) ∪ Ioi (3/4)) ×ˢ ((λ x, smooth_step (‖x‖ ^ 2)) ⁻¹' {1}) ∈
    𝓝ˢ (({0, 1} : set ℝ) ×ˢ 𝕊²),
  { refine mem_of_superset this (prod_mono subset.rfl _),
    rw @preimage_comp _ _ _ _ smooth_step,
    refine preimage_mono _,
    intros x hx,
    rw [mem_preimage, mem_singleton_iff, smooth_step.of_gt hx] },
  refine eventually_of_mem this _,
  rintro ⟨t, x⟩ ⟨ht|ht, hx⟩,
  { exact loc_formal_eversion_hol_at_zero ω ht hx },
  { exact loc_formal_eversion_hol_at_one ω ht hx }
end

end assume_finite_dimensional

open_locale unit_interval

theorem sphere_eversion_of_loc [fact (dim E = 3)] :
  ∃ f : ℝ → E → E,
  (𝒞 ∞ ↿f) ∧
  (∀ x ∈ 𝕊², f 0 x = x) ∧
  (∀ x ∈ 𝕊², f 1 x = -x) ∧
  ∀ t ∈ I, sphere_immersion (f t) :=
begin
  classical,
  borelize E,
  have rankE := fact.out (dim E = 3),
  haveI : finite_dimensional ℝ E := finite_dimensional_of_finrank_eq_succ rankE,
  let ω : orientation ℝ E (fin 3) :=
    ((std_orthonormal_basis _ _).reindex $ fin_congr (fact.out _ : dim E = 3)).to_basis.orientation,
  have is_closed_pair : is_closed ({0, 1} : set ℝ) :=
  (by simp : ({0, 1} : set ℝ).finite).is_closed,
  obtain ⟨f, h₁, h₂, h₃⟩ :=
    (loc_formal_eversion ω).exists_sol loc_immersion_rel_open (loc_immersion_rel_ample 2 le_rfl)
    ({0, 1} ×ˢ 𝕊²) (is_closed_pair.prod is_closed_sphere) 𝕊² (is_compact_sphere 0 1)
    (loc_formal_eversion_hol ω),
  refine ⟨f, h₁, _, _, _⟩,
  { intros x hx, rw [h₂ (0, x) (mk_mem_prod (by simp) hx), loc_formal_eversion_zero] },
  { intros x hx, rw [h₂ (1, x) (mk_mem_prod (by simp) hx), loc_formal_eversion_one] },
  { exact λ t ht, sphere_immersion_of_sol _ (λ x hx, h₃ x hx t ht) },
end

/- Stating the full statement with all type-class arguments and no uncommon notation. -/
example (E : Type*) [normed_add_comm_group E] [inner_product_space ℝ E] [fact (finrank ℝ E = 3)] :
  ∃ f : ℝ → E → E,
  (cont_diff ℝ ⊤ (uncurry f)) ∧
  (∀ x ∈ sphere (0 : E) 1, f 0 x = x) ∧
  (∀ x ∈ sphere (0 : E) 1, f 1 x = -x) ∧
  ∀ t ∈ unit_interval, sphere_immersion (f t) :=
sphere_eversion_of_loc

end sphere_eversion
