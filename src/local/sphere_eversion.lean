import to_mathlib.geometry.manifold.sphere
import to_mathlib.analysis.inner_product_space.dual
import local.parametric_h_principle
import global.rotation
import interactive_expr
-- set_option trace.filter_inst_type true

/-!
This is a stop-gap file to prove sphere eversion from the local verson of the h-principle.
Contents:
relation of immersions
formal solution of sphere eversion
sphere eversion
-/
noncomputable theory

open metric finite_dimensional set function rel_loc filter (hiding mem_map)
open_locale topological_space

section sphere_eversion

variables
{E : Type*} [inner_product_space ℝ E]
{E' : Type*} [inner_product_space ℝ E']
{F : Type*} [inner_product_space ℝ F]


local notation `𝕊²` := sphere (0 : E) 1
-- ignore the next line which is fixing a pretty-printer bug
local notation (name := module_span_printing_only) `{.` x `}ᗮ` := (submodule.span ℝ {x})ᗮ
local notation `{.` x `}ᗮ` := (ℝ ∙ x)ᗮ
local notation `dim` := finrank ℝ
-- ignore the next line which is fixing a pretty-printer bug
local notation (name := line_printing_only) `Δ` v:55 := submodule.span ℝ {v}
local notation `Δ ` v:55 := submodule.span ℝ ({v} : set E)
local notation `pr[`x`]ᗮ` := orthogonal_projection (submodule.span ℝ {x})ᗮ

/-- A map between vector spaces is a immersion viewed as a map on the sphere, when its
derivative at `x ∈ 𝕊²` is injective on the orthogonal complement of `x`
(the tangent space to the sphere). Note that this implies `f` is differentiable at every point
`x ∈ 𝕊²` since otherwise `D f x = 0`.
-/
def sphere_immersion (f : E → E') : Prop :=
∀ x ∈ 𝕊², inj_on (D f x) {.x}ᗮ

variables (E E')

local notation `B` := ball (0 : E) 0.9

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

section assume_finite_dimensional

variables [finite_dimensional ℝ E] [finite_dimensional ℝ E']
open_locale real_inner_product_space
open submodule

lemma function.injective.inj_on_range {α β γ : Type*} {j : α → β} {φ : β → γ}
  (h : injective $ φ ∘ j) : inj_on φ (range j) :=
begin
  rintros - ⟨x, rfl⟩ - ⟨y, rfl⟩ H,
  exact congr_arg j (h  H)
end

lemma set.range_comp_of_surj {α β γ : Type*} {f : α → β} (hf : surjective f) (g : β → γ) :
  range (g ∘ f) = range g :=
begin
  ext c,
  rw [mem_range, mem_range],
  split,
  { rintros ⟨a, rfl⟩,
    exact ⟨f a, rfl⟩ },
  { rintros ⟨b, rfl⟩,
    rcases hf b with ⟨a, rfl⟩,
    exact ⟨a, rfl⟩ }
end

lemma continuous_at.eventually {α β : Type*} [topological_space α] [topological_space β] {f : α → β}
  {a₀ : α} (hf : continuous_at f a₀) (P : β → Prop) (hP : is_open {b | P b}) (ha₀ : P (f a₀)) :
  ∀ᶠ a in 𝓝 a₀, P (f a) :=
hf (is_open_iff_mem_nhds.mp hP _ ha₀)

lemma continuous.eventually {α β : Type*} [topological_space α] [topological_space β] {f : α → β}
  {a₀ : α} (hf : continuous f) (P : β → Prop) (hP : is_open {b | P b}) (ha₀ : P (f a₀)) :
  ∀ᶠ a in 𝓝 a₀, P (f a) :=
hf.continuous_at.eventually P hP ha₀

-- The following is extracted from `loc_immersion_rel_open` because it takes forever to typecheck
lemma loc_immersion_rel_open_aux {x₀ : E} {y₀ : E'} {φ₀ : E →L[ℝ] E'} (hx₀ : x₀ ∉ B)
  (H : inj_on φ₀ {.x₀}ᗮ) :
  ∀ᶠ (p : one_jet E E') in 𝓝 (x₀, y₀, φ₀),
    ⟪x₀, p.1⟫ ≠ 0 ∧ injective ((p.2.2.comp $ (subtypeL {.p.1}ᗮ).comp pr[p.1]ᗮ).comp {.x₀}ᗮ.subtypeL) :=
begin
  -- This is true at (x₀, y₀, φ₀) and is an open condition because
  -- p ↦ ⟪x₀, p.1⟫ and p ↦ (p.2.2.comp $ (subtypeL {.p.1}ᗮ).comp pr[p.1]ᗮ).comp j₀ are continuous
  set j₀ := subtypeL {.x₀}ᗮ,
  let f : one_jet E E' → ℝ × ({.x₀}ᗮ →L[ℝ] E') :=
      λ p, (⟪x₀, p.1⟫, (p.2.2.comp $ (subtypeL {.p.1}ᗮ).comp pr[p.1]ᗮ).comp j₀),
  let P : ℝ × ({.x₀}ᗮ →L[ℝ] E') → Prop :=
      λ q, q.1 ≠ 0 ∧ injective q.2,
  have x₀_ne : x₀ ≠ 0,
  { refine λ hx₀', hx₀ _,
    rw hx₀',
    apply mem_ball_self,
    norm_num },
  -- The following suffices looks stupid but is much faster than using the change tactic.
  suffices : ∀ᶠ (p : one_jet E E') in 𝓝 (x₀, y₀, φ₀), P (f p),
  { exact this },
  apply continuous_at.eventually,
  {
    dsimp [f, one_jet],
    apply continuous_at.prod,
    exact (continuous_const.inner continuous_fst).continuous_at,
    apply continuous_at.compL,
    { apply continuous_at.compL,
      exact continuous_at_snd.comp continuous_at_snd,
      change continuous_at ((λ x, {.x}ᗮ.subtypeL.comp pr[x]ᗮ) ∘ prod.fst) (x₀, y₀, φ₀),
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


lemma loc_immersion_rel_open : is_open (immersion_sphere_rel E E') :=
begin
  dsimp only [immersion_sphere_rel],
  rw is_open_iff_mem_nhds,
  rintros ⟨x₀, y₀, φ₀⟩ (H : x₀ ∉ B → inj_on φ₀ {.x₀}ᗮ),
  change ∀ᶠ (p : one_jet E E') in 𝓝 (x₀, y₀, φ₀), _,
  by_cases hx₀ : x₀ ∈ B,
  { have : ∀ᶠ (p : one_jet E E') in 𝓝 (x₀, y₀, φ₀), p.1 ∈ B,
    { rw nhds_prod_eq,
      apply (is_open_ball.eventually_mem hx₀).prod_inl },
    apply this.mono,
    rintros ⟨x, y, φ⟩ (hx : x ∈ B) (Hx : x ∉ B),
    exact (Hx hx).elim },
  { replace H := H hx₀,
    set j₀ := subtypeL {.x₀}ᗮ,
    let f : one_jet E E' → ℝ × ({.x₀}ᗮ →L[ℝ] E') :=
      λ p, (⟪x₀, p.1⟫, (p.2.2.comp $ (subtypeL {.p.1}ᗮ).comp pr[p.1]ᗮ).comp j₀),
    let P : ℝ × ({.x₀}ᗮ →L[ℝ] E') → Prop :=
      λ q, q.1 ≠ 0 ∧ injective q.2,
    have : ∀ᶠ (p : one_jet E E') in 𝓝 (x₀, y₀, φ₀), P (f p),
    { exact loc_immersion_rel_open_aux hx₀ H },
    apply this.mono, clear this,
    rintros ⟨x, y, φ⟩ ⟨hxx₀ : ⟪x₀, x⟫ ≠ 0, Hφ⟩ (hx : x ∉ B),
    dsimp only [P, f] at Hφ,
    change inj_on φ {.x}ᗮ,
    have : range ((subtypeL {.x}ᗮ) ∘ pr[x]ᗮ ∘ j₀) = {.x}ᗮ,
    { rw set.range_comp_of_surj,
      exact subtype.range_coe,
      exact surjective_orthogonal_projection_comp_subtypeL hxx₀ },
    rw ← this, clear this,
    exact function.injective.inj_on_range Hφ },
end

lemma ample_set_univ {F : Type*} [normed_add_comm_group F] [normed_space ℝ F] :
  ample_set (univ : set F) :=
begin
  intros x _,
  rw [connected_component_in_univ, preconnected_space.connected_component_eq_univ, convex_hull_univ]
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

open submodule (hiding map_zero) rel_loc

lemma mem_slice_iff_of_not_mem {x : E} {w : E'} {φ : E →L[ℝ] E'} {p : dual_pair' E}
  (hx : x ∉ B) (y : E') : w ∈ slice R p (x, y, φ) ↔ inj_on (p.update φ w) {.x}ᗮ :=
begin
  change (x ∉ ball (0 : E) 0.9 → inj_on (p.update φ w) {.x}ᗮ) ↔ inj_on (p.update φ w) {.x}ᗮ,
  simp [hx]
end

lemma slice_eq_of_not_mem {x : E} {w : E'} {φ : E →L[ℝ] E'} {p : dual_pair' E}
  (hx : x ∉ B) (y : E') : slice R p (x, y, φ) = {w | inj_on (p.update φ w) {.x}ᗮ} :=
by { ext w, rw mem_slice_iff_of_not_mem hx y, exact iff.rfl }

open inner_product_space

@[simp] lemma subtypeL_apply' {R₁ : Type*} [semiring R₁] {M₁ : Type*} [topological_space M₁]
  [add_comm_monoid M₁] [module R₁ M₁] (p : submodule R₁ M₁) (x : p) :
  (subtypeL p : p →ₗ[R₁] M₁) x = x :=
rfl

-- In the next lemma the assumption `dim E = n + 1` is for convenience
-- using `finrank_orthogonal_span_singleton`. We could remove it to treat empty spheres...
lemma loc_immersion_rel_ample (n : ℕ) [fact (dim E = n+1)] (h : finrank ℝ E ≤ finrank ℝ E') :
  (immersion_sphere_rel E E').is_ample :=
begin
  rw is_ample_iff,
  rintro ⟨x, y, φ⟩ p h_mem,
  by_cases hx : x ∈ B,
  { apply ample_slice_of_forall,
    intros w,
    simp [hx]  },
  { have x_ne : x ≠ 0,
    { rintro rfl,
      apply hx,
      apply mem_ball_self,
      norm_num },
    have hφ : inj_on φ {.x}ᗮ := h_mem hx, clear h_mem,
    let u := (inner_product_space.to_dual ℝ E).symm p.π,
    have u_ne : u ≠ 0,
    { exact (inner_product_space.to_dual ℝ E).symm.apply_ne_zero p.pi_ne_zero },
    by_cases H : p.π.ker = {.x}ᗮ,
    { have key : ∀ w, eq_on (p.update φ w) φ {.x}ᗮ,
      { intros w x,
        rw ← H,
        exact p.update_ker_pi φ w },
      exact ample_slice_of_forall _ p  (λ w _, hφ.congr (key w).symm) },
    { obtain ⟨v', v'_in, hv', hπv'⟩ :
        ∃ v' : E,  v' ∈ {.x}ᗮ ∧ {.x}ᗮ = (p.π.ker ⊓ {.x}ᗮ) ⊔ Δ v' ∧ p.π v' = 1,
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
        refine ⟨(p.π $ pr[x]ᗮ u)⁻¹ • pr[x]ᗮ u, {.x}ᗮ.smul_mem _ (pr[x]ᗮ u).2, _, _⟩,
        { have := orthogonal_line_inf_sup_line u x,
          rw [← orthogonal_span_to_dual_symm p.π,
            span_singleton_smul_eq ne_z'.is_unit],
          exact (orthogonal_line_inf_sup_line u x).symm },
        rw [p.π.map_smul, smul_eq_mul, inv_mul_cancel ne_z] },
      let p' : dual_pair' E := { π := p.π, v := v', pairing := hπv' },
      apply ample_slice_of_ample_slice (show p'.π = p.π, from rfl),
      suffices : slice R p' (x, y, φ) = (map φ (p.π.ker ⊓ {.x}ᗮ))ᶜ,
      { rw [this],
        apply ample_of_two_le_codim,
        let Φ := φ.to_linear_map,
        suffices : 2 ≤ dim (E' ⧸ map Φ (p.π.ker ⊓ {.x}ᗮ)),
        { rw ← finrank_eq_dim,
          exact_mod_cast this },
        apply le_of_add_le_add_right,
        rw submodule.finrank_quotient_add_finrank (map Φ $ p.π.ker ⊓ {.x}ᗮ),
        have : dim (p.π.ker ⊓ {.x}ᗮ : submodule ℝ E) + 1 = n,
        { have eq := submodule.dim_sup_add_dim_inf_eq (p.π.ker ⊓ {.x}ᗮ) (span ℝ {v'}),
          have eq₁ : dim {.x}ᗮ = n,  from finrank_orthogonal_span_singleton x_ne,
          have eq₂ : p.π.ker ⊓ {.x}ᗮ ⊓ span ℝ {v'} = (⊥ : submodule ℝ E),
          { erw [inf_left_right_swap, inf_comm, ← inf_assoc, p'.inf_eq_bot, bot_inf_eq] },
          have eq₃ : dim (span ℝ {v'}) = 1, apply finrank_span_singleton p'.v_ne_zero,
          rw [← hv', eq₁, eq₃, eq₂] at eq,
          simpa using eq.symm },
        have : dim E = n+1, from fact.out _,
        linarith [finrank_map_le ℝ Φ (p.π.ker ⊓ {.x}ᗮ)] },
      ext w,
      rw mem_slice_iff_of_not_mem hx y,
      rw inj_on_iff_injective,
      let j := {.x}ᗮ.subtypeL,
      let p'' : dual_pair' {.x}ᗮ := ⟨p.π.comp j, ⟨v', v'_in⟩, hπv'⟩,
      have eq : ({.x}ᗮ : set E).restrict (p'.update φ w) = (p''.update (φ.comp j) w),
      { ext z,
        simp [dual_pair'.update] },
      have eq' : map (φ.comp j) p''.π.ker = map φ (p.π.ker ⊓ {.x}ᗮ),
      { have : map ↑j p''.π.ker = p.π.ker ⊓ {.x}ᗮ,
        { ext z,
          simp only [mem_map, continuous_linear_map.mem_ker, continuous_linear_map.coe_comp',
                     coe_subtypeL', submodule.coe_subtype, comp_app, mem_inf],
          split,
          { rintros ⟨t, ht, rfl⟩,
            rw subtypeL_apply',
            exact ⟨ht, t.2⟩ },
          { rintros ⟨hz, z_in⟩,
            exact ⟨⟨z, z_in⟩, hz, rfl⟩ }, },
        erw [← this, map_comp],
        refl },
      rw [eq, p''.injective_update_iff, mem_compl_iff, eq'],
      exact iff.rfl,
      rw ← show ({.x}ᗮ : set E).restrict φ = φ.comp j, by { ext, refl },
      exact hφ.injective } }
end

variables (E) [fact (dim E = 3)]

/- The relation of immersion of a two-sphere into its ambient Euclidean space. -/
local notation `𝓡_imm` := immersion_sphere_rel E E

lemma is_closed_pair : is_closed ({0, 1} : set ℝ) :=
(by simp : ({0, 1} : set ℝ).finite).is_closed

variables {E} (ω : orientation ℝ E (fin 3))

def loc_formal_eversion_aux_φ (t : ℝ) (x : E) : E →L[ℝ] E :=
rot ω.volume_form (t, x) - (2 * t) • (submodule.subtypeL (Δ x) ∘L orthogonal_projection (Δ x))

lemma smooth_at_loc_formal_eversion_aux_φ {p : ℝ × E} (hx : p.2 ≠ 0) :
  cont_diff_at ℝ ∞ (uncurry (loc_formal_eversion_aux_φ ω)) p :=
begin
  refine (cont_diff_rot ω.volume_form hx).sub _,
  refine cont_diff_at.smul (cont_diff_at_const.mul cont_diff_at_fst) _,
  exact (cont_diff_at_orthogonal_projection_singleton hx).comp p cont_diff_at_snd
end

include ω
def loc_formal_eversion_aux : htpy_jet_sec E E :=
{ f := λ (t : ℝ) (x : E), (1 - 2 * smooth_step t) • x,
  φ := λ t x, smooth_step (∥x∥ ^ 2) • loc_formal_eversion_aux_φ ω (smooth_step t) x,
  f_diff := cont_diff.smul (cont_diff_const.sub $ cont_diff_const.mul $
    smooth_step.smooth.comp cont_diff_fst) cont_diff_snd,
  φ_diff := begin
    refine cont_diff_iff_cont_diff_at.mpr (λ x, _),
    cases eq_or_ne x.2 0 with hx hx,
    { refine cont_diff_at_const.congr_of_eventually_eq _, exact 0,
      have : ((λ x, ∥x∥ ^ 2) ⁻¹' Iio (1/4)) ∈ 𝓝 (0 : E),
      { refine is_open.mem_nhds _ _,
        exact (is_open_Iio.preimage (cont_diff_norm_sq : 𝒞 ∞ _).continuous),
        simp_rw [mem_preimage, norm_zero, zero_pow two_pos, mem_Iio],
        norm_num },
      have : ((λ x, smooth_step (∥x∥ ^ 2)) ⁻¹' {0}) ∈ 𝓝 (0 : E),
      { refine mem_of_superset this _,
        rw @preimage_comp _ _ _ _ smooth_step,
        refine preimage_mono _,
        intros x hx,
        rw [mem_preimage, mem_singleton_iff, smooth_step.of_lt hx] },
      have : ((λ p : ℝ × E, smooth_step (∥p.2∥ ^ 2)) ⁻¹' {0}) ∈ 𝓝 x,
      { rw [← hx] at this, exact continuous_at_snd.preimage_mem_nhds this },
      refine eventually_of_mem this _,
      rintro ⟨t, x⟩ hx,
      simp_rw [mem_preimage, mem_singleton_iff] at hx,
      show smooth_step (∥x∥ ^ 2) • loc_formal_eversion_aux_φ ω (smooth_step t) x = 0,
      simp_rw [hx, zero_smul] },
    refine cont_diff_at.smul _ _,
    refine (smooth_step.smooth.comp $ cont_diff_norm_sq.comp cont_diff_snd).cont_diff_at,
    exact (smooth_at_loc_formal_eversion_aux_φ ω
      (show (prod.map smooth_step id x).2 ≠ 0, from hx)).comp x
      (smooth_step.smooth.prod_map cont_diff_id).cont_diff_at,
     end }

/-- A formal eversion of a two-sphere into its ambient Euclidean space. -/
def loc_formal_eversion : htpy_formal_sol 𝓡_imm :=
{ is_sol := begin
    intros t x,
    change x ∉ B →
      inj_on (smooth_step (∥x∥ ^ 2) • loc_formal_eversion_aux_φ ω (smooth_step t) x) {.x}ᗮ,
    intros hx,
    have h2x : smooth_step (∥x∥ ^ 2) = 1,
    { refine smooth_step.of_gt _,
      rw [mem_ball, not_lt, dist_zero_right] at hx,
      refine (show (3 : ℝ)/4 < 0.9 ^ 2, by norm_num).trans_le _,
      rwa [sq_le_sq, show |(0.9 : ℝ)| = 0.9, by norm_num, abs_norm_eq_norm] },
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
  (loc_formal_eversion ω t).φ x v = smooth_step (∥x∥ ^ 2) •
    (rot ω.volume_form (smooth_step t, x) v -
    (2 * smooth_step t) • orthogonal_projection (Δ x) v) :=
rfl

lemma loc_formal_eversion_zero (x : E) : (loc_formal_eversion ω 0).f x = x :=
by simp

lemma loc_formal_eversion_one (x : E) : (loc_formal_eversion ω 1).f x = -x :=
by simp [show (1 : ℝ) - 2 = -1, by norm_num]

lemma loc_formal_eversion_hol_at_zero {t : ℝ} (ht : t < 1/4) {x : E}
  (hx : smooth_step (∥x∥ ^ 2) = 1) : (loc_formal_eversion ω t).is_holonomic_at x :=
by simp_rw [jet_sec.is_holonomic_at, loc_formal_eversion_f, continuous_linear_map.ext_iff,
    loc_formal_eversion_φ, smooth_step.of_lt ht, hx, rot_zero, mul_zero, zero_smul, sub_zero,
    show (has_smul.smul (1 : ℝ) : E → E) = id, from funext (one_smul ℝ), fderiv_id, function.id_def,
    eq_self_iff_true, implies_true_iff]

lemma loc_formal_eversion_hol_at_one {t : ℝ} (ht : 3/4 < t) {x : E}
  (hx : smooth_step (∥x∥ ^ 2) = 1) : (loc_formal_eversion ω t).is_holonomic_at x :=
begin
  simp_rw [jet_sec.is_holonomic_at, loc_formal_eversion_f, continuous_linear_map.ext_iff,
    loc_formal_eversion_φ, smooth_step.of_gt ht, hx],
  intro v,
  simp_rw [mul_one, show (1 : ℝ) - 2 = -1, by norm_num,
    show (has_smul.smul (-1 : ℝ) : E → E) = λ x, - x, from funext (λ v, by rw [neg_smul, one_smul]),
    fderiv_neg, fderiv_id', continuous_linear_map.neg_apply, continuous_linear_map.id_apply],
  obtain ⟨v', hv', v, hv, rfl⟩ := submodule.exists_sum_mem_mem_orthogonal (Δ x) v,
  simp_rw [continuous_linear_map.map_add, rot_one _ x hv, rot_eq_of_mem_span _ ((1 : ℝ), x) hv'],
  simp_rw [neg_add, submodule.coe_add, orthogonal_projection_eq_self_iff.mpr hv',
    orthogonal_projection_mem_subspace_orthogonal_complement_eq_zero hv, submodule.coe_zero,
    add_zero, two_smul, one_smul],
  abel
end

lemma loc_formal_eversion_hol :
  ∀ᶠ (p : ℝ × E) near {0, 1} ×ˢ 𝕊², (loc_formal_eversion ω p.1).is_holonomic_at p.2 :=
begin
  have : (Iio (1/4 : ℝ) ∪ Ioi (3/4)) ×ˢ ((λ x, ∥x∥ ^ 2) ⁻¹' Ioi (3/4)) ∈
    𝓝ˢ (({0, 1} : set ℝ) ×ˢ 𝕊²),
  { refine (is_open.mem_nhds_set _).mpr _,
    exact (is_open_Iio.union is_open_Ioi).prod
      (is_open_Ioi.preimage (cont_diff_norm_sq : 𝒞 ∞ _).continuous),
    rintro ⟨s, x⟩ ⟨hs, hx⟩,
    refine ⟨_, _⟩,
    simp_rw [mem_insert_iff, mem_singleton_iff] at hs,
    rcases hs with rfl|rfl,
    exact or.inl (show (0 : ℝ) < 1 / 4, by norm_num),
    exact or.inr (show (3 / 4 : ℝ) < 1, by norm_num),
    simp_rw [mem_sphere_zero_iff_norm] at hx,
    simp_rw [mem_preimage, hx, one_pow, mem_Ioi],
    norm_num },
  have : (Iio (1/4 : ℝ) ∪ Ioi (3/4)) ×ˢ ((λ x, smooth_step (∥x∥ ^ 2)) ⁻¹' {1}) ∈
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
  (𝒞 ∞ (uncurry f)) ∧
  (∀ x ∈ 𝕊², f 0 x = x) ∧
  (∀ x ∈ 𝕊², f 1 x = -x) ∧
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
    zero_lt_one ({0, 1} ×ˢ 𝕊²) (is_closed_pair.prod is_closed_sphere) 𝕊² (is_compact_sphere 0 1) (loc_formal_eversion_hol ω),
  refine ⟨f, h₁, _, _, _⟩,
  { intros x hx, rw [h₂ (0, x) (mk_mem_prod (by simp) hx), loc_formal_eversion_zero] },
  { intros x hx, rw [h₂ (1, x) (mk_mem_prod (by simp) hx), loc_formal_eversion_one] },
  { exact λ t ht, sphere_immersion_of_sol _ (λ x hx, h₃ x hx t ht) },
end

/- Stating the full statement with all type-class arguments and no uncommon notation. -/
example (E : Type*) [inner_product_space ℝ E] [fact (finrank ℝ E = 3)] :
  ∃ f : ℝ → E → E,
  (cont_diff ℝ ⊤ (uncurry f)) ∧
  (∀ x ∈ sphere (0 : E) 1, f 0 x = x) ∧
  (∀ x ∈ sphere (0 : E) 1, f 1 x = -x) ∧
  ∀ t ∈ unit_interval, sphere_immersion (f t) :=
sphere_eversion_of_loc

end sphere_eversion
