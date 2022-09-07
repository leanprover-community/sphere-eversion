import to_mathlib.geometry.manifold.sphere
import global.gromov
import global.twist_one_jet_sec
import global.rotation
-- import interactive_expr
-- set_option trace.filter_inst_type true

noncomputable theory

open metric finite_dimensional set function
open_locale manifold

section general

variables
{E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
{H : Type*} [topological_space H] (I : model_with_corners ℝ E H)
{M : Type*} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]

{E' : Type*} [normed_add_comm_group E'] [normed_space ℝ E']
{H' : Type*} [topological_space H'] (I' : model_with_corners ℝ E' H')
{M' : Type*} [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M']

{F : Type*} [normed_add_comm_group F] [normed_space ℝ F]
{G : Type*} [topological_space G] (J : model_with_corners ℝ F G)
(N : Type*) [topological_space N] [charted_space G N] [smooth_manifold_with_corners J N]

local notation `TM` := tangent_space I
local notation `TM'` := tangent_space I'
local notation `HJ` := model_prod (model_prod H H') (E →L[ℝ] E')
local notation `ψJ` := chart_at HJ

/-- A map between manifolds is an immersion if it is differentiable and its differential at
any point is injective. Note the formalized definition doesn't require differentiability.
If `f` is not differentiable at `m` then, by definition, `mfderiv I I' f m` is zero, which
is not injective unless the source dimension is zero, which implies differentiability. -/
def immersion (f : M → M') : Prop := ∀ m, injective (mfderiv I I' f m)

variables (M M')

/-- The relation of immersions for maps between two manifolds. -/
def immersion_rel : rel_mfld I M I' M' := {σ | injective σ.2}

variables {M M'}

@[simp] lemma mem_immersion_rel_iff {σ : one_jet_bundle I M I' M'} :
  σ ∈ immersion_rel I M I' M' ↔ injective (σ.2 : tangent_space I _ →L[ℝ] tangent_space I' _) :=
iff.rfl

/-- A characterisation of the immersion relation in terms of a local chart. -/
lemma mem_immersion_rel_iff' {σ σ' : one_jet_bundle I M I' M'} (hσ' : σ' ∈ (ψJ σ).source) :
  σ' ∈ immersion_rel I M I' M' ↔ injective (ψJ σ σ').2 :=
by simp [mem_immersion_rel_iff, one_jet_bundle_chart_at' I M I' M' hσ']

lemma chart_at_image_immersion_rel_eq {σ : one_jet_bundle I M I' M'} :
  (ψJ σ) '' ((ψJ σ).source ∩ immersion_rel I M I' M') = (ψJ σ).target ∩ {q : HJ | injective q.2} :=
local_equiv.is_image.image_eq $ λ σ' hσ', (mem_immersion_rel_iff' I I' hσ').symm

lemma immersion_iff_one_jet (f : M → M') :
  immersion I I' f ↔ ∀ m, one_jet_ext I I' f m ∈ immersion_rel I M I' M' :=
by simp [immersion, one_jet_ext, immersion_rel]

variables [finite_dimensional ℝ E] [finite_dimensional ℝ E']

lemma immersion_rel_open :
  is_open (immersion_rel I M I' M') :=
begin
  simp_rw [charted_space.is_open_iff HJ (immersion_rel I M I' M'), chart_at_image_immersion_rel_eq],
  refine λ σ, (ψJ σ).open_target.inter _,
  convert is_open_univ.prod continuous_linear_map.is_open_injective,
  { ext, simp, },
  { apply_instance, },
  { apply_instance, },
end

@[simp] lemma immersion_rel_slice_eq {m : M} {m' : M'} {p : dual_pair' $ tangent_space I m}
  {φ : tangent_space I m →L[ℝ] tangent_space I' m'} (hφ : injective φ) :
  (immersion_rel I M I' M').slice ⟨(m, m'), φ⟩ p = (p.π.ker.map φ)ᶜ :=
set.ext_iff.mpr $ λ w, p.injective_update_iff hφ

lemma immersion_rel_ample (h : finrank ℝ E < finrank ℝ E') :
  (immersion_rel I M I' M').ample :=
begin
  rw [rel_mfld.ample_iff],
  rintros ⟨⟨m, m'⟩, φ : tangent_space I m →L[ℝ] tangent_space I' m'⟩
          (p : dual_pair' (tangent_space I m)) (hφ : injective φ),
  haveI : finite_dimensional ℝ (tangent_space I m) := (by apply_instance : finite_dimensional ℝ E),
  have hcodim := p.two_le_rank_of_rank_lt_rank h φ,
  rw [immersion_rel_slice_eq I I' hφ],
  exact ample_of_two_le_codim hcodim,
end

/-- This is lemma `lem:open_ample_immersion` from the blueprint. -/
lemma immersion_rel_open_ample (h : finrank ℝ E < finrank ℝ E') :
  is_open (immersion_rel I M I' M') ∧ (immersion_rel I M I' M').ample :=
⟨immersion_rel_open I I', immersion_rel_ample I I' h⟩

end general

section generalbis

variables
{E : Type*} [normed_add_comm_group E] [normed_space ℝ E] [finite_dimensional ℝ E]
{H : Type*} [topological_space H] (I : model_with_corners ℝ E H) [model_with_corners.boundaryless I]
{M : Type*} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]

{E' : Type*} [normed_add_comm_group E'] [normed_space ℝ E'] [finite_dimensional ℝ E']
{H' : Type*} [topological_space H'] (I' : model_with_corners ℝ E' H') [model_with_corners.boundaryless I']
{M' : Type*} [metric_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M']

variables [finite_dimensional ℝ E] [finite_dimensional ℝ E']

variables
  {EP : Type*} [normed_add_comm_group EP] [normed_space ℝ EP] [finite_dimensional ℝ EP]
  {HP : Type*} [topological_space HP] {IP : model_with_corners ℝ EP HP} [model_with_corners.boundaryless IP]
  {P : Type*} [topological_space P] [charted_space HP P] [smooth_manifold_with_corners IP P]
  {C : set (P × M)} {ε : M → ℝ}

include I I' M' IP

variables (I M I' M' IP P)

/-- parametric h-principle for immersions. -/
theorem immersion_rel_satisfies_h_principle_with
  [nonempty P] [t2_space P] [sigma_compact_space P] [locally_compact_space P]
  [nonempty M] [t2_space M] [sigma_compact_space M] [locally_compact_space M]
  [nonempty M'] [t2_space M'] [locally_compact_space M'] [sigma_compact_space M']
  (h : finrank ℝ E < finrank ℝ E') (hC : is_closed C)
  (hε_pos : ∀ x, 0 < ε x) (hε_cont : continuous ε) :
  (immersion_rel I M I' M').satisfies_h_principle_with IP C ε :=
by exact (immersion_rel_ample I I' h).satisfies_h_principle_with (immersion_rel_open I I')
     hC hε_pos hε_cont

end generalbis

section sphere_eversion

variables (E : Type*) [inner_product_space ℝ E] [fact (finrank ℝ E = 3)]

local attribute [instance] fact_finite_dimensional_of_finrank_eq_succ

local notation `𝕊²` := sphere (0 : E) 1

/- Maybe the next two lemmas won't be used directly, but they should be done first as
sanity checks. -/

lemma immersion_inclusion_sphere : immersion (𝓡 2) 𝓘(ℝ, E) (λ x : 𝕊², (x : E)) :=
mfderiv_coe_sphere_injective

lemma immersion_antipodal_sphere : immersion (𝓡 2) 𝓘(ℝ, E) (λ x : 𝕊², -(x : E)) :=
begin
  intros x,
  change injective (mfderiv (𝓡 2) 𝓘(ℝ, E) (-(λ x : 𝕊², (x:E))) x),
  rw mfderiv_neg,
  exact neg_injective.comp (mfderiv_coe_sphere_injective x),
end

/- The relation of immersion of a two-sphere into its ambient Euclidean space. -/
local notation `𝓡_imm` := immersion_rel (𝓡 2) 𝕊² 𝓘(ℝ, E) E

variables (ω : orientation ℝ E (fin 3))

lemma smooth_bs :
  smooth (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E)
    (λ p : ℝ × 𝕊², ((1-p.1) • p.2 + p.1 • (-p.2) : E)) :=
begin
  refine (cont_mdiff.smul _ _).add (cont_mdiff_fst.smul _),
  { exact (cont_diff_const.sub cont_diff_id).cont_mdiff.comp cont_mdiff_fst },
  { exact cont_mdiff_coe_sphere.comp cont_mdiff_snd },
  { exact (cont_diff_neg.cont_mdiff.comp cont_mdiff_coe_sphere).comp cont_mdiff_snd },
end

def formal_eversion_aux : family_one_jet_sec (𝓡 2) (𝕊²) 𝓘(ℝ, E) E 𝓘(ℝ, ℝ) ℝ :=
family_join
  (smooth_bs E) $
  family_twist
    (drop (one_jet_ext_sec ⟨(coe : 𝕊² → E), cont_mdiff_coe_sphere⟩))
    (λ p : ℝ × 𝕊², rot ω.volume_form (p.1, p.2))
    begin
      intros p,
      have : smooth_at (𝓘(ℝ, ℝ × E)) 𝓘(ℝ, E →L[ℝ] E) (rot ω.volume_form) (p.1, p.2),
      { refine (cont_diff_rot ω.volume_form _).cont_mdiff_at,
        exact ne_zero_of_mem_unit_sphere p.2 },
      refine this.comp p (smooth.smooth_at _),
      exact smooth_fst.prod_mk (cont_mdiff_coe_sphere.comp smooth_snd),
    end

/-- A formal eversion of a two-sphere into its ambient Euclidean space. -/
def formal_eversion : htpy_formal_sol 𝓡_imm :=
{ is_sol' := λ t x, (ω.isometry_rot t x).injective.comp (mfderiv_coe_sphere_injective x),
  .. formal_eversion_aux E ω }

lemma formal_eversion_zero (x : 𝕊²) : (formal_eversion E ω 0).bs x = x :=
show (1-0 : ℝ) • (x : E) + (0 : ℝ) • (-x : E) = x, by simp

lemma formal_eversion_one (x : 𝕊²) : (formal_eversion E ω 1).bs x = -x :=
show (1-1 : ℝ) • (x : E) + (1 : ℝ) • (-x : E) = -x, by simp

lemma formal_eversion_hol_at_zero :
  (formal_eversion E ω 0).to_one_jet_sec.is_holonomic :=
begin
  intros x,
  change mfderiv (𝓡 2) 𝓘(ℝ, E) (λ y : 𝕊², ((1:ℝ) - 0) • (y:E) + (0:ℝ) • -y) x
    = (rot ω.volume_form (0, x)).comp (mfderiv (𝓡 2) 𝓘(ℝ, E) (λ y : 𝕊², (y:E)) x),
  simp only [rot_zero, continuous_linear_map.id_comp],
  congr,
  ext y,
  simp,
end

lemma formal_eversion_hol_at_one :
  (formal_eversion E ω 1).to_one_jet_sec.is_holonomic :=
begin
  intros x,
  change mfderiv (𝓡 2) 𝓘(ℝ, E) (λ y : 𝕊², ((1:ℝ) - 1) • (y:E) + (1:ℝ) • -y) x
    = (rot ω.volume_form (1, x)).comp (mfderiv (𝓡 2) 𝓘(ℝ, E) (λ y : 𝕊², (y:E)) x),
  transitivity mfderiv (𝓡 2) 𝓘(ℝ, E) (-(λ y : 𝕊², (y:E))) x,
  { congr' 2,
    ext y,
    simp, },
  ext v,
  simp only [mfderiv_neg, continuous_linear_map.coe_comp', comp_app,
    continuous_linear_map.neg_apply],
  rw rot_one,
  convert continuous_linear_map.mem_range_self _ _,
  rw range_mfderiv_coe_sphere,
end

lemma formal_eversion_hol_near_zero_one' :
  ∀ᶠ (s : ℝ) near {0, 1}, (formal_eversion E ω s).to_one_jet_sec.is_holonomic :=
sorry

lemma formal_eversion_hol_near_zero_one : ∀ᶠ (s : ℝ × 𝕊²) near {0, 1} ×ˢ univ,
  (formal_eversion E ω s.1).to_one_jet_sec.is_holonomic_at s.2 :=
sorry

theorem sphere_eversion : ∃ f : ℝ → 𝕊² → E,
  (cont_mdiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E) ∞ (uncurry f)) ∧
  (f 0 = λ x, x) ∧
  (f 1 = λ x, -x) ∧
  ∀ t, immersion (𝓡 2) 𝓘(ℝ, E) (f t) :=
begin
  classical,
  let ω : orientation ℝ E (fin 3) :=
    (fin_std_orthonormal_basis (fact.out _ : finrank ℝ E = 3)).to_basis.orientation,
  have rankE := fact.out (finrank ℝ E = 3),
  haveI : finite_dimensional ℝ E :=
    finite_dimensional_of_finrank_eq_succ rankE,
  have ineq_rank : finrank ℝ (euclidean_space ℝ (fin 2)) < finrank ℝ E := by simp [rankE],
  let ε : 𝕊² → ℝ := λ x, 1,
  have hε_pos : ∀ x, 0 < ε x,
    from λ x, zero_lt_one,
  have hε_cont : continuous ε := continuous_const,
  haveI : nontrivial E := nontrivial_of_finrank_eq_succ (fact.out _ : finrank ℝ E = 3),
  haveI : nonempty ↥(sphere 0 1 : set E) :=
    (normed_space.sphere_nonempty.mpr zero_le_one).to_subtype,
  rcases (immersion_rel_satisfies_h_principle_with (𝓡 2) 𝕊² 𝓘(ℝ, E) E 𝓘(ℝ, ℝ) ℝ ineq_rank
    ((finite.is_closed (by simp : ({0, 1} : set ℝ).finite)).prod is_closed_univ) hε_pos hε_cont).bs
    (formal_eversion E ω) (formal_eversion_hol_near_zero_one E ω) with ⟨f, h₁, h₂, -, h₅⟩,
  have := h₂.nhds_set_forall_mem,
  refine ⟨f, h₁, _, _, h₅⟩,
  { ext x,
    rw [this (0, x) (by simp)],
    exact formal_eversion_zero E ω x },
  { ext x,
    rw [this (1, x) (by simp)],
    exact formal_eversion_one E ω x },
end

end sphere_eversion
