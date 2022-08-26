import geometry.manifold.instances.sphere

import global.gromov

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

/-- A map between manifolds is an immersion if it is differentiable and its differential at
any point is injective. Note the formalized definition doesn't require differentiability.
If `f` is not differentiable at `m` then, by definition, `mfderiv I I' f m` is zero, which
is not injective unless the source dimension is zero, which implies differentiability. -/
def immersion (f : M → M') : Prop := ∀ m, injective (mfderiv I I' f m)

variables (M M')

/-- The relation of immersions for maps between two manifolds. -/
def immersion_rel : rel_mfld I M I' M' := {σ | injective σ.2}

@[simp] lemma immersion_rel_preslice_eq {m : M} {m' : M'} {p : dual_pair' $ tangent_space I m}
  {φ : tangent_space I m →L[ℝ] tangent_space I' m'} (hφ : injective φ) :
  (immersion_rel I M I' M').slice ⟨(m, m'), φ⟩ p = (p.π.ker.map φ)ᶜ :=
set.ext_iff.mpr $ λ w, p.injective_update_iff hφ

variables {M M'}

lemma immersion_iff_one_jet (f : M → M') :
  immersion I I' f ↔ ∀ m, one_jet_ext I I' f m ∈ immersion_rel I M I' M' :=
by simp [immersion, one_jet_ext, immersion_rel]

variables [finite_dimensional ℝ E] [finite_dimensional ℝ E']

lemma immersion_rel_open :
  is_open (immersion_rel I M I' M') :=
sorry

lemma immersion_rel_ample (h : finrank ℝ E < finrank ℝ E') :
  (immersion_rel I M I' M').ample :=
begin
  rw [rel_mfld.ample_iff],
  rintros ⟨⟨m, m'⟩, φ : tangent_space I m →L[ℝ] tangent_space I' m'⟩
          (p : dual_pair' (tangent_space I m)) (hφ : injective φ),
  haveI : finite_dimensional ℝ (tangent_space I m) := (by apply_instance : finite_dimensional ℝ E),
  have hcodim := p.two_le_rank_of_rank_lt_rank h φ,
  rw [immersion_rel_preslice_eq I M I' M' hφ],
  exact ample_of_two_le_codim hcodim,
end

/-- This is lemma `lem:open_ample_immersion` from the blueprint. -/
lemma immersion_rel_open_ample (h : finrank ℝ E < finrank ℝ E') :
  is_open (immersion_rel I M I' M') ∧ (immersion_rel I M I' M').ample :=
⟨immersion_rel_open I I', immersion_rel_ample I I' h⟩

end general

section generalbis

variables
{E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
{H : Type*} [topological_space H] (I : model_with_corners ℝ E H)
{M : Type*} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]

{E' : Type*} [normed_add_comm_group E'] [normed_space ℝ E']
{H' : Type*} [topological_space H'] (I' : model_with_corners ℝ E' H')
{M' : Type*} [metric_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M']

variables [finite_dimensional ℝ E] [finite_dimensional ℝ E']

variables
  {EP : Type*} [normed_add_comm_group EP] [normed_space ℝ EP]
  {HP : Type*} [topological_space HP] {IP : model_with_corners ℝ EP HP}
  {P : Type*} [topological_space P] [charted_space HP P] [smooth_manifold_with_corners IP P]
  {C₁ : set P} {C₂ : set M} {ε : M → ℝ}

include I I' M' IP

variables (I M I' M' IP P)

/-- parametric h-principle for immersions. -/
theorem immersion_rel_satisfies_h_principle_with
  (h : finrank ℝ E < finrank ℝ E') (hC₁ : is_closed C₁) (hC₂ : is_closed C₂)
  (hε_pos : ∀ x, 0 < ε x) (hε_cont : continuous ε) :
  (immersion_rel I M I' M').satisfies_h_principle_with IP  C₁ C₂ ε :=
by apply (immersion_rel_ample I I' h).satisfies_h_principle_with (immersion_rel_open I I')
     hC₁ hC₂ hε_pos hε_cont

end generalbis

section sphere_eversion

variables (E : Type*) [inner_product_space ℝ E] {n : ℕ} [fact (finrank ℝ E = 3)]

/- Maybe the next two lemmas won't be used directly, but they should be done first as
sanity checks. -/

lemma immersion_inclusion_sphere : immersion (𝓡 2) 𝓘(ℝ, E) (λ x : sphere (0 : E) 1, (x : E)) :=
sorry

lemma immersion_antipodal_sphere : immersion (𝓡 2) 𝓘(ℝ, E) (λ x : sphere (0 : E) 1, -(x : E)) :=
sorry

local notation `𝕊²` := sphere (0 : E) 1

/- The relation of immersion of a two-sphere into its ambiant Euclidean space. -/
local notation `𝓡_imm` := immersion_rel (𝓡 2) 𝕊² 𝓘(ℝ, E) E

/-- A formal eversion of a two-sphere into its ambiant Euclidean space.
Right now this is waiting for Heather's work on rotations. -/
def formal_eversion : family_formal_sol 𝓘(ℝ, ℝ) ℝ 𝓡_imm :=
{ bs := λ t x, (1-t) • x + t • (-x),
  ϕ := λ t x, sorry, -- Here we need to make sure we stay holonomic for t close to 0 and 1
  smooth' := sorry,
  is_sol' := sorry }

lemma formal_eversion_zero (x : 𝕊²) : (formal_eversion E 0).bs x = x :=
show (1-0 : ℝ) • (x : E) + (0 : ℝ) • (-x : E) = x, by simp

lemma formal_eversion_one (x : 𝕊²) : (formal_eversion E 1).bs x = -x :=
show (1-1 : ℝ) • (x : E) + (1 : ℝ) • (-x : E) = -x, by simp

lemma formal_eversion_hol_near_zero_one :
  ∀ᶠ (s : ℝ) near {0, 1}, (formal_eversion E s).to_one_jet_sec.is_holonomic :=
sorry

lemma formal_eversion_hol_near_empty :
  ∀ᶠ (x : 𝕊²) near ∅, ∀ s, (formal_eversion E s).to_one_jet_sec.is_holonomic_at x :=
sorry

theorem sphere_eversion : ∃ f : ℝ → 𝕊² → E,
  (cont_mdiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E) ∞ (uncurry f)) ∧
  (f 0 = λ x, x) ∧
  (f 1 = λ x, -x) ∧
  ∀ t, immersion (𝓡 2) 𝓘(ℝ, E) (f t) :=
begin
  have rankE := fact.out (finrank ℝ E = 3),
  haveI : finite_dimensional ℝ E :=
    finite_dimensional_of_finrank_eq_succ rankE,
  have ineq_rank : finrank ℝ (euclidean_space ℝ (fin 2)) < finrank ℝ E := by simp [rankE],
  let ε : 𝕊² → ℝ := λ x, 1,
  have hε_pos : ∀ x, 0 < ε x,
    from λ x, zero_lt_one,
  have hε_cont : continuous ε := continuous_const,
  rcases (immersion_rel_satisfies_h_principle_with (𝓡 2) 𝕊² 𝓘(ℝ, E) E 𝓘(ℝ, ℝ) ℝ ineq_rank
    (finite.is_closed (by simp : ({0, 1} : set ℝ).finite)) (is_closed_empty : is_closed  (∅ : set 𝕊²)) hε_pos hε_cont).bs
    (formal_eversion E)(formal_eversion_hol_near_zero_one E) (formal_eversion_hol_near_empty E)
    with ⟨f, h₁, h₂, -, -, h₅⟩,
  have := h₂.nhds_set_forall_mem,
  refine ⟨f, h₁, _, _, h₅⟩,
  { ext x,
    rw [this 0 (by simp)],
    exact formal_eversion_zero E x },
  { ext x,
    rw [this 1 (by simp)],
    exact formal_eversion_one E x },
end

end sphere_eversion
