/-
Copyright © 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/

import to_mathlib.geometry.manifold.vector_bundle.basic
import analysis.normed_space.operator_norm

/-!
# The smooth vector bundle of continuous (semi)linear maps

We define the smooth vector bundle of continuous (semi)linear maps between two
vector bundles over the same base.
-/

noncomputable theory

open bundle set continuous_linear_map

variables {𝕜 𝕜₁ 𝕜₂ B VB VE₁ VE₂ HB HE₁ HE₂ : Type*}
variables [nondiscrete_normed_field 𝕜] [nondiscrete_normed_field 𝕜₁] [nondiscrete_normed_field 𝕜₂]
variables [normed_group VB] [normed_space 𝕜 VB]
variables [normed_group VE₁] [normed_space 𝕜₁ VE₁] [normed_group VE₂] [normed_space 𝕜 VE₂]
variables [topological_space HB] [topological_space HE₁] [topological_space HE₂]
variables (IB : model_with_corners 𝕜 VB HB)
variables (IE₁ : model_with_corners 𝕜₁ VE₁ HE₁) (IE₂ : model_with_corners 𝕜 VE₂ HE₂)
variables (F₁ F₂ : Type*) (E₁ E₂ : B → Type*)
variables [∀ x, normed_group (E₁ x)] [∀ x, normed_space 𝕜₁ (E₁ x)]
variables [∀ x, normed_group (E₂ x)] [∀ x, normed_space 𝕜₂ (E₂ x)]
variables [normed_group F₁] [normed_space 𝕜 F₁] [normed_group F₂] [normed_space 𝕜 F₂]
variables [topological_space B] [charted_space HB B]
variables [topological_space (total_space E₁)] [charted_space HE₁ (total_space E₁)]
variables [topological_space (total_space E₂)] [charted_space HE₂ (total_space E₂)]
variables (σ : 𝕜₁ →+* 𝕜₂)
variables [∀ x, normed_space 𝕜 (E₂ x)] [∀ x, smul_comm_class 𝕜₂ 𝕜 (E₂ x)]

namespace smooth_vector_bundle

variables {F₁ E₁ F₂ E₂} (e₁ e₁' : trivialization IB IE₁ F₁ E₁)
  (e₂ e₂' : trivialization IB IE₂ F₂ E₂)
variables [ring_hom_isometric σ]

instance {B : Type*} {F : Type*} [normed_group F] (b : B) :
  normed_group (bundle.trivial B F b) := ‹normed_group F›

instance {B : Type*} {F : Type*} [normed_group F] [normed_space 𝕜 F] (b : B) :
  normed_space 𝕜 (bundle.trivial B F b) := ‹normed_space 𝕜 F›

instance : charted_space (model_prod H F) (total_space (trivial B F)) :=
sorry

-- variables (I I' B F)
-- namespace trivial_smooth_vector_bundle

-- /-- Local trivialization for trivial bundle. -/
-- def trivialization : trivialization I (I.prod 𝓘(𝕜, F)) F (bundle.trivial B F) :=
-- { smooth_on_to_fun := sorry,
--   smooth_on_inv_fun := sorry,
--   ..topological_vector_bundle.trivial_topological_vector_bundle.trivialization 𝕜 B F }


-- lemma trivialization.coord_change (b : B) :
--   (trivialization B I F).coord_change (trivialization B I F) b = continuous_linear_equiv.refl 𝕜 F :=
-- topological_vector_bundle.trivial_topological_vector_bundle.trivialization.coord_change 𝕜 B F b

-- instance trivial_bundle.smooth_vector_bundle :
--   smooth_vector_bundle I (I.prod 𝓘(𝕜, F)) F (bundle.trivial B F) :=
-- { trivialization_atlas := {trivial_smooth_vector_bundle.trivialization B I F},
--   trivialization_at := λ x, trivial_smooth_vector_bundle.trivialization B I F,
--   mem_base_set_trivialization_at := mem_univ,
--   trivialization_mem_atlas := λ x, mem_singleton _,
--   total_space_mk_inducing := λ b, ⟨begin
--     have : (λ (x : trivial B F b), x) = @id F, by { ext x, refl },
--     simp only [total_space.topological_space, induced_inf, induced_compose, function.comp,
--       total_space.proj, induced_const, top_inf_eq, trivial.proj_snd, id.def,
--       trivial.topological_space, this, induced_id],
--   end⟩,
--   smooth_on_coord_change := begin
--     intros e he e' he',
--     rw [mem_singleton_iff.mp he, mem_singleton_iff.mp he'],
--     simp_rw [trivialization.coord_change],
--     exact smooth_on_const
--   end }

namespace pretrivialization

/-- Assume `eᵢ` and `eᵢ'` are trivializations of the bundles `Eᵢ` over base `B` with fiber `Fᵢ`
(`i ∈ {1,2}`), then `continuous_linear_map_coord_change σ e₁ e₁' e₂ e₂'` is the coordinate change
function between the two induced (pre)trivializations
`pretrivialization.continuous_linear_map σ e₁ e₂` and
`pretrivialization.continuous_linear_map σ e₁' e₂'` of `bundle.continuous_linear_map`. -/
def continuous_linear_map_coord_change (b : B) : (F₁ →SL[σ] F₂) →L[𝕜₂] F₁ →SL[σ] F₂ :=
((e₁'.coord_change e₁ b).symm.arrow_congrSL (e₂.coord_change e₂' b) :
  (F₁ →SL[σ] F₂) ≃L[𝕜₂] F₁ →SL[σ] F₂)

variables {σ e₁ e₁' e₂ e₂'}
variables [Π x : B, topological_space (E₁ x)] [smooth_vector_bundle 𝕜₁ F₁ E₁]
variables [Π x : B, topological_space (E₂ x)] [smooth_vector_bundle 𝕜₂ F₂ E₂]

lemma continuous_on_continuous_linear_map_coord_change
  (he₁ : e₁ ∈ trivialization_atlas 𝕜₁ F₁ E₁) (he₁' : e₁' ∈ trivialization_atlas 𝕜₁ F₁ E₁)
  (he₂ : e₂ ∈ trivialization_atlas 𝕜₂ F₂ E₂) (he₂' : e₂' ∈ trivialization_atlas 𝕜₂ F₂ E₂) :
  continuous_on (continuous_linear_map_coord_change σ e₁ e₁' e₂ e₂')
    ((e₁.base_set ∩ e₂.base_set) ∩ (e₁'.base_set ∩ e₂'.base_set)) :=
begin
  have h₁ := (compSL F₁ F₂ F₂ σ (ring_hom.id 𝕜₂)).continuous,
  have h₂ := (continuous_linear_map.flip (compSL F₁ F₁ F₂ (ring_hom.id 𝕜₁) σ)).continuous,
  have h₃ := (continuous_on_coord_change e₁' he₁' e₁ he₁),
  have h₄ := (continuous_on_coord_change e₂ he₂ e₂' he₂'),
  refine ((h₁.comp_continuous_on (h₄.mono _)).clm_comp (h₂.comp_continuous_on (h₃.mono _))).congr _,
  { mfld_set_tac },
  { mfld_set_tac },
  { intros b hb, ext L v,
    simp only [continuous_linear_map_coord_change, continuous_linear_equiv.coe_coe,
      continuous_linear_equiv.arrow_congrSL_apply, comp_apply, function.comp, compSL_apply,
      flip_apply, continuous_linear_equiv.symm_symm] },
end

variables (σ e₁ e₁' e₂ e₂')
variables [Π x, has_continuous_add (E₂ x)] [Π x, has_continuous_smul 𝕜₂ (E₂ x)]

/-- Given trivializations `e₁`, `e₂` for vector bundles `E₁`, `E₂` over a base `B`,
`pretrivialization.continuous_linear_map σ e₁ e₂` is the induced pretrivialization for the
continuous `σ`-semilinear maps from `E₁` to `E₂`. That is, the map which will later become a
trivialization, after the bundle of continuous semilinear maps is equipped with the right
smooth vector bundle structure. -/
def continuous_linear_map :
  pretrivialization 𝕜₂ (F₁ →SL[σ] F₂) (bundle.continuous_linear_map σ F₁ E₁ F₂ E₂) :=
{ to_fun := λ p, ⟨p.1, (e₂.continuous_linear_map_at p.1).comp $ p.2.comp $ e₁.symmL p.1⟩,
  inv_fun := λ p, ⟨p.1, (e₂.symmL p.1).comp $ p.2.comp $ e₁.continuous_linear_map_at p.1⟩,
  source := (bundle.total_space.proj) ⁻¹' (e₁.base_set ∩ e₂.base_set),
  target := (e₁.base_set ∩ e₂.base_set) ×ˢ (set.univ : set (F₁ →SL[σ] F₂)),
  map_source' := λ ⟨x, L⟩ h, ⟨h, set.mem_univ _⟩,
  map_target' := λ ⟨x, f⟩ h, h.1,
  left_inv' := λ ⟨x, L⟩ ⟨h₁, h₂⟩,
  begin
    simp_rw [sigma.mk.inj_iff, eq_self_iff_true, heq_iff_eq, true_and],
    ext v,
    simp only [comp_apply, trivialization.symmL_continuous_linear_map_at, h₁, h₂]
  end,
  right_inv' := λ ⟨x, f⟩ ⟨⟨h₁, h₂⟩, _⟩,
  begin
    simp_rw [prod.mk.inj_iff, eq_self_iff_true, true_and],
    ext v,
    simp only [comp_apply, trivialization.continuous_linear_map_at_symmL, h₁, h₂]
  end,
  open_target := (e₁.open_base_set.inter e₂.open_base_set).prod is_open_univ,
  base_set := e₁.base_set ∩ e₂.base_set,
  open_base_set := e₁.open_base_set.inter e₂.open_base_set,
  source_eq := rfl,
  target_eq := rfl,
  proj_to_fun := λ ⟨x, f⟩ h, rfl,
  linear' := λ x h,
  { map_add := λ L L', by simp_rw [add_comp, comp_add],
    map_smul := λ c L, by simp_rw [smul_comp, comp_smulₛₗ, ring_hom.id_apply] } }

lemma continuous_linear_map_apply
  (p : total_space (bundle.continuous_linear_map σ F₁ E₁ F₂ E₂)) :
  (continuous_linear_map σ e₁ e₂) p =
  ⟨p.1, (e₂.continuous_linear_map_at p.1).comp $ p.2.comp $ e₁.symmL p.1⟩ :=
rfl

lemma continuous_linear_map_symm_apply (p : B × (F₁ →SL[σ] F₂)) :
  (continuous_linear_map σ e₁ e₂).to_local_equiv.symm p =
  ⟨p.1, (e₂.symmL p.1).comp $ p.2.comp $ e₁.continuous_linear_map_at p.1⟩ :=
rfl

lemma continuous_linear_map_symm_apply' {b : B} (hb : b ∈ e₁.base_set ∩ e₂.base_set)
  (L : F₁ →SL[σ] F₂) :
  (continuous_linear_map σ e₁ e₂).symm b L =
  (e₂.symmL b).comp (L.comp $ e₁.continuous_linear_map_at b) :=
begin
  rw [symm_apply], refl, exact hb
end

lemma continuous_linear_map_coord_change_apply (b : B)
  (hb : b ∈ (e₁.base_set ∩ e₂.base_set) ∩ (e₁'.base_set ∩ e₂'.base_set)) (L : F₁ →SL[σ] F₂) :
  continuous_linear_map_coord_change σ e₁ e₁' e₂ e₂' b L =
  (continuous_linear_map σ e₁' e₂'
    (total_space_mk b ((continuous_linear_map σ e₁ e₂).symm b L))).2 :=
begin
  ext v,
  simp_rw [continuous_linear_map_coord_change, continuous_linear_equiv.coe_coe,
    continuous_linear_equiv.arrow_congrSL_apply,
    continuous_linear_map_apply, continuous_linear_map_symm_apply' σ e₁ e₂ hb.1,
    comp_apply, continuous_linear_equiv.coe_coe, continuous_linear_equiv.symm_symm,
    trivialization.continuous_linear_map_at_apply, trivialization.symmL_apply],
  dsimp only [total_space_mk],
  rw [e₂.coord_change_apply e₂', e₁'.coord_change_apply e₁, e₁.coe_linear_map_at_of_mem hb.1.1,
    e₂'.coe_linear_map_at_of_mem hb.2.2],
  exacts [⟨hb.2.1, hb.1.1⟩, ⟨hb.1.2, hb.2.2⟩]
end

end pretrivialization

open pretrivialization
variables (F₁ E₁ F₂ E₂)
variables [Π x : B, topological_space (E₁ x)] [smooth_vector_bundle 𝕜₁ F₁ E₁]
variables [Π x : B, topological_space (E₂ x)] [smooth_vector_bundle 𝕜₂ F₂ E₂]
variables [Π x, has_continuous_add (E₂ x)] [Π x, has_continuous_smul 𝕜₂ (E₂ x)]

/-- The continuous `σ`-semilinear maps between two smooth vector bundles form a
`smooth_vector_prebundle` (this is an auxiliary construction for the
`smooth_vector_bundle` instance, in which the pretrivializations are collated but no topology
on the total space is yet provided). -/
def _root_.bundle.continuous_linear_map.smooth_vector_prebundle :
  smooth_vector_prebundle 𝕜₂ (F₁ →SL[σ] F₂)
  (bundle.continuous_linear_map σ F₁ E₁ F₂ E₂) :=
{ pretrivialization_atlas :=
  image2 (λ e₁ e₂, pretrivialization.continuous_linear_map σ e₁ e₂) (trivialization_atlas 𝕜₁ F₁ E₁)
    (trivialization_atlas 𝕜₂ F₂ E₂),
  pretrivialization_at := λ x, pretrivialization.continuous_linear_map σ
    (trivialization_at 𝕜₁ F₁ E₁ x) (trivialization_at 𝕜₂ F₂ E₂ x),
  mem_base_pretrivialization_at := λ x,
    ⟨mem_base_set_trivialization_at 𝕜₁ F₁ E₁ x, mem_base_set_trivialization_at 𝕜₂ F₂ E₂ x⟩,
  pretrivialization_mem_atlas := λ x,
    ⟨_, _, trivialization_mem_atlas 𝕜₁ F₁ E₁ x, trivialization_mem_atlas 𝕜₂ F₂ E₂ x, rfl⟩,
  exists_coord_change := by { rintro _ ⟨e₁, e₂, he₁, he₂, rfl⟩ _ ⟨e₁', e₂', he₁', he₂', rfl⟩,
    exact ⟨continuous_linear_map_coord_change σ e₁ e₁' e₂ e₂',
    continuous_on_continuous_linear_map_coord_change he₁ he₁' he₂ he₂',
    continuous_linear_map_coord_change_apply σ e₁ e₁' e₂ e₂'⟩ } }

/-- Topology on the continuous `σ`-semilinear_maps between the respective fibers at a point of two
"normable" vector bundles over the same base. Here "normable" means that the bundles have fibers
modelled on normed spaces `F₁`, `F₂` respectively.  The topology we put on the continuous
`σ`-semilinear_maps is the topology coming from the operator norm on maps from `F₁` to `F₂`. -/
instance (x : B) : topological_space (bundle.continuous_linear_map σ F₁ E₁ F₂ E₂ x) :=
(bundle.continuous_linear_map.smooth_vector_prebundle σ F₁ E₁ F₂ E₂).fiber_topology x

/-- Topology on the total space of the continuous `σ`-semilinear_maps between two "normable" vector
bundles over the same base. -/
instance : topological_space (total_space (bundle.continuous_linear_map σ F₁ E₁ F₂ E₂)) :=
(bundle.continuous_linear_map.smooth_vector_prebundle
  σ F₁ E₁ F₂ E₂).total_space_topology

/-- The continuous `σ`-semilinear_maps between two vector bundles form a vector bundle. -/
instance _root_.bundle.continuous_linear_map.smooth_vector_bundle :
  smooth_vector_bundle 𝕜₂ (F₁ →SL[σ] F₂) (bundle.continuous_linear_map σ F₁ E₁ F₂ E₂) :=
(bundle.continuous_linear_map.smooth_vector_prebundle
  σ F₁ E₁ F₂ E₂).to_smooth_vector_bundle

variables {F₁ E₁ F₂ E₂}

/-- Given trivializations `e₁`, `e₂` in the atlas for vector bundles `E₁`, `E₂` over a base `B`,
the induced trivialization for the continuous `σ`-semilinear maps from `E₁` to `E₂`,
whose base set is `e₁.base_set ∩ e₂.base_set`. -/
def trivialization.continuous_linear_map
  (he₁ : e₁ ∈ trivialization_atlas 𝕜₁ F₁ E₁) (he₂ : e₂ ∈ trivialization_atlas 𝕜₂ F₂ E₂) :
  trivialization 𝕜₂ (F₁ →SL[σ] F₂) (bundle.continuous_linear_map σ F₁ E₁ F₂ E₂) :=
(bundle.continuous_linear_map.smooth_vector_prebundle σ F₁ E₁ F₂ E₂)
  .trivialization_of_mem_pretrivialization_atlas (mem_image2_of_mem he₁ he₂)

variables {e₁ e₂}

@[simp] lemma trivialization.base_set_continuous_linear_map
  (he₁ : e₁ ∈ trivialization_atlas 𝕜₁ F₁ E₁) (he₂ : e₂ ∈ trivialization_atlas 𝕜₂ F₂ E₂) :
  (e₁.continuous_linear_map σ e₂ he₁ he₂).base_set = e₁.base_set ∩ e₂.base_set :=
rfl

lemma trivialization.continuous_linear_map_apply
  (he₁ : e₁ ∈ trivialization_atlas 𝕜₁ F₁ E₁) (he₂ : e₂ ∈ trivialization_atlas 𝕜₂ F₂ E₂)
  (p : total_space (bundle.continuous_linear_map σ F₁ E₁ F₂ E₂)) :
  e₁.continuous_linear_map σ e₂ he₁ he₂ p =
  ⟨p.1, (e₂.continuous_linear_map_at p.1).comp $ p.2.comp $ e₁.symmL p.1⟩ :=
rfl

end smooth_vector_bundle
