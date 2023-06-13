/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/

import geometry.manifold.vector_bundle.pullback
import topology.vector_bundle.hom
import to_mathlib.geometry.manifold.misc_manifold

/-!
# Various operations on and properties of smooth vector bundles
-/

noncomputable theory

open bundle set topological_space local_homeomorph
open_locale classical manifold bundle

namespace fiber_bundle

variables {𝕜 B B' F M : Type*} {E : B → Type*}
variables [topological_space F] [topological_space (total_space E)] [∀ x, topological_space (E x)]
  {HB : Type*} [topological_space HB]
  [topological_space B] [charted_space HB B] [fiber_bundle F E]

lemma charted_space_chart_at_fst' (x y : total_space E) :
  (chart_at (model_prod HB F) x y).1 =
  chart_at HB x.proj (trivialization_at F E x.proj y).1 :=
by { rw [charted_space_chart_at], refl }

lemma charted_space_chart_at_fst {x y : total_space E}
  (hy : y.proj ∈ (trivialization_at F E x.proj).base_set) :
  (chart_at (model_prod HB F) x y).1 = chart_at HB x.proj y.proj :=
by rw [charted_space_chart_at_fst', (trivialization_at F E x.proj).coe_fst' hy]

lemma charted_space_chart_at_snd (x y : total_space E) :
  (chart_at (model_prod HB F) x y).2 = (trivialization_at F E x.proj y).2 :=
by { rw [charted_space_chart_at], refl }

end fiber_bundle

section vector_bundle

variables {𝕜 B F F₁ F₂ : Type*}
  {E : B → Type*} {E₁ : B → Type*} {E₂ : B → Type*}
  [nontrivially_normed_field 𝕜]
  [∀ x, add_comm_monoid (E x)] [∀ x, module 𝕜 (E x)]
  [normed_add_comm_group F] [normed_space 𝕜 F]
  [topological_space (total_space E)] [∀ x, topological_space (E x)]
  [∀ x, add_comm_monoid (E₁ x)] [∀ x, module 𝕜 (E₁ x)]
  [normed_add_comm_group F₁] [normed_space 𝕜 F₁]
  [topological_space (total_space E₁)] [∀ x, topological_space (E₁ x)]
  [∀ x, add_comm_monoid (E₂ x)] [∀ x, module 𝕜 (E₂ x)]
  [normed_add_comm_group F₂] [normed_space 𝕜 F₂]
  [topological_space (total_space E₂)] [∀ x, topological_space (E₂ x)]
  [topological_space B]
  {n : ℕ∞}
  [fiber_bundle F₁ E₁] [vector_bundle 𝕜 F₁ E₁]
  [fiber_bundle F₂ E₂] [vector_bundle 𝕜 F₂ E₂]
  {e₁ e₁' : trivialization F₁ (π E₁)} {e₂ e₂' : trivialization F₂ (π E₂)}




end vector_bundle


namespace vector_bundle_core

variables {R 𝕜 B F ι : Type*}
  [nontrivially_normed_field R]
  [normed_add_comm_group F] [normed_space R F] [topological_space B]
  (Z : vector_bundle_core R B F ι)

/-- `Z.coord_change j i` is a partial inverse of `Z.coord_change i j`. -/
lemma coord_change_comp_eq_self {i j : ι} {x : B} (hx : x ∈ Z.base_set i ∩ Z.base_set j) (v : F) :
  Z.coord_change j i x (Z.coord_change i j x v) = v :=
by rw [Z.coord_change_comp i j i x ⟨hx, hx.1⟩, Z.coord_change_self i x hx.1]

end vector_bundle_core

namespace bundle.trivial
open _root_.trivialization

variables {𝕜 B F : Type*}
variables [nontrivially_normed_field 𝕜] [normed_add_comm_group F] [normed_space 𝕜 F]
  [topological_space B]

@[simp, mfld_simps]
protected lemma trivialization_at (x : B) :
  trivialization_at F (trivial B F) x = trivial.trivialization B F :=
rfl

@[simp, mfld_simps]
lemma trivialization_continuous_linear_map_at (x : B) :
  (trivial.trivialization B F).continuous_linear_map_at 𝕜 x = continuous_linear_map.id 𝕜 F :=
begin
  ext v,
  simp_rw [continuous_linear_map_at_apply, coe_linear_map_at],
  rw [if_pos],
  exacts [rfl, mem_univ _]
end

end bundle.trivial

section hom
variables {𝕜₁ : Type*} [nontrivially_normed_field 𝕜₁] {𝕜₂ : Type*} [nontrivially_normed_field 𝕜₂]
  (σ : 𝕜₁ →+* 𝕜₂) [iσ : ring_hom_isometric σ]

variables {B : Type*} [topological_space B]

variables (F₁ : Type*) [normed_add_comm_group F₁] [normed_space 𝕜₁ F₁]
  (E₁ : B → Type*) [Π x, add_comm_group (E₁ x)] [Π x, module 𝕜₁ (E₁ x)]
  [topological_space (total_space E₁)]
variables (F₂ : Type*) [normed_add_comm_group F₂][normed_space 𝕜₂ F₂]
  (E₂ : B → Type*) [Π x, add_comm_group (E₂ x)] [Π x, module 𝕜₂ (E₂ x)]
  [topological_space (total_space E₂)]
variables (F₁ E₁ F₂ E₂) [ring_hom_isometric σ]
variables [Π x : B, topological_space (E₁ x)] [fiber_bundle F₁ E₁] [vector_bundle 𝕜₁ F₁ E₁]
variables [Π x : B, topological_space (E₂ x)] [fiber_bundle F₂ E₂] [vector_bundle 𝕜₂ F₂ E₂]
variables [Π x, topological_add_group (E₂ x)] [Π x, has_continuous_smul 𝕜₂ (E₂ x)]

@[simp, mfld_simps]
lemma continuous_linear_map_trivialization_at (x : B) :
  trivialization_at (F₁ →SL[σ] F₂) (bundle.continuous_linear_map σ F₁ E₁ F₂ E₂) x =
  (trivialization_at F₁ E₁ x).continuous_linear_map σ (trivialization_at F₂ E₂ x) :=
rfl

end hom

section pullback

/-- We need some instances like this to work with negation on pullbacks -/
instance {B B'} {E : B → Type*} {f : B' → B} {x : B'} [∀ x', add_comm_group (E x')] :
  add_comm_group ((f *ᵖ E) x) :=
by delta_instance bundle.pullback

instance {B B'} {E : B → Type*} {f : B' → B} {x : B'} [∀ x', has_zero (E x')] :
  has_zero ((f *ᵖ E) x) :=
by delta_instance bundle.pullback

variables {B F B' K : Type*} {E : B → Type*} {f : K}
  [topological_space B'] [topological_space (total_space E)]
  [topological_space F] [topological_space B]
  [∀ b, has_zero (E b)] [continuous_map_class K B' B]

namespace trivialization

-- attribute [simps base_set] trivialization.pullback

lemma pullback_symm (e : trivialization F (π E)) (x : B') : (e.pullback f).symm x = e.symm (f x) :=
begin
  ext y,
  simp_rw [trivialization.symm, pretrivialization.symm],
  congr', ext (hx : f x ∈ e.to_pretrivialization.base_set),
  change cast _ (e.symm (f x) y) = cast _ ((e.to_local_homeomorph.symm (f x, y)).2),
  simp_rw [trivialization.symm, pretrivialization.symm, dif_pos hx, cast_cast],
  refl,
end

end trivialization


variables [∀ x, topological_space (E x)] [fiber_bundle F E]

lemma pullback_trivialization_at {x : B'} : trivialization_at F (f *ᵖ E) x =
  (trivialization_at F E (f x)).pullback f :=
rfl




end pullback

section pullback_vb

variables {R 𝕜 B F B' : Type*} {E : B → Type*}


variables [topological_space B'] [topological_space (total_space E)]
  [nontrivially_normed_field 𝕜] [normed_add_comm_group F] [normed_space 𝕜 F] [topological_space B]
  [∀ x, add_comm_monoid (E x)] [∀ x, module 𝕜 (E x)] [∀ x, topological_space (E x)]
  [fiber_bundle F E]
  {K : Type*} [continuous_map_class K B' B] (f : K)

namespace trivialization
lemma pullback_symmL (e : trivialization F (π E)) [e.is_linear 𝕜] (x : B') :
  (e.pullback f).symmL 𝕜 x = e.symmL 𝕜 (f x) :=
by { ext y, simp_rw [symmL_apply, pullback_symm] }

end trivialization

end pullback_vb

namespace vector_prebundle

-- attribute [reducible] vector_prebundle.to_fiber_bundle

/-!
### `vector_prebundle.is_smooth`

Todo: maybe redefine `vector_prebundle` as a mixin `fiber_prebundle.is_vector_prebundle`.
The reason is that if you define a `fiber_prebundle` operation, and then
(under certain circumstances)
upgrade it to a `vector_prebundle`, this will result in `fiber_bundle` instances that are probably
not easily seen as definitionally equal by type-class inference.
-/


variables {𝕜 B F F₁ F₂ M M₁ M₂ : Type*}
  {E : B → Type*} {E₁ : B → Type*} {E₂ : B → Type*}
  [nontrivially_normed_field 𝕜]
  [∀ x, add_comm_monoid (E x)] [∀ x, module 𝕜 (E x)] [∀ x, topological_space (E x)]
  [normed_add_comm_group F] [normed_space 𝕜 F]
  [∀ x, add_comm_monoid (E₁ x)] [∀ x, module 𝕜 (E₁ x)]
  [normed_add_comm_group F₁] [normed_space 𝕜 F₁]
  [∀ x, add_comm_monoid (E₂ x)] [∀ x, module 𝕜 (E₂ x)]
  [normed_add_comm_group F₂] [normed_space 𝕜 F₂]
  {EB : Type*} [normed_add_comm_group EB] [normed_space 𝕜 EB]
  {HB : Type*} [topological_space HB] (IB : model_with_corners 𝕜 EB HB)
  [topological_space B] [charted_space HB B] [smooth_manifold_with_corners IB B]
  {EM : Type*} [normed_add_comm_group EM] [normed_space 𝕜 EM]
  {HM : Type*} [topological_space HM] {IM : model_with_corners 𝕜 EM HM}
  [topological_space M] [charted_space HM M]
  {n : ℕ∞}

variables (a : vector_prebundle 𝕜 F E) [ha : a.is_smooth IB] {e e' : pretrivialization F (π E)}
include ha

/-- Make a `smooth_vector_bundle` from a `smooth_vector_prebundle`.  -/
lemma to_smooth_vector_bundle :
  @_root_.smooth_vector_bundle  _ _ F E _ _ _ _ _ _ IB _ _ _ _ _ _ _ a.total_space_topology _
  a.to_fiber_bundle a.to_vector_bundle :=
{ smooth_on_coord_change := begin
    rintros _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩,
    refine (a.smooth_on_smooth_coord_change he he').congr _,
    intros b hb,
    ext v,
    rw [a.smooth_coord_change_apply he he' hb v, continuous_linear_equiv.coe_coe,
      trivialization.coord_changeL_apply],
    exacts [rfl, hb]
  end }

end vector_prebundle

variables {𝕜 B F F₁ F₂ M M₁ M₂ : Type*}
  {E : B → Type*} {E₁ : B → Type*} {E₂ : B → Type*}
  [nontrivially_normed_field 𝕜]
  [∀ x, add_comm_group (E x)] [∀ x, module 𝕜 (E x)]
  [normed_add_comm_group F] [normed_space 𝕜 F]
  [topological_space (total_space E)] [∀ x, topological_space (E x)]
  [∀ x, add_comm_group (E₁ x)] [∀ x, module 𝕜 (E₁ x)]
  [normed_add_comm_group F₁] [normed_space 𝕜 F₁]
  [topological_space (total_space E₁)] [∀ x, topological_space (E₁ x)]
  [∀ x, add_comm_group (E₂ x)] [∀ x, module 𝕜 (E₂ x)]
  [normed_add_comm_group F₂] [normed_space 𝕜 F₂]
  [topological_space (total_space E₂)] [∀ x, topological_space (E₂ x)]

  {EB : Type*} [normed_add_comm_group EB] [normed_space 𝕜 EB]
  {HB : Type*} [topological_space HB] (IB : model_with_corners 𝕜 EB HB)
  [topological_space B] [charted_space HB B]
  {EM : Type*} [normed_add_comm_group EM] [normed_space 𝕜 EM]
  {HM : Type*} [topological_space HM] {IM : model_with_corners 𝕜 EM HM}
  [topological_space M] [charted_space HM M] [Is : smooth_manifold_with_corners IM M]
  {n : ℕ∞}
  [fiber_bundle F₁ E₁] [vector_bundle 𝕜 F₁ E₁]
  [fiber_bundle F₂ E₂] [vector_bundle 𝕜 F₂ E₂]
  {e₁ e₁' : trivialization F₁ (π E₁)} {e₂ e₂' : trivialization F₂ (π E₂)}


/-!
### Homs of smooth vector bundles over the same base space
-/

section hom
open continuous_linear_map pretrivialization

local notation `σ` := ring_hom.id 𝕜

section general
-- what is better notation for this?
local notation `LE₁E₂` := total_space (bundle.continuous_linear_map σ F₁ E₁ F₂ E₂)
local notation `PLE₁E₂` := bundle.continuous_linear_map.vector_prebundle σ F₁ E₁ F₂ E₂


/- This proof is slow, especially the `simp only` and the elaboration of `h₂`.
  It needs a timeout >100k to compile -/
lemma smooth_on_continuous_linear_map_coord_change
  [smooth_manifold_with_corners IB B]
  [smooth_vector_bundle F₁ E₁ IB] [smooth_vector_bundle F₂ E₂ IB]
  [mem_trivialization_atlas e₁] [mem_trivialization_atlas e₁']
  [mem_trivialization_atlas e₂] [mem_trivialization_atlas e₂'] :
  smooth_on IB 𝓘(𝕜, ((F₁ →L[𝕜] F₂) →L[𝕜] (F₁ →L[𝕜] F₂)))
    (continuous_linear_map_coord_change σ e₁ e₁' e₂ e₂')
    ((e₁.base_set ∩ e₂.base_set) ∩ (e₁'.base_set ∩ e₂'.base_set)) :=
begin
  let L₁ := compSL F₁ F₂ F₂ σ σ,
  have h₁ : smooth _ _ _ := L₁.cont_mdiff,
  have h₂ : smooth _ _ _ := (continuous_linear_map.flip (compSL F₁ F₁ F₂ σ σ)).cont_mdiff,
  have h₃ : smooth_on IB _ _ _ := smooth_on_coord_change e₁' e₁,
  have h₄ : smooth_on IB _ _ _ := smooth_on_coord_change e₂ e₂',
  refine ((h₁.comp_smooth_on (h₄.mono _)).clm_comp (h₂.comp_smooth_on (h₃.mono _))).congr _,
  { mfld_set_tac },
  { mfld_set_tac },
  { intros b hb, ext L v,
    simp only [continuous_linear_map_coord_change, continuous_linear_equiv.coe_coe,
      continuous_linear_equiv.arrow_congrSL_apply, comp_apply, function.comp, compSL_apply,
      flip_apply, continuous_linear_equiv.symm_symm] },
end

variables [∀ x, topological_add_group (E₂ x)] [∀ x, has_continuous_smul 𝕜 (E₂ x)]

@[reducible]
def topological_space.continuous_linear_map' (x) : topological_space (bundle.continuous_linear_map σ F₁ E₁ F₂ E₂ x) :=
by apply_instance
local attribute [instance, priority 1] topological_space.continuous_linear_map'
-- ^ probably needed because of the type-class pi bug
-- https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/vector.20bundles.20--.20typeclass.20inference.20issue

lemma hom_chart (x₀ x : LE₁E₂) :
  chart_at (model_prod HB (F₁ →L[𝕜] F₂)) x₀ x =
  (chart_at HB x₀.1 x.1, in_coordinates F₁ E₁ F₂ E₂ x₀.1 x.1 x₀.1 x.1 x.2) :=
by simp_rw [fiber_bundle.charted_space_chart_at, trans_apply, local_homeomorph.prod_apply,
  trivialization.coe_coe, local_homeomorph.refl_apply, function.id_def, hom_trivialization_at_apply]

lemma smooth_at_hom_bundle {f : M → LE₁E₂} {x₀ : M} :
  smooth_at IM (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) f x₀ ↔
  smooth_at IM IB (λ x, (f x).1) x₀ ∧
  smooth_at IM 𝓘(𝕜, F₁ →L[𝕜] F₂)
  (λ x, in_coordinates F₁ E₁ F₂ E₂ (f x₀).1 (f x).1 (f x₀).1 (f x).1 (f x).2) x₀ :=
by { simp_rw [smooth_at, cont_mdiff_at_total_space], refl }

variables [smooth_manifold_with_corners IB B]
  [smooth_vector_bundle F₁ E₁ IB] [smooth_vector_bundle F₂ E₂ IB]

variables [∀ x, has_continuous_add (E₂ x)] [∀ x, has_continuous_smul 𝕜 (E₂ x)]

instance bundle.continuous_linear_map.vector_prebundle.is_smooth :
  (bundle.continuous_linear_map.vector_prebundle σ F₁ E₁ F₂ E₂).is_smooth IB :=
{ exists_smooth_coord_change := by {
    rintro _ ⟨e₁, e₂, he₁, he₂, rfl⟩ _ ⟨e₁', e₂', he₁', he₂', rfl⟩,
    resetI,
    refine ⟨continuous_linear_map_coord_change σ e₁ e₁' e₂ e₂',
    smooth_on_continuous_linear_map_coord_change IB,
    continuous_linear_map_coord_change_apply σ e₁ e₁' e₂ e₂'⟩ } }

instance smooth_vector_bundle.continuous_linear_map :
  smooth_vector_bundle (F₁ →L[𝕜] F₂) (bundle.continuous_linear_map σ F₁ E₁ F₂ E₂) IB :=
PLE₁E₂ .to_smooth_vector_bundle IB

end general

end hom
