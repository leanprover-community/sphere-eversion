/-
Copyright © 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/

import to_mathlib.geometry.manifold.vector_bundle.basic
import to_mathlib.topology.vector_bundle.hom

/-!
# The smooth vector bundle of continuous (semi)linear maps

We define the smooth vector bundle of continuous (semi)linear maps between two
vector bundles over the same base.
-/

noncomputable theory

open bundle set continuous_linear_map
open_locale classical manifold

variables {𝕜 B VB VE₁ VE₂ HB HE₁ HE₂ : Type*}
variables [nondiscrete_normed_field 𝕜] [nondiscrete_normed_field 𝕜] [nondiscrete_normed_field 𝕜]
variables [normed_group VB] [normed_space 𝕜 VB]
variables [normed_group VE₁] [normed_space 𝕜 VE₁] [normed_group VE₂] [normed_space 𝕜 VE₂]
variables [topological_space HB] [topological_space HE₁] [topological_space HE₂]
variables (IB : model_with_corners 𝕜 VB HB)
variables (IE₁ : model_with_corners 𝕜 VE₁ HE₁) (IE₂ : model_with_corners 𝕜 VE₂ HE₂)
variables (F₁ F₂ : Type*) (E₁ E₂ : B → Type*)
variables [∀ x, normed_group (E₁ x)] [∀ x, normed_space 𝕜 (E₁ x)]
variables [∀ x, normed_group (E₂ x)] [∀ x, normed_space 𝕜 (E₂ x)]
variables [normed_group F₁] [normed_space 𝕜 F₁] [normed_group F₂] [normed_space 𝕜 F₂]
variables [topological_space B] [charted_space HB B]
variables [topological_space (total_space E₁)] [charted_space HE₁ (total_space E₁)]
variables [topological_space (total_space E₂)] [charted_space HE₂ (total_space E₂)]
variables (σ : 𝕜 →+* 𝕜) /- the domain and codomain are the same, because vector bundles (currently?)
are only defined when they are Banach spaces over the same field. -/

namespace smooth_vector_bundle

variables {F₁ E₁ F₂ E₂} (e₁ e₁' : trivialization IB IE₁ F₁ E₁)
  (e₂ e₂' : trivialization IB IE₂ F₂ E₂)
variables [ring_hom_isometric σ]

/- todo: do we want to modify this instance so that the topology is definitionally the
topology given by the topological space instance in `topology/vector_bundle/hom`?
Probably not, because I think that will mess with lemmas involving the topology on continuous linear
maps.
-/
instance (b : B) : normed_group (bundle.continuous_linear_map σ F₁ E₁ F₂ E₂ b) :=
by delta_instance bundle.continuous_linear_map

instance (b : B) : normed_space 𝕜 (bundle.continuous_linear_map σ F₁ E₁ F₂ E₂ b) :=
by delta_instance bundle.continuous_linear_map

variables [smooth_vector_bundle IB IE₁ F₁ E₁] [smooth_vector_bundle IB IE₂ F₂ E₂]
-- variables [∀ x, has_continuous_add (E₂ x)] [∀ x, has_continuous_smul 𝕜₂ (E₂ x)]

include IB IE₁ IE₂

instance charted_space_total_space_clm : charted_space (model_prod HB (F₁ →SL[σ] F₂))
  (total_space (bundle.continuous_linear_map σ F₁ E₁ F₂ E₂)) :=
topological_vector_bundle.total_space.to_charted_space 𝕜 _ _

variables {IB IE₁ IE₂ F₁ F₂ E₁ E₂}
/-- Local trivialization for the clm bundle. -/
-- maybe we should define "smooth_vector_prebundle", so that we don't have to prove the following
-- sorry's
def trivialization.continuous_linear_map (he₁ : e₁ ∈ trivialization_atlas IB IE₁ F₁ E₁)
  (he₂ : e₂ ∈ trivialization_atlas IB IE₂ F₂ E₂) :
  trivialization IB (IB.prod 𝓘(𝕜, F₁ →SL[σ] F₂)) (F₁ →SL[σ] F₂)
  (bundle.continuous_linear_map σ F₁ E₁ F₂ E₂) :=
{ smooth_on_to_fun := sorry,
  smooth_on_inv_fun := sorry,
  .. e₁.to_topological.continuous_linear_map σ e₂.to_topological
    (to_topological_mem_trivialization_atlas.mpr he₁)
    (to_topological_mem_trivialization_atlas.mpr he₂) }

lemma trivialization.continuous_linear_map.coord_change
  (he₁ : e₁ ∈ trivialization_atlas IB IE₁ F₁ E₁) (he₁' : e₁' ∈ trivialization_atlas IB IE₁ F₁ E₁)
  (he₂ : e₂ ∈ trivialization_atlas IB IE₂ F₂ E₂) (he₂' : e₂' ∈ trivialization_atlas IB IE₂ F₂ E₂)
  (b : B) (L : F₁ →SL[σ] F₂) : (e₁.continuous_linear_map σ e₂ he₁ he₂).coord_change
    (e₁'.continuous_linear_map σ e₂' he₁' he₂') b L =
  topological_vector_bundle.pretrivialization.continuous_linear_map_coord_change
   σ e₁.to_topological e₁'.to_topological e₂.to_topological e₂'.to_topological b L :=
begin
  rw [trivialization.coord_change], sorry
end

variables (IB IE₁ IE₂ F₁ F₂ E₁ E₂)
instance continuous_linear_map.smooth_vector_bundle :
  smooth_vector_bundle IB (IB.prod 𝓘(𝕜, F₁ →SL[σ] F₂)) (F₁ →SL[σ] F₂)
  (bundle.continuous_linear_map σ F₁ E₁ F₂ E₂) :=
  -- topological_vector_bundle.total_space_mk_inducing won't apply here
{ total_space_mk_inducing := by { sorry },
  trivialization_atlas := ⋃ (e₁ : trivialization IB IE₁ F₁ E₁)
    (e₂ : trivialization IB IE₂ F₂ E₂) (he₁ : e₁ ∈ trivialization_atlas IB IE₁ F₁ E₁)
    (he₂ : e₂ ∈ trivialization_atlas IB IE₂ F₂ E₂),
    {trivialization.continuous_linear_map σ e₁ e₂ he₁ he₂},
  trivialization_at := λ b, trivialization.continuous_linear_map σ _ _
    (trivialization_mem_atlas IB IE₁ F₁ E₁ b) (trivialization_mem_atlas IB IE₂ F₂ E₂ b),
  trivialization_mem_atlas := λ b, by { simp_rw [mem_Union, mem_singleton_iff], exact
    ⟨_, _, trivialization_mem_atlas IB IE₁ F₁ E₁ b, trivialization_mem_atlas IB IE₂ F₂ E₂ b, rfl⟩ },
  mem_base_set_trivialization_at := λ b,
    ⟨mem_base_set_trivialization_at IB IE₁ F₁ E₁ b, mem_base_set_trivialization_at IB IE₂ F₂ E₂ b⟩,
  smooth_on_coord_change := begin
    simp_rw [mem_Union, mem_singleton_iff],
    rintro _ ⟨e₁, e₂, he₁, he₂, rfl⟩ _ ⟨e₁', e₂', he₁', he₂', rfl⟩,
    sorry
  end }

end smooth_vector_bundle
