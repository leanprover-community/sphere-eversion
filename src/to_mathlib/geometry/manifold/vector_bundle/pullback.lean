/-
Copyright © 2022 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/

import to_mathlib.geometry.manifold.vector_bundle.basic
import topology.vector_bundle.pullback
import geometry.manifold.cont_mdiff_map

/-!
# Pullbacks of smooth vector bundles
-/

noncomputable theory

open bundle set topological_space topological_vector_bundle
open_locale classical manifold

variables {𝕜 B B' VB VB' VE HB HB' HE : Type*}
variables [nondiscrete_normed_field 𝕜]
variables [normed_group VB] [normed_space 𝕜 VB] [normed_group VB'] [normed_space 𝕜 VB']
variables [normed_group VE] [normed_space 𝕜 VE]
variables [topological_space HB] [topological_space HB'] [topological_space HE]
variables (IB : model_with_corners 𝕜 VB HB) (IB' : model_with_corners 𝕜 VB' HB')
variables (IE : model_with_corners 𝕜 VE HE)
variables (F : Type*) (E : B → Type*)
variables [∀ x, normed_group (E x)]
variables [normed_group F] [normed_space 𝕜 F]
variables [topological_space B] [charted_space HB B]
variables [topological_space B'] [charted_space HB' B']
variables (f : C^∞⟮IB', B'; IB, B⟯) -- todo: define cont_mdiff_map_class
-- variables [smooth_manifold_with_corners I' (total_space E)]

namespace smooth_vector_bundle

instance (b : B') : normed_group ((f *ᵖ E) b) :=
by delta_instance bundle.pullback

variables [∀ x, normed_space 𝕜 (E x)]

instance (b : B') : normed_space 𝕜 ((f *ᵖ E) b) :=
by delta_instance bundle.pullback

variables [topological_space (total_space E)] [charted_space HE (total_space E)]
variables [smooth_vector_bundle IB IE F E]
variables (e e' : trivialization IB IE F E)

include IB IE

@[nolint dangerous_instance] -- is this fine?
instance charted_space_total_space_pullback : charted_space (model_prod HB' F)
  (total_space (f *ᵖ E)) :=
topological_vector_bundle.total_space.to_charted_space 𝕜 _ _

variables {IB IB' IE F E}
/-- Local trivialization for the clm bundle. -/
-- maybe we should define "smooth_vector_prebundle", so that we don't have to prove the following
-- sorry's
def trivialization.pullback : --(he : e ∈ trivialization_atlas IB IE F E)
  trivialization IB' (IB'.prod 𝓘(𝕜, F)) F (f *ᵖ E) :=
{ smooth_on_to_fun := sorry,
  smooth_on_inv_fun := sorry,
  ..e.to_topological.pullback f }

-- lemma trivialization.pullback.coord_change
--   (he : e ∈ trivialization_atlas IB IE F E) (he' : e' ∈ trivialization_atlas IB IE F E)
--   (b : B') : (e.pullback f).coord_change (e'.pullback f) b = sorry :=
-- begin
--   rw [trivialization.coord_change], sorry
-- end

example : topological_vector_bundle 𝕜 F (f *ᵖ E) := by apply_instance

variables (IB IB' IE F E)
instance pullback.smooth_vector_bundle : smooth_vector_bundle IB' (IB'.prod 𝓘(𝕜, F)) F (f *ᵖ E) :=
{
  total_space_mk_inducing :=
    (topological_vector_bundle.total_space_mk_inducing 𝕜 F (f *ᵖ E) : _),
  trivialization_atlas := (λ e : trivialization IB IE F E, e.pullback f) '' trivialization_atlas IB IE F E,
  trivialization_at := λ x, (trivialization_at IB IE F E (f x)).pullback f,
  mem_base_set_trivialization_at := λ x, mem_base_set_trivialization_at IB IE F E (f x),
  trivialization_mem_atlas := λ x, mem_image_of_mem _ (trivialization_mem_atlas IB IE F E (f x)),
  smooth_on_coord_change := begin
    rintro _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩,
    sorry
    -- refine ((continuous_on_coord_change e he e' he').comp (map_continuous f).continuous_on
    --   (λ b hb, hb)).congr _,
    -- rintro b (hb : f b ∈ e.base_set ∩ e'.base_set), ext v,
    -- show ((e.pullback f).coord_change (e'.pullback f) b) v = (e.coord_change e' (f b)) v,
    -- rw [e.coord_change_apply e' hb, (e.pullback f).coord_change_apply' _],
    -- exacts [rfl, hb]
  end
   }

end smooth_vector_bundle
