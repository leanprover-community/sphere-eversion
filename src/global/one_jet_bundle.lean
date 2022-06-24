/-
Copyright (c) 2022 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import to_mathlib.geometry.manifold.vector_bundle.hom
import to_mathlib.geometry.manifold.vector_bundle.pullback

noncomputable theory

open set equiv bundle
open_locale manifold

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {E : Type*} [normed_group E] [normed_space 𝕜 E]
  {H : Type*} [topological_space H]
  (I : model_with_corners 𝕜 E H)
  (M : Type*) [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
  {E' : Type*} [normed_group E'] [normed_space 𝕜 E']
  {H' : Type*} [topological_space H']
  (I' : model_with_corners 𝕜 E' H')
  (M' : Type*) [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M']

include I I'
variables {M M'}

/-- The fibers of the 1-jet space of `M` and `N`. -/
@[nolint unused_arguments, derive [normed_group, normed_space 𝕜, inhabited]]
def one_jet_space : M × M' → Type* :=
bundle.continuous_linear_map (ring_hom.id 𝕜) E (cont_mdiff_map.fst I M I' M' *ᵖ tangent_space I)
  E' (cont_mdiff_map.snd I M I' M' *ᵖ tangent_space I')

variables (M M')

/-- The space of one jets of maps between two smooth manifolds, as a Sigma type.
Defined in terms of `bundle.total_space` to be able to put a suitable topology on it. -/
@[nolint has_inhabited_instance, reducible] -- is empty if the base manifold is empty
def one_jet_bundle := total_space (one_jet_space I I' : M × M' → Type*)

local notation `J¹MM'` := one_jet_bundle I M I' M'

/-- The projection from the one jet bundle of smooth manifolds to the product manifold. As the
one_jet bundle is represented internally as a sigma type, the notation `p.1` also works for the
projection of the point `p`. -/
def one_jet_bundle.proj : J¹MM' → M × M' :=
λ p, p.1

instance (p : M × M') : has_coe_to_fun (one_jet_space I I' p)
  (λ σ, tangent_space I p.1 → tangent_space I' p.2) := ⟨λ φ, φ.to_fun⟩

instance topological_space_total_space_one_jet_space : topological_space J¹MM' :=
by delta_instance one_jet_bundle one_jet_space

instance charted_space_total_space_one_jet_space :
  charted_space (model_prod (model_prod H H') (E →L[𝕜] E')) J¹MM' :=
by delta_instance one_jet_bundle one_jet_space

omit I I'

instance :
  smooth_vector_bundle (I.prod I') ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) (E →L[𝕜] E')
  (one_jet_space I I' : M × M' → Type*) :=
by delta_instance one_jet_space

instance : smooth_manifold_with_corners ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) J¹MM' :=
sorry

/-
TODO: Also define the projection to source?
-/

@[simp, mfld_simps] lemma one_jet_bundle.proj_apply (p : M × M') (σ : one_jet_space I I' p) :
  one_jet_bundle.proj I M I' M' ⟨p, σ⟩ = p :=
rfl


section one_jet_bundle_instances

variable (M)

instance : topological_vector_bundle 𝕜 (E →L[𝕜] E') (one_jet_space I I' : M × M' → Type*) :=
topological_vector_bundle_core.fiber.topological_vector_bundle
  (one_jet_bundle_core I M I' M').to_topological_vector_bundle_core

end one_jet_bundle_instances

variable (M)

/-- The tangent bundle projection on the basis is a continuous map. -/
lemma one_jet_bundle_proj_continuous : continuous (one_jet_bundle.proj I M I' M') :=
((one_jet_bundle_core I M I' M').to_topological_vector_bundle_core).continuous_proj

/-- The one_jet bundle projection on the basis is an open map. -/
lemma one_jet_bundle_proj_open : is_open_map (one_jet_bundle.proj I M I' M') :=
((one_jet_bundle_core I M I' M').to_topological_vector_bundle_core).is_open_map_proj

local notation `𝓜` := model_prod (model_prod H H') (E →L[𝕜] E')

/-- In the one_jet bundle to the model space, the charts are just the canonical identification
between a product type and a sigma type, a.k.a. `sigma_equiv_prod`. -/
@[simp, mfld_simps] lemma one_jet_bundle_model_space_chart_at (p : one_jet_bundle I H I' H') :
  (chart_at 𝓜 p).to_local_equiv = (sigma_equiv_prod (H × H') (E →L[𝕜] E')).to_local_equiv :=
sorry

@[simp, mfld_simps] lemma one_jet_bundle_model_space_coe_chart_at (p : one_jet_bundle I H I' H') :
  ⇑(chart_at 𝓜 p) = sigma_equiv_prod (H × H') (E →L[𝕜] E') :=
by { unfold_coes, simp only with mfld_simps }

@[simp, mfld_simps] lemma one_jet_bundle_model_space_coe_chart_at_symm
  (p : one_jet_bundle I H I' H') :
  ((chart_at 𝓜 p).symm : 𝓜 → one_jet_bundle I H I' H') =
  (sigma_equiv_prod (H × H') (E →L[𝕜] E')).symm :=
by { unfold_coes, simp only with mfld_simps }

variables (H H')

/-- The canonical identification between the one_jet bundle to the model space and the product,
as a homeomorphism -/
def one_jet_bundle_model_space_homeomorph : one_jet_bundle I H I' H' ≃ₜ 𝓜 :=
{ continuous_to_fun := sorry,
  continuous_inv_fun := sorry,
  .. sigma_equiv_prod (H × H') (E →L[𝕜] E') }

@[simp, mfld_simps] lemma one_jet_bundle_model_space_homeomorph_coe :
  (one_jet_bundle_model_space_homeomorph H I H' I' : one_jet_bundle I H I' H' → 𝓜) =
  sigma_equiv_prod (H × H') (E →L[𝕜] E') :=
rfl

@[simp, mfld_simps] lemma one_jet_bundle_model_space_homeomorph_coe_symm :
  ((one_jet_bundle_model_space_homeomorph H I H' I').symm : 𝓜 → one_jet_bundle I H I' H') =
  (sigma_equiv_prod (H × H') (E →L[𝕜] E')).symm :=
rfl
