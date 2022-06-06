/-
Copyright (c) 2022 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import geometry.manifold.tangent_bundle

noncomputable theory

open set equiv
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

/-
The definition below is an unreadable term but we keep the tactic version commented out
for people who want to understand.

A element `i : ↥(atlas (model_prod H H') (M × M'))` is secretely a pair consisting of
an element `atlas H M` and an element of `atlas H' M'`. They are accessed as
`i.2.some` and `i.2.some_spec.some` because `prod_charted_space` is defined using `image2`.
-/

def one_jet_bundle_core : basic_smooth_vector_bundle_core (I.prod I') (M × M') (E →L[𝕜] E') :=
{ coord_change := λ i j x, (continuous_linear_map.compL 𝕜 E E' E' (fderiv_within 𝕜 (I' ∘ (j.2.some_spec.some) ∘ (i.2.some_spec.some).symm ∘ I'.symm) (range I') (I' x.2))) ∘L (continuous_linear_map.compL 𝕜 E E E').flip (fderiv_within 𝕜 (I ∘ (j.2.some) ∘ (i.2.some).symm ∘ I.symm) (range I) (I x.1)),
/- begin
  cases i with ii hi,
  choose i i' hi hi' H using hi,
  --subst H,
  cases j with jj hj,
  choose j j' hj hj' H' using hj,
  --subst H',
  exact (continuous_linear_map.compL 𝕜 E E' E' (fderiv_within 𝕜 (I' ∘ j' ∘ i'.symm ∘ I'.symm) (range I') (I' x.2))) ∘L (continuous_linear_map.compL 𝕜 E E E').flip (fderiv_within 𝕜 (I ∘ j ∘ i.symm ∘ I.symm) (range I) (I x.1)),
end, -/
  coord_change_self := sorry,
  coord_change_comp := sorry,
  coord_change_smooth_clm := sorry }

include I I'
variables {M M'}

@[nolint unused_arguments]
def one_jet_space (p : M × M') : Type* := E →L[𝕜] E'

omit I I'

variables (M M')

/-- The space of one jets of maps between two smooth manifolds, as a Sigma type.
Defined in terms of `bundle.total_space` to be able to put a suitable topology on it. -/
@[nolint has_inhabited_instance, reducible] -- is empty if the base manifold is empty
def one_jet_bundle := bundle.total_space (one_jet_space I I' : M × M' → Type*)

local notation `J¹MM'` := one_jet_bundle I M I' M'

/-- The projection from the one jet bundle of smooth manifolds to the product manifold. As the
one_jet bundle is represented internally as a sigma type, the notation `p.1` also works for the
projection of the point `p`. -/
def one_jet_bundle.proj : J¹MM' → M × M' :=
λ p, p.1

/-
TODO: Also define the projection to source?
-/

@[simp, mfld_simps] lemma one_jet_bundle.proj_apply (p : M × M') (σ : one_jet_space I I' p) :
  one_jet_bundle.proj I M I' M' ⟨p, σ⟩ = p :=
rfl


section one_jet_bundle_instances

/- In general, the definition of one_jet_bundle and one_jet_space are not reducible, so that type
class inference does not pick wrong instances. In this section, we record the right instances for
them, noting in particular that the one_jet bundle is a smooth manifold. -/

section
local attribute [reducible] one_jet_space

variables {M} (p : M × M')

instance : topological_space (one_jet_space I I' p) := by apply_instance
instance : add_comm_group (one_jet_space I I' p) := by apply_instance
instance : topological_add_group (one_jet_space I I' p) := by apply_instance
instance : module 𝕜 (one_jet_space I I' p) := by apply_instance
instance : inhabited (one_jet_space I I' p) := ⟨0⟩

end

variable (M)

instance : topological_space J¹MM' :=
(one_jet_bundle_core I M I' M').to_topological_vector_bundle_core.to_topological_space (atlas (model_prod H H') (M × M'))

instance : charted_space (model_prod (model_prod H H') (E →L[𝕜] E')) J¹MM' :=
(one_jet_bundle_core I M I' M').to_charted_space

instance : smooth_manifold_with_corners ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) J¹MM' :=
(one_jet_bundle_core I M I' M').to_smooth_manifold

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
