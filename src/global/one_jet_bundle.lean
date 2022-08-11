/-
Copyright (c) 2022 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Floris van Doorn
-/
import to_mathlib.geometry.manifold.vector_bundle.basic_core_constructions

/-!
# 1-jet bundles

This file contains the definition of the 1-jet bundle `J¹(M, M')`, also known as
`one_jet_bundle I M I' M'`.

We also define
* `one_jet_ext I I' f : M → J¹(M, M')`: the 1-jet extension `j¹f` of a map `f : M → M'`

We prove
* If `f` is smooth, `j¹f` is smooth.
* If `x ↦ (f₁ x, f₂ x, ϕ₁ x) : N → J¹(M₁, M₂)` and `x ↦ (f₂ x, f₃ x, ϕ₂ x) : N → J¹(M₂, M₃)` are smooth, then so is `x ↦ (f₁ x, f₃ x, ϕ₂ x ∘ ϕ₁ x) : N → J¹(M₁, M₃)`.
-/

noncomputable theory

open filter set equiv basic_smooth_vector_bundle_core
open_locale manifold

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
  {H : Type*} [topological_space H]
  (I : model_with_corners 𝕜 E H)
  (M : Type*) [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
  {E' : Type*} [normed_add_comm_group E'] [normed_space 𝕜 E']
  {H' : Type*} [topological_space H']
  (I' : model_with_corners 𝕜 E' H')
  (M' : Type*) [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M']
  {F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]
  {G : Type*} [topological_space G] (J : model_with_corners 𝕜 F G)
  {N : Type*} [topological_space N] [charted_space G N] [smooth_manifold_with_corners J N]
  {F' : Type*} [normed_add_comm_group F'] [normed_space 𝕜 F']
  {G' : Type*} [topological_space G'] (J' : model_with_corners 𝕜 F' G')
  {N' : Type*} [topological_space N'] [charted_space G' N'] [smooth_manifold_with_corners J' N']

/-- The one jet-bundle, as a a `basic_smooth_vector_bundle_core` -/
def one_jet_bundle_core : basic_smooth_vector_bundle_core (I.prod I') (M × M') (E →L[𝕜] E') :=
((tangent_bundle_core I M).pullback_fst M' I').hom $ (tangent_bundle_core I' M').pullback_snd M I

include I I'
variables {M M'}

/-- The fibers of the one jet-bundle. -/
@[nolint unused_arguments]
def one_jet_space (p : M × M') : Type* := tangent_space I p.1 →L[𝕜] tangent_space I' p.2

instance (p : M × M') : has_coe_to_fun (one_jet_space I I' p)
  (λ σ, tangent_space I p.1 → tangent_space I' p.2) := ⟨λ φ, φ.to_fun⟩

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

section

variables {M} (p : M × M')

instance : normed_add_comm_group (one_jet_space I I' p) := by delta_instance one_jet_space
instance : normed_space 𝕜 (one_jet_space I I' p) := by delta_instance one_jet_space
instance : inhabited (one_jet_space I I' p) := ⟨0⟩

end

variable (M)

instance : topological_space J¹MM' :=
(one_jet_bundle_core I M I' M').to_topological_vector_bundle_core.to_topological_space
  (atlas (model_prod H H') (M × M'))

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

/-- Computing the value of a chart around `v` at point `v'` in `J¹(M, M')`.
  The last component equals the continuous linear map `v'.2`, composed on both sides by an
  appropriate coordinate change function. -/
lemma one_jet_bundle_chart_at {v v' : one_jet_bundle I M I' M'} :
  chart_at (model_prod (model_prod H H') (E →L[𝕜] E')) v v' =
  ((chart_at H v.1.1 v'.1.1, chart_at H' v.1.2 v'.1.2),
  ((tangent_bundle_core I' M').coord_change (achart H' v'.1.2) (achart H' v.1.2)
    (chart_at H' v'.1.2 v'.1.2)).comp $ v'.2.comp $
    (tangent_bundle_core I M).coord_change (achart H v.1.1) (achart H v'.1.1)
    (chart_at H v.1.1 v'.1.1)) :=
begin
  simp_rw [to_charted_space_chart_at],
  dsimp only [one_jet_bundle_core],
  simp_rw [hom_chart, ← achart_def, pullback_fst_coord_change_at,
    pullback_snd_coord_change_at, prod_charted_space_chart_at, local_homeomorph.prod_apply],
end

/-- Computing the value of an extended chart around `v` at point `v'` in `J¹(M, M')`.
  The last component equals the continuous linear map `v'.2`, composed on both sides by an
  appropriate coordinate change function. -/
lemma one_jet_bundle_ext_chart_at {v v' : one_jet_bundle I M I' M'} :
  ext_chart_at ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) v v' =
  ((I (chart_at H v.1.1 v'.1.1), I' (chart_at H' v.1.2 v'.1.2)),
  ((tangent_bundle_core I' M').coord_change (achart H' v'.1.2) (achart H' v.1.2)
    (chart_at H' v'.1.2 v'.1.2)).comp $ v'.2.comp $
    (tangent_bundle_core I M).coord_change (achart H v.1.1) (achart H v'.1.1)
    (chart_at H v.1.1 v'.1.1)) :=
by simp_rw [ext_chart_at_coe, function.comp_apply, one_jet_bundle_chart_at,
    model_with_corners.prod_apply, model_with_corners_self_coe, id]

section maps

variables {M M'}

/-- The one-jet extension of a function -/
def one_jet_ext (f : M → M') : M → one_jet_bundle I M I' M' :=
λ x, ⟨(x, f x), (mfderiv I I' f x : tangent_space I x →L[𝕜] tangent_space I' (f x))⟩

variables {I I'}

/-- The constructor of one_jet_bundle, in case `sigma.mk` will not give the right type. -/
@[simp] def one_jet_bundle.mk (x : M) (y : M') (f : one_jet_space I I' (x, y)) :
  one_jet_bundle I M I' M' :=
⟨(x, y), f⟩

@[simp, mfld_simps] lemma one_jet_bundle_mk_fst {x : M} {y : M'} {f : one_jet_space I I' (x, y)} :
  (one_jet_bundle.mk x y f).1 = (x, y) := rfl

@[simp, mfld_simps] lemma one_jet_bundle_mk_snd {x : M} {y : M'} {f : one_jet_space I I' (x, y)} :
  (one_jet_bundle.mk x y f).2 = f := rfl

@[simp, mfld_simps] lemma one_jet_ext_one_jet_bundle_proj {f : M → M'} {x :  M} :
  one_jet_bundle.proj I M I' M' (one_jet_ext I I' f x) = (x, f x) := rfl

@[simp, mfld_simps] lemma one_jet_ext_proj {f : M → M'} {x :  M} :
  (one_jet_ext I I' f x).1 = (x, f x) := rfl

lemma smooth_at.one_jet_ext {f : M → M'} {x : M} (hf : smooth_at I I' f x) :
  smooth_at I ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) (one_jet_ext I I' f) x :=
begin
  rw [smooth_at, (one_jet_bundle_core I M I' M').cont_mdiff_at_iff_target],
  refine ⟨continuous_at_id.prod hf.continuous_at, _⟩,
  simp_rw [function.comp, one_jet_bundle_ext_chart_at],
  refine (cont_mdiff_at_ext_chart_at.prod_mk_space $ cont_mdiff_at_ext_chart_at.comp _ hf)
    .prod_mk_space _,
  exact hf.mfderiv' le_rfl
end

lemma smooth.one_jet_ext {f : M → M'} (hf : smooth I I' f) :
  smooth I ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) (one_jet_ext I I' f) :=
λ x, (hf x).smooth_at.one_jet_ext

variables (I I' J J')
lemma smooth.one_jet_comp
  {f1 : N' → M} (f2 : N' → M') {f3 : N' → N}
  {h : ∀ x : N', one_jet_space I' J (f2 x, f3 x)} {g : ∀ x : N', one_jet_space I I' (f1 x, f2 x)}
  (hh : smooth J' ((I'.prod J).prod 𝓘(𝕜, E' →L[𝕜] F)) (λ x, one_jet_bundle.mk _ _ (h x)))
  (hg : smooth J' ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) (λ x, one_jet_bundle.mk _ _ (g x))) :
  smooth J' ((I.prod J).prod 𝓘(𝕜, E →L[𝕜] F))
    (λ x, one_jet_bundle.mk (f1 x) (f3 x) (h x ∘L g x) : N' → one_jet_bundle I M J N) :=
begin
  rw [basic_smooth_vector_bundle_core.smooth_iff_target] at hh hg ⊢,
  refine ⟨hg.1.fst.prod_mk hh.1.snd, _⟩,
  intro x,
  have hf2 : continuous_at f2 x := hg.1.snd.continuous_at,
  simp_rw [function.comp, one_jet_bundle_ext_chart_at],
  refine ((cont_diff_at_fst.fst.cont_mdiff_at.comp _ (hg.2 x)).prod_mk_space $
    cont_diff_at_fst.snd.cont_mdiff_at.comp _ (hh.2 x)).prod_mk_space _,
  have h1 := (cont_diff_at_snd.cont_mdiff_at.comp _ (hg.2 x)),
  have h2 := (cont_diff_at_snd.cont_mdiff_at.comp _ (hh.2 x)),
  refine (h2.clm_comp h1).congr_of_eventually_eq _,
  refine eventually_of_mem (hf2.preimage_mem_nhds $ (achart H' (f2 x)).1.open_source.mem_nhds $
    mem_achart_source H' (f2 x)) (λ x' hx', _),
  ext v,
  simp_rw [function.comp_apply, one_jet_bundle_ext_chart_at,
    one_jet_bundle_mk_fst, one_jet_bundle_mk_snd, continuous_linear_map.comp_apply],
  congr' 2,
  symmetry,
  exact (tangent_bundle_core I' M').coord_change_comp_eq_self' (mem_achart_source H' (f2 x')) hx' _
end

end maps

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
