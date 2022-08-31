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
local notation `HJ` := model_prod (model_prod H H') (E →L[𝕜] E')

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

instance : charted_space HJ J¹MM' :=
(one_jet_bundle_core I M I' M').to_charted_space

instance : smooth_manifold_with_corners ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) J¹MM' :=
(one_jet_bundle_core I M I' M').to_smooth_manifold

instance : topological_vector_bundle 𝕜 (E →L[𝕜] E') (one_jet_space I I' : M × M' → Type*) :=
topological_vector_bundle_core.fiber.topological_vector_bundle
  (one_jet_bundle_core I M I' M').to_topological_vector_bundle_core

-- /-- `J¹(M, M')` is σ-compact. This is needed if we need metrizability of `J¹(M, M')`. -/
-- instance [sigma_compact_space M] [sigma_compact_space M'] :
--   sigma_compact_space (one_jet_bundle I M I' M') :=
-- by admit

-- /-- `J¹(M, M')` is Hausdorff. This is needed if we need metrizability of `J¹(M, M')`. -/
-- instance [t2_space M] [t2_space M'] : t2_space (one_jet_bundle I M I' M') :=
-- by admit

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
  appropriate coordinate change function.

See also `one_jet_bundle_chart_at'`. -/
lemma one_jet_bundle_chart_at {v v' : one_jet_bundle I M I' M'} :
  chart_at HJ v v' =
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

/-- A variant of `one_jet_bundle_chart_at` in which the fact that the coordinate change actions
are equivalences is expressed at the type-theoretic level (i.e., `coord_change_equiv` instead of
`coord_change`). -/
lemma one_jet_bundle_chart_at' {v v' : J¹MM'} (hv' : v' ∈ (chart_at HJ v).source) :
  chart_at HJ v v' =
  ((chart_at H v.1.1 v'.1.1, chart_at H' v.1.2 v'.1.2),
   ((tangent_bundle_core I' M').coord_change_equiv
       (achart H' v'.1.2) (achart H' v.1.2) v'.1.2 : E' →L[𝕜] E').comp $
   v'.2.comp $
   ((tangent_bundle_core I M).coord_change_equiv
       (achart H v.1.1) (achart H v'.1.1) v'.1.1 : E →L[𝕜] E)) :=
begin
  have hx : v'.1.2 ∈ (achart H' v'.1.2 : local_homeomorph M' H').source ∩
                     (achart H' v.1.2  : local_homeomorph M' H').source,
  { simp only [to_charted_space_chart_at, chart_source] at hv',
    simpa only [coe_achart, mem_inter_eq, mem_chart_source, true_and] using hv'.2, },
  have hy : v'.1.1 ∈ (achart H  v.1.1  : local_homeomorph M H).source ∩
                     (achart H  v'.1.1 : local_homeomorph M H).source,
  { simp only [to_charted_space_chart_at, chart_source] at hv',
    simpa only [coe_achart, mem_inter_eq, mem_chart_source, and_true] using hv'.1, },
  simp only [one_jet_bundle_chart_at I M I' M', prod.mk.inj_iff, eq_self_iff_true, true_and],
  ext e,
  simp only [tangent_bundle_core_coord_change, achart_val, continuous_linear_map.coe_comp',
    function.comp_app, continuous_linear_equiv.coe_coe],
  erw [← (tangent_bundle_core I' M').coe_coord_change_equiv hx,
       ← (tangent_bundle_core I M).coe_coord_change_equiv hy],
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


variables {I I' J J'}

/-- The constructor of one_jet_bundle, in case `sigma.mk` will not give the right type. -/
@[simp] def one_jet_bundle.mk (x : M) (y : M') (f : one_jet_space I I' (x, y)) :
  one_jet_bundle I M I' M' :=
⟨(x, y), f⟩

@[simp, mfld_simps] lemma one_jet_bundle_mk_fst {x : M} {y : M'} {f : one_jet_space I I' (x, y)} :
  (one_jet_bundle.mk x y f).1 = (x, y) := rfl

@[simp, mfld_simps] lemma one_jet_bundle_mk_snd {x : M} {y : M'} {f : one_jet_space I I' (x, y)} :
  (one_jet_bundle.mk x y f).2 = f := rfl

lemma smooth_at.one_jet_bundle_mk {f : N → M} {g : N → M'} {ϕ : N → E →L[𝕜] E'} {n : N}
  (hf : smooth_at J I f n) (hg : smooth_at J I' g n)
  (hϕ : smooth_at J 𝓘(𝕜, E →L[𝕜] E')
    (λ x, ((tangent_bundle_core I' M').coord_change (achart H' (g x)) (achart H' (g n))
      (chart_at H' (g x) (g x))).comp $ (ϕ x).comp $
    (tangent_bundle_core I M).coord_change (achart H (f n)) (achart H (f x))
    (chart_at H (f n) (f x))) n) :
  smooth_at J ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E'))
    (λ x, one_jet_bundle.mk (f x) (g x) (ϕ x) : N → one_jet_bundle I M I' M') n :=
begin
  rw [smooth_at, (one_jet_bundle_core I M I' M').cont_mdiff_at_iff_target],
  refine ⟨hf.continuous_at.prod hg.continuous_at, _⟩,
  simp_rw [function.comp, one_jet_bundle_ext_chart_at],
  refine ((cont_mdiff_at_ext_chart_at.comp _ hf).prod_mk_space $
    cont_mdiff_at_ext_chart_at.comp _ hg).prod_mk_space hϕ
end

variables (I I')
/-- The one-jet extension of a function -/
def one_jet_ext (f : M → M') : M → one_jet_bundle I M I' M' :=
λ x, one_jet_bundle.mk x (f x) (mfderiv I I' f x)

variables {I I'}

@[simp, mfld_simps] lemma one_jet_ext_one_jet_bundle_proj {f : M → M'} {x :  M} :
  one_jet_bundle.proj I M I' M' (one_jet_ext I I' f x) = (x, f x) := rfl

@[simp, mfld_simps] lemma one_jet_ext_proj {f : M → M'} {x : M} :
  (one_jet_ext I I' f x).1 = (x, f x) := rfl

-- /-- A family of one-jet extensions indexed by a parameter is smooth. Currently unused and
-- `admit`ted -/
-- lemma smooth_at.one_jet_ext' {f : N → M → M'} {g : N → M} {n : N}
--   (hf : smooth_at (J.prod I) I' (function.uncurry f) (n, g n)) (hg : smooth_at J I g n) :
--   smooth_at J ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) (λ x, one_jet_ext I I' (f x) (g x)) n :=
-- begin
--   -- it is so horrible to work with `cont_mdiff_at.comp`
--   have : smooth_at J I' (λ x, f x (g x)) n,
--   { exact cont_mdiff_at.comp n hf (smooth_at_id.prod_mk hg) },
--   refine hg.one_jet_bundle_mk this _,
--   -- refine cont_mdiff_at.mfderiv'' _ _ _,
--   -- rw [smooth_at, (one_jet_bundle_core I M I' M').cont_mdiff_at_iff_target],
--   -- refine ⟨hg.continuous_at.prod this.continuous_at, _⟩,
--   -- simp_rw [function.comp, one_jet_bundle_ext_chart_at],
--   -- dsimp only [one_jet_ext_proj],
--   -- refine ((cont_mdiff_at_ext_chart_at.comp _ hg).prod_mk_space $
--   --   cont_mdiff_at_ext_chart_at.comp _ this).prod_mk_space _,
--   admit
--   -- exact hf.mfderiv' le_rfl
-- end

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

-- lemma smooth.one_jet_ext' {f : N → M → M'} {g : N → M}
--   (hf : smooth (J.prod I) I' (function.uncurry f)) (hg : smooth J I g) :
--   smooth J ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) (λ x, one_jet_ext I I' (f x) (g x)) :=
-- λ x, hf.smooth_at.one_jet_ext' hg.smooth_at

lemma smooth.one_jet_ext {f : M → M'} (hf : smooth I I' f) :
  smooth I ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) (one_jet_ext I I' f) :=
λ x, (hf x).smooth_at.one_jet_ext

variables (I')
lemma smooth.one_jet_comp {f1 : N' → M} (f2 : N' → M') {f3 : N' → N}
  {h : ∀ x : N', one_jet_space I' J (f2 x, f3 x)} {g : ∀ x : N', one_jet_space I I' (f1 x, f2 x)}
  (hh : smooth J' ((I'.prod J).prod 𝓘(𝕜, E' →L[𝕜] F)) (λ x, one_jet_bundle.mk _ _ (h x)))
  (hg : smooth J' ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) (λ x, one_jet_bundle.mk _ _ (g x))) :
  smooth J' ((I.prod J).prod 𝓘(𝕜, E →L[𝕜] F))
    (λ x, one_jet_bundle.mk (f1 x) (f3 x) (h x ∘L g x) : N' → one_jet_bundle I M J N) :=
begin
  rw [basic_smooth_vector_bundle_core.smooth_iff_target] at hh hg ⊢,
  refine ⟨hg.1.fst.prod_mk hh.1.snd, λ x, _⟩,
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

variables {I'}
lemma smooth.one_jet_add {f : N → M} {g : N → M'}
  {ϕ ϕ' : ∀ x : N, one_jet_space I I' (f x, g x)}
  (hϕ : smooth J ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) (λ x, one_jet_bundle.mk _ _ (ϕ x)))
  (hϕ' : smooth J ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) (λ x, one_jet_bundle.mk _ _ (ϕ' x))) :
  smooth J ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E'))
    (λ x, one_jet_bundle.mk (f x) (g x) (ϕ x + ϕ' x)) :=
begin
  rw [basic_smooth_vector_bundle_core.smooth_iff_target] at hϕ hϕ' ⊢,
  refine ⟨hϕ.1.fst.prod_mk hϕ.1.snd, λ x, _⟩,
  simp_rw [function.comp, one_jet_bundle_ext_chart_at],
  refine ((cont_diff_at_fst.fst.cont_mdiff_at.comp _ (hϕ.2 x)).prod_mk_space $
    cont_diff_at_fst.snd.cont_mdiff_at.comp _ (hϕ.2 x)).prod_mk_space _,
  have h1 := (cont_diff_at_snd.cont_mdiff_at.comp _ (hϕ.2 x)),
  have h2 := (cont_diff_at_snd.cont_mdiff_at.comp _ (hϕ'.2 x)),
  refine (h1.add h2).congr_of_eventually_eq (eventually_of_forall $ λ x', _),
  ext v,
  simp_rw [pi.add_apply, function.comp_apply, one_jet_bundle_ext_chart_at,
    one_jet_bundle_mk_fst, one_jet_bundle_mk_snd, continuous_linear_map.add_apply,
    continuous_linear_map.comp_apply, continuous_linear_map.add_apply,
    continuous_linear_map.map_add]
end

/-- A useful definition to define maps between two one_jet_bundles. -/
def map_left (f : M → N) (Dfinv : ∀ x : M, tangent_space J (f x) →L[𝕜] tangent_space I x) :
  one_jet_bundle I M I' M' → one_jet_bundle J N I' M' :=
λ p, one_jet_bundle.mk (f p.1.1) p.1.2 (p.2 ∘L Dfinv p.1.1)

def bundle_fst : one_jet_bundle (J.prod I) (N × M) I' M' → one_jet_bundle J N I' M' :=
map_left prod.fst $ λ x, continuous_linear_map.inl 𝕜 F E

def bundle_snd : one_jet_bundle (J.prod I) (N × M) I' M' → one_jet_bundle I M I' M' :=
map_left prod.snd $ λ x, continuous_linear_map.inr 𝕜 F E

lemma smooth_bundle_snd :
  smooth (((J.prod I).prod I').prod 𝓘(𝕜, F × E →L[𝕜] E')) ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E'))
    (bundle_snd : one_jet_bundle (J.prod I) (N × M) I' M' → one_jet_bundle I M I' M') :=
sorry

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
