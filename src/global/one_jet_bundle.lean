/-
Copyright (c) 2022 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Floris van Doorn
-/
import to_mathlib.geometry.manifold.vector_bundle.basic_core_constructions
import interactive_expr
set_option trace.filter_inst_type true

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
open_locale manifold topological_space

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
  in_coordinates' (tangent_bundle_core I M) (tangent_bundle_core I' M')
    v.1.1 v'.1.1 v.1.2 v'.1.2 v'.2) :=
begin
  simp_rw [to_charted_space_chart_at],
  dsimp only [one_jet_bundle_core],
  simp_rw [hom_chart, in_coordinates', pullback_fst_coord_change_at,
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
    function.comp_app, continuous_linear_equiv.coe_coe, in_coordinates'],
  erw [← (tangent_bundle_core I' M').coe_coord_change_equiv hx,
       ← (tangent_bundle_core I M).coe_coord_change_equiv hy],
end

/-- Computing the value of an extended chart around `v` at point `v'` in `J¹(M, M')`.
  The last component equals the continuous linear map `v'.2`, composed on both sides by an
  appropriate coordinate change function. -/
-- unused
lemma one_jet_bundle_ext_chart_at {v v' : one_jet_bundle I M I' M'} :
  ext_chart_at ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) v v' =
  ((ext_chart_at I v.1.1 v'.1.1, ext_chart_at I' v.1.2 v'.1.2),
  in_coordinates' (tangent_bundle_core I M) (tangent_bundle_core I' M')
  v.1.1 v'.1.1 v.1.2 v'.1.2 v'.2) :=
by simp_rw [ext_chart_at_coe, function.comp_apply, one_jet_bundle_chart_at,
    model_with_corners.prod_apply, model_with_corners_self_coe, id]

section maps

variables {M M'}

variables {I I' J J'}

lemma smooth_one_jet_bundle_proj :
  smooth ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) (I.prod I') (one_jet_bundle.proj I M I' M') :=
basic_smooth_vector_bundle_core.smooth_proj _

lemma smooth.one_jet_bundle_proj {f : N → one_jet_bundle I M I' M'}
  (hf : smooth J ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) f) :
  smooth J (I.prod I') (λ x, (f x).1) :=
smooth_one_jet_bundle_proj.comp hf

lemma smooth_at.one_jet_bundle_proj {f : N → one_jet_bundle I M I' M'} {x₀ : N}
  (hf : smooth_at J ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) f x₀) :
  smooth_at J (I.prod I') (λ x, (f x).1) x₀ :=
(smooth_one_jet_bundle_proj _).comp x₀ hf

/-- The constructor of one_jet_bundle, in case `sigma.mk` will not give the right type. -/
@[simp] def one_jet_bundle.mk (x : M) (y : M') (f : one_jet_space I I' (x, y)) :
  one_jet_bundle I M I' M' :=
⟨(x, y), f⟩

@[simp, mfld_simps] lemma one_jet_bundle_mk_fst {x : M} {y : M'} {f : one_jet_space I I' (x, y)} :
  (one_jet_bundle.mk x y f).1 = (x, y) := rfl

@[simp, mfld_simps] lemma one_jet_bundle_mk_snd {x : M} {y : M'} {f : one_jet_space I I' (x, y)} :
  (one_jet_bundle.mk x y f).2 = f := rfl

lemma smooth_at_one_jet_bundle {f : N → one_jet_bundle I M I' M'} {x₀ : N} :
  smooth_at J ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) f x₀ ↔
  smooth_at J I (λ x, (f x).1.1) x₀ ∧ smooth_at J I' (λ x, (f x).1.2) x₀ ∧
  smooth_at J 𝓘(𝕜, E →L[𝕜] E') (in_coordinates I I' (λ x, (f x).1.1) (λ x, (f x).1.2)
    (λ x, (f x).2) x₀) x₀ :=
begin
  simp_rw [smooth_at_hom_bundle, in_coordinates', pullback_fst_coord_change_at,
    pullback_snd_coord_change_at],
  refine ⟨λ h, ⟨h.1.fst, h.1.snd, h.2⟩, λ h, ⟨_, h.2.2⟩⟩,
  convert h.1.prod_mk h.2.1,
  ext x; refl
end

lemma smooth_at.in_coordinates_snd {f : N → one_jet_bundle I M I' M'} {x₀ : N}
  (hf : smooth_at J ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) f x₀) :
  smooth_at J 𝓘(𝕜, E →L[𝕜] E') (in_coordinates I I' (λ x, (f x).1.1) (λ x, (f x).1.2)
    (λ x, (f x).2) x₀) x₀ :=
(smooth_at_one_jet_bundle.mp hf).2.2

lemma smooth_at_one_jet_bundle_mk {f : N → M} {g : N → M'} {ϕ : N → E →L[𝕜] E'} {x₀ : N} :
  smooth_at J ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E'))
    (λ x, one_jet_bundle.mk (f x) (g x) (ϕ x) : N → one_jet_bundle I M I' M') x₀ ↔
  smooth_at J I f x₀ ∧ smooth_at J I' g x₀ ∧
  smooth_at J 𝓘(𝕜, E →L[𝕜] E') (in_coordinates I I' f g ϕ x₀) x₀ :=
smooth_at_one_jet_bundle

lemma smooth_at.one_jet_bundle_mk {f : N → M} {g : N → M'} {ϕ : N → E →L[𝕜] E'} {x₀ : N}
  (hf : smooth_at J I f x₀) (hg : smooth_at J I' g x₀)
  (hϕ : smooth_at J 𝓘(𝕜, E →L[𝕜] E') (in_coordinates I I' f g ϕ x₀) x₀) :
  smooth_at J ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E'))
    (λ x, one_jet_bundle.mk (f x) (g x) (ϕ x) : N → one_jet_bundle I M I' M') x₀ :=
smooth_at_one_jet_bundle.mpr ⟨hf, hg, hϕ⟩

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
-- hg.one_jet_bundle_mk hf sorry

lemma smooth_at.one_jet_ext {f : M → M'} {x : M} (hf : smooth_at I I' f x) :
  smooth_at I ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) (one_jet_ext I I' f) x :=
smooth_at_id.one_jet_bundle_mk hf (hf.mfderiv' le_rfl)

-- lemma smooth.one_jet_ext' {f : N → M → M'} {g : N → M}
--   (hf : smooth (J.prod I) I' (function.uncurry f)) (hg : smooth J I g) :
--   smooth J ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) (λ x, one_jet_ext I I' (f x) (g x)) :=
-- λ x, hf.smooth_at.one_jet_ext' hg.smooth_at

lemma smooth.one_jet_ext {f : M → M'} (hf : smooth I I' f) :
  smooth I ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) (one_jet_ext I I' f) :=
λ x, (hf x).smooth_at.one_jet_ext

lemma continuous_at.in_coordinates_comp {f : N → M} {g : N → M'} {h : N → N'}
  {ϕ' : N → E' →L[𝕜] F'} {ϕ : N → E →L[𝕜] E'} {x₀ : N}
  (hg : continuous_at g x₀) :
  in_coordinates I J' f h (λ x, ϕ' x ∘L ϕ x) x₀ =ᶠ[𝓝 x₀]
  λ x, in_coordinates I' J' g h ϕ' x₀ x ∘L in_coordinates I I' f g ϕ x₀ x :=
begin
  refine eventually_of_mem (hg.preimage_mem_nhds $
    (achart H' (g x₀)).1.open_source.mem_nhds $ mem_achart_source H' (g x₀)) (λ x hx, _),
  ext v,
  simp_rw [function.comp_apply, in_coordinates, in_coordinates', continuous_linear_map.comp_apply],
  congr' 2,
  symmetry,
  exact (tangent_bundle_core I' M').coord_change_comp_eq_self' (mem_achart_source H' (g x)) hx _
end

lemma smooth_at.clm_comp_in_coordinates {f : N → M} {g : N → M'} {h : N → N'}
  {ϕ' : N → E' →L[𝕜] F'} {ϕ : N → E →L[𝕜] E'} {n : N}
  (hg : continuous_at g n)
  (hϕ' : smooth_at J 𝓘(𝕜, E' →L[𝕜] F') (in_coordinates I' J' g h ϕ' n) n)
  (hϕ : smooth_at J 𝓘(𝕜, E →L[𝕜] E') (in_coordinates I I' f g ϕ n) n) :
  smooth_at J (𝓘(𝕜, E →L[𝕜] F')) (in_coordinates I J' f h (λ n, ϕ' n ∘L ϕ n) n) n :=
(hϕ'.clm_comp hϕ).congr_of_eventually_eq (hg.in_coordinates_comp)

variables (I')
lemma smooth.one_jet_comp {f1 : N' → M} (f2 : N' → M') {f3 : N' → N}
  {h : ∀ x : N', one_jet_space I' J (f2 x, f3 x)} {g : ∀ x : N', one_jet_space I I' (f1 x, f2 x)}
  (hh : smooth J' ((I'.prod J).prod 𝓘(𝕜, E' →L[𝕜] F)) (λ x, one_jet_bundle.mk _ _ (h x)))
  (hg : smooth J' ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) (λ x, one_jet_bundle.mk _ _ (g x))) :
  smooth J' ((I.prod J).prod 𝓘(𝕜, E →L[𝕜] F))
    (λ x, one_jet_bundle.mk (f1 x) (f3 x) (h x ∘L g x) : N' → one_jet_bundle I M J N) :=
begin
  intro x,
  specialize hh x,
  specialize hg x,
  rw [← smooth_at, smooth_at_one_jet_bundle_mk] at hh hg ⊢,
  exact ⟨hg.1, hh.2.1, hh.2.2.clm_comp_in_coordinates hg.2.1.continuous_at hg.2.2⟩
end

variables {I'}
lemma smooth.one_jet_add {f : N → M} {g : N → M'}
  {ϕ ϕ' : ∀ x : N, one_jet_space I I' (f x, g x)}
  (hϕ : smooth J ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) (λ x, one_jet_bundle.mk _ _ (ϕ x)))
  (hϕ' : smooth J ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) (λ x, one_jet_bundle.mk _ _ (ϕ' x))) :
  smooth J ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E'))
    (λ x, one_jet_bundle.mk (f x) (g x) (ϕ x + ϕ' x)) :=
begin
  intro x,
  specialize hϕ x,
  specialize hϕ' x,
  rw [← smooth_at, smooth_at_one_jet_bundle_mk] at hϕ hϕ' ⊢,
  simp_rw [in_coordinates, in_coordinates', continuous_linear_map.add_comp,
    continuous_linear_map.comp_add],
  exact ⟨hϕ.1, hϕ.2.1, hϕ.2.2.add hϕ'.2.2⟩
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
begin
  intro x,
  refine smooth_at.one_jet_bundle_mk _ _ _,
  { exact smooth_one_jet_bundle_proj.fst.snd x },
  { exact smooth_one_jet_bundle_proj.snd x },
  sorry
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
