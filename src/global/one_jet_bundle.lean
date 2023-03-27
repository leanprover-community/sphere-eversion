/-
Copyright (c) 2022 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Floris van Doorn
-/
import to_mathlib.geometry.manifold.vector_bundle.misc
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

open filter set equiv bundle
open_locale manifold topology bundle

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
  {H : Type*} [topological_space H] (I : model_with_corners 𝕜 E H)
  (M : Type*) [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
  {E' : Type*} [normed_add_comm_group E'] [normed_space 𝕜 E']
  {H' : Type*} [topological_space H'] (I' : model_with_corners 𝕜 E' H')
  (M' : Type*) [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M']
  {E'' : Type*} [normed_add_comm_group E''] [normed_space 𝕜 E'']
  {H'' : Type*} [topological_space H''] {I'' : model_with_corners 𝕜 E'' H''}
  {M'' : Type*} [topological_space M''] [charted_space H'' M'']
  [smooth_manifold_with_corners I'' M'']
  {F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]
  {G : Type*} [topological_space G] (J : model_with_corners 𝕜 F G)
  {N : Type*} [topological_space N] [charted_space G N] [smooth_manifold_with_corners J N]
  {F' : Type*} [normed_add_comm_group F'] [normed_space 𝕜 F']
  {G' : Type*} [topological_space G'] (J' : model_with_corners 𝕜 F' G')
  {N' : Type*} [topological_space N'] [charted_space G' N'] [smooth_manifold_with_corners J' N']
  {E₂ : Type*} [normed_add_comm_group E₂] [normed_space 𝕜 E₂]
  {H₂ : Type*} [topological_space H₂] {I₂ : model_with_corners 𝕜 E₂ H₂}
  {M₂ : Type*} [topological_space M₂] [charted_space H₂ M₂] [smooth_manifold_with_corners I₂ M₂]
  {E₃ : Type*} [normed_add_comm_group E₃] [normed_space 𝕜 E₃]
  {H₃ : Type*} [topological_space H₃] {I₃ : model_with_corners 𝕜 E₃ H₃}
  {M₃ : Type*} [topological_space M₃] [charted_space H₃ M₃] [smooth_manifold_with_corners I₃ M₃]

-- /-- The one jet-bundle -/
-- def one_jet_bundle_core : basic_smooth_vector_bundle_core (I.prod I') (M × M') (E →L[𝕜] E') :=
-- ((tangent_bundle_core I M).pullback_fst M' I').hom $ (tangent_bundle_core I' M').pullback_snd M I

variables {M M'}

local notation `σ` := ring_hom.id 𝕜

/-- The fibers of the one jet-bundle. -/
@[nolint unused_arguments, derive [add_comm_monoid, topological_space]]
def one_jet_space (p : M × M') : Type* :=
bundle.continuous_linear_map σ E
  ((cont_mdiff_map.fst : C^∞⟮I.prod I', M × M'; I, M⟯) *ᵖ tangent_space I) E'
  ((cont_mdiff_map.snd : C^∞⟮I.prod I', M × M'; I', M'⟯) *ᵖ tangent_space I') p

variables {I I'}
-- what is better notation for this?
local notation `FJ¹MM'` := (one_jet_space I I' : M × M' → Type*)
variables (I I')
instance (p : M × M') : has_coe_to_fun (one_jet_space I I' p)
  (λ _, tangent_space I p.1 → tangent_space I' p.2) := ⟨λ φ, φ.to_fun⟩

variables (M M')

/-- The space of one jets of maps between two smooth manifolds, as a Sigma type.
Defined in terms of `bundle.total_space` to be able to put a suitable topology on it. -/
@[nolint has_inhabited_instance, reducible] -- is empty if the base manifold is empty
def one_jet_bundle := total_space (one_jet_space I I' : M × M' → Type*)

variables {I I' M M'}
local notation `J¹MM'` := one_jet_bundle I M I' M'
local notation `HJ` := model_prod (model_prod H H') (E →L[𝕜] E')

@[ext] lemma one_jet_bundle.ext {x y : J¹MM'} (h : x.1.1 = y.1.1) (h' : x.1.2 = y.1.2)
  (h'' : x.2 = y.2) : x = y :=
begin
  rcases x with ⟨⟨a, b⟩, c⟩,
  rcases y with ⟨⟨d, e⟩, f⟩,
  dsimp only at h h' h'',
  rw [h, h', h'']
end

variables (I I' M M')

-- /-- The projection from the one jet bundle of smooth manifolds to the product manifold. As the
-- one_jet bundle is represented internally as a sigma type, the notation `p.1` also works for the
-- projection of the point `p`. -/
-- def one_jet_bundle.proj : J¹MM' → M × M' :=
-- λ p, p.1

section one_jet_bundle_instances

section

variables {M} (p : M × M')

instance (x : M × M') : module 𝕜 (FJ¹MM' x) :=
by delta_instance one_jet_space

-- instance : normed_add_comm_group (one_jet_space I I' p) := by delta_instance one_jet_space
-- instance : inhabited (one_jet_space I I' p) := ⟨0⟩

end

variable (M)

instance : topological_space J¹MM' :=
by delta_instance one_jet_bundle one_jet_space

instance : fiber_bundle (E →L[𝕜] E') FJ¹MM' :=
by delta_instance one_jet_space

instance : vector_bundle 𝕜 (E →L[𝕜] E') FJ¹MM' :=
by delta_instance one_jet_space

instance : charted_space HJ J¹MM' :=
by delta_instance one_jet_bundle one_jet_space

instance : smooth_manifold_with_corners ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) J¹MM' :=
by delta_instance one_jet_bundle one_jet_space

end one_jet_bundle_instances

variable (M)

/-- The tangent bundle projection on the basis is a continuous map. -/
lemma one_jet_bundle_proj_continuous : continuous (π FJ¹MM') :=
continuous_proj (E →L[𝕜] E') FJ¹MM'

lemma trivialization_at_one_jet_bundle_apply (x₀ : M × M') (x : J¹MM') :
  trivialization_at (E →L[𝕜] E') FJ¹MM' x₀ x =
  ⟨x.1, (trivialization_at E' (tangent_space I') x₀.2).continuous_linear_map_at 𝕜 x.1.2 ∘L x.2 ∘L
    (trivialization_at E (tangent_space I) x₀.1).symmL 𝕜 x.1.1⟩ :=
begin
  refine (trivialization_at_hom_apply x₀ x).trans _,
  have : trivialization.symmL 𝕜 (trivialization_at E
    ((cont_mdiff_map.fst : C^∞⟮I.prod I', M × M'; I, M⟯) *ᵖ tangent_space I) x₀) x.1 =
    by apply trivialization.symmL 𝕜 (trivialization_at E (tangent_space I) x₀.1) x.1.1,
  { sorry },
  rw [this],
  refl,
end

@[simp, mfld_simps]
lemma trivialization_at_one_jet_bundle_source (x₀ : M × M') :
  (trivialization_at (E →L[𝕜] E') FJ¹MM' x₀).source =
  π FJ¹MM' ⁻¹' (prod.fst ⁻¹' (chart_at H x₀.1).source ∩ prod.snd ⁻¹' (chart_at H' x₀.2).source) :=
rfl

@[simp, mfld_simps]
lemma trivialization_at_one_jet_bundle_target (x₀ : M × M') :
  (trivialization_at (E →L[𝕜] E') FJ¹MM' x₀).target =
  (prod.fst ⁻¹' (trivialization_at E (tangent_space I) x₀.1).base_set ∩
  prod.snd ⁻¹' (trivialization_at E' (tangent_space I') x₀.2).base_set) ×ˢ set.univ :=
rfl

/-- Computing the value of a chart around `v` at point `v'` in `J¹(M, M')`.
  The last component equals the continuous linear map `v'.2`, composed on both sides by an
  appropriate coordinate change function. -/
lemma one_jet_bundle_chart_at {v v' : one_jet_bundle I M I' M'} :
  chart_at HJ v v' =
  ((chart_at H v.1.1 v'.1.1, chart_at H' v.1.2 v'.1.2),
  in_coordinates_core' (tangent_bundle_core I M) (tangent_bundle_core I' M')
    v.1.1 v'.1.1 v.1.2 v'.1.2 v'.2) :=
begin
  simp_rw [hom_chart, in_coordinates_core'],
  ext1,
  refl,
  dsimp only,
  sorry
  -- simp_rw [to_charted_space_chart_at],
  -- dsimp only [one_jet_bundle_core],
  -- simp_rw [hom_chart, in_coordinates', pullback_fst_coord_change_at,
  --   pullback_snd_coord_change_at, prod_charted_space_chart_at, local_homeomorph.prod_apply],
end

lemma one_jet_bundle_chart_source (x₀ : J¹MM') :
  (chart_at HJ x₀).source = sigma.fst ⁻¹' (chart_at (model_prod H H') x₀.proj).source :=
begin
  simp only [fiber_bundle.charted_space_chart_at] with mfld_simps,
  -- set ZZ' := (Z.hom Z').to_vector_bundle_core,
  sorry
end

lemma one_jet_bundle_chart_target (x₀ : J¹MM') :
  (chart_at HJ x₀).target =
  prod.fst ⁻¹' (chart_at (model_prod H H') x₀.proj).target :=
begin
  simp only [fiber_bundle.charted_space_chart_at,
    trivialization_at_one_jet_bundle_target] with mfld_simps,
  simp_rw [prod_univ, preimage_inter, preimage_preimage, inter_eq_left_iff_subset,
    subset_inter_iff],
  rw [← @preimage_preimage _ _ _ (λ x, (chart_at H x₀.proj.1).symm (prod.fst x))],
  rw [← @preimage_preimage _ _ _ (λ x, (chart_at H' x₀.proj.2).symm (prod.snd x))],
  refine ⟨preimage_mono _, preimage_mono _⟩,
  { rw [← @preimage_preimage _ _ _ (chart_at H x₀.proj.1).symm],
    refine (prod_subset_preimage_fst _ _).trans (preimage_mono _),
    exact (chart_at H x₀.proj.1).target_subset_preimage_source },
  { rw [← @preimage_preimage _ _ _ (chart_at H' x₀.proj.2).symm],
    refine (prod_subset_preimage_snd _ _).trans (preimage_mono _),
    exact (chart_at H' x₀.proj.2).target_subset_preimage_source }
end

-- /-- A variant of `one_jet_bundle_chart_at` in which the fact that the coordinate change actions
-- are equivalences is expressed at the type-theoretic level (i.e., `coord_change_equiv` instead of
-- `coord_change`). -/
-- lemma one_jet_bundle_chart_at' {v v' : J¹MM'} (hv' : v' ∈ (chart_at HJ v).source) :
--   chart_at HJ v v' =
--   ((chart_at H v.1.1 v'.1.1, chart_at H' v.1.2 v'.1.2),
--    ((tangent_bundle_core I' M').coord_change_equiv
--        (achart H' v'.1.2) (achart H' v.1.2) v'.1.2 : E' →L[𝕜] E').comp $
--    v'.2.comp $
--    ((tangent_bundle_core I M).coord_change_equiv
--        (achart H v.1.1) (achart H v'.1.1) v'.1.1 : E →L[𝕜] E)) :=
-- begin
--   have hx : v'.1.2 ∈ (achart H' v'.1.2 : local_homeomorph M' H').source ∩
--                      (achart H' v.1.2  : local_homeomorph M' H').source,
--   { simp only [to_charted_space_chart_at, chart_source] at hv',
--     simpa only [coe_achart, mem_inter_iff, mem_chart_source, true_and] using hv'.2, },
--   have hy : v'.1.1 ∈ (achart H  v.1.1  : local_homeomorph M H).source ∩
--                      (achart H  v'.1.1 : local_homeomorph M H).source,
--   { simp only [to_charted_space_chart_at, chart_source] at hv',
--     simpa only [coe_achart, mem_inter_iff, mem_chart_source, and_true] using hv'.1, },
--   simp only [one_jet_bundle_chart_at I M I' M', prod.mk.inj_iff, eq_self_iff_true, true_and],
--   ext e,
--   simp only [tangent_bundle_core_coord_change, achart_val, continuous_linear_map.coe_comp',
--     function.comp_app, continuous_linear_equiv.coe_coe, in_coordinates'],
--   erw [← (tangent_bundle_core I' M').coe_coord_change_equiv hx,
--        ← (tangent_bundle_core I M).coe_coord_change_equiv hy],
-- end

section maps

variables {M M'}

variables {I I' J J'}

lemma smooth_one_jet_bundle_proj :
  smooth ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) (I.prod I') (π FJ¹MM') :=
by apply smooth_proj _

lemma smooth.one_jet_bundle_proj {f : N → J¹MM'}
  (hf : smooth J ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) f) :
  smooth J (I.prod I') (λ x, (f x).1) :=
smooth_one_jet_bundle_proj.comp hf

lemma smooth_at.one_jet_bundle_proj {f : N → J¹MM'} {x₀ : N}
  (hf : smooth_at J ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) f x₀) :
  smooth_at J (I.prod I') (λ x, (f x).1) x₀ :=
(smooth_one_jet_bundle_proj _).comp x₀ hf

/-- The constructor of one_jet_bundle, in case `sigma.mk` will not give the right type. -/
@[simp] def one_jet_bundle.mk (x : M) (y : M') (f : one_jet_space I I' (x, y)) :
  J¹MM' :=
⟨(x, y), f⟩

@[simp, mfld_simps] lemma one_jet_bundle_mk_fst {x : M} {y : M'} {f : one_jet_space I I' (x, y)} :
  (one_jet_bundle.mk x y f).1 = (x, y) := rfl

@[simp, mfld_simps] lemma one_jet_bundle_mk_snd {x : M} {y : M'} {f : one_jet_space I I' (x, y)} :
  (one_jet_bundle.mk x y f).2 = f := rfl

lemma one_jet_bundle_trivialization_at' (x₀ x : J¹MM') :
  (trivialization_at (E →L[𝕜] E') (one_jet_space I I') x₀.proj x).2 =
  in_coordinates_core' (tangent_bundle_core I M) (tangent_bundle_core I' M')
    x₀.proj.1 x.proj.1 x₀.proj.2 x.proj.2 x.2 :=
begin
 simp_rw [trivialization_at_one_jet_bundle_apply], sorry
end

lemma one_jet_bundle_trivialization_at {f : N → J¹MM'} {x₀ : N} (x : N) :
  (trivialization_at (E →L[𝕜] E') (one_jet_space I I') (f x₀).proj (f x)).2 =
  in_coordinates_core I I' (λ x, (f x).proj.1) (λ x, (f x).proj.2) (λ x, (f x).2) x₀ x :=
by apply one_jet_bundle_trivialization_at'

lemma smooth_at_one_jet_bundle {f : N → J¹MM'} {x₀ : N} :
  smooth_at J ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) f x₀ ↔
  smooth_at J I (λ x, (f x).1.1) x₀ ∧ smooth_at J I' (λ x, (f x).1.2) x₀ ∧
  smooth_at J 𝓘(𝕜, E →L[𝕜] E') (in_coordinates_core I I' (λ x, (f x).1.1) (λ x, (f x).1.2)
    (λ x, (f x).2) x₀) x₀ :=
begin
  simp_rw [smooth_at, cont_mdiff_at_total_space, one_jet_bundle_trivialization_at],
  refine ⟨λ h, ⟨h.1.fst, h.1.snd, h.2⟩, λ h, ⟨_, h.2.2⟩⟩,
  convert h.1.prod_mk h.2.1,
  ext x; refl
end

lemma smooth_at_one_jet_bundle_mk {f : N → M} {g : N → M'} {ϕ : N → E →L[𝕜] E'} {x₀ : N} :
  smooth_at J ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E'))
    (λ x, one_jet_bundle.mk (f x) (g x) (ϕ x) : N → J¹MM') x₀ ↔
  smooth_at J I f x₀ ∧ smooth_at J I' g x₀ ∧
  smooth_at J 𝓘(𝕜, E →L[𝕜] E') (in_coordinates_core I I' f g ϕ x₀) x₀ :=
smooth_at_one_jet_bundle

lemma smooth_at.one_jet_bundle_mk {f : N → M} {g : N → M'} {ϕ : N → E →L[𝕜] E'} {x₀ : N}
  (hf : smooth_at J I f x₀) (hg : smooth_at J I' g x₀)
  (hϕ : smooth_at J 𝓘(𝕜, E →L[𝕜] E') (in_coordinates_core I I' f g ϕ x₀) x₀) :
  smooth_at J ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E'))
    (λ x, one_jet_bundle.mk (f x) (g x) (ϕ x) : N → J¹MM') x₀ :=
smooth_at_one_jet_bundle.mpr ⟨hf, hg, hϕ⟩

variables (I I')
/-- The one-jet extension of a function -/
def one_jet_ext (f : M → M') : M → one_jet_bundle I M I' M' :=
λ x, one_jet_bundle.mk x (f x) (mfderiv I I' f x)

variables {I I'}

lemma smooth_at.one_jet_ext {f : M → M'} {x : M} (hf : smooth_at I I' f x) :
  smooth_at I ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) (one_jet_ext I I' f) x :=
smooth_at_id.one_jet_bundle_mk hf (hf.mfderiv' le_rfl)

lemma smooth.one_jet_ext {f : M → M'} (hf : smooth I I' f) :
  smooth I ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) (one_jet_ext I I' f) :=
λ x, (hf x).smooth_at.one_jet_ext

lemma continuous_at.in_coordinates_comp {f : N → M} {g : N → M'} {h : N → N'}
  {ϕ' : N → E' →L[𝕜] F'} {ϕ : N → E →L[𝕜] E'} {x₀ : N}
  (hg : continuous_at g x₀) :
  in_coordinates_core I J' f h (λ x, ϕ' x ∘L ϕ x) x₀ =ᶠ[𝓝 x₀]
  λ x, in_coordinates_core I' J' g h ϕ' x₀ x ∘L in_coordinates_core I I' f g ϕ x₀ x :=
begin
  refine eventually_of_mem (hg.preimage_mem_nhds $
    (achart H' (g x₀)).1.open_source.mem_nhds $ mem_achart_source H' (g x₀)) (λ x hx, _),
  ext v,
  simp_rw [function.comp_apply, in_coordinates_core, in_coordinates_core',
    continuous_linear_map.comp_apply],
  rw [(tangent_bundle_core I' M').coord_change_comp_eq_self],
  exact ⟨mem_achart_source H' (g x), hx⟩
end

lemma smooth_at.clm_comp_in_coordinates_core {f : N → M} {g : N → M'} {h : N → N'}
  {ϕ' : N → E' →L[𝕜] F'} {ϕ : N → E →L[𝕜] E'} {n : N}
  (hg : continuous_at g n)
  (hϕ' : smooth_at J 𝓘(𝕜, E' →L[𝕜] F') (in_coordinates_core I' J' g h ϕ' n) n)
  (hϕ : smooth_at J 𝓘(𝕜, E →L[𝕜] E') (in_coordinates_core I I' f g ϕ n) n) :
  smooth_at J (𝓘(𝕜, E →L[𝕜] F')) (in_coordinates_core I J' f h (λ n, ϕ' n ∘L ϕ n) n) n :=
(hϕ'.clm_comp hϕ).congr_of_eventually_eq (hg.in_coordinates_comp)

variables (I')
lemma smooth_at.one_jet_comp {f1 : N' → M} (f2 : N' → M') {f3 : N' → N} {x₀ : N'}
  {h : ∀ x : N', one_jet_space I' J (f2 x, f3 x)} {g : ∀ x : N', one_jet_space I I' (f1 x, f2 x)}
  (hh : smooth_at J' ((I'.prod J).prod 𝓘(𝕜, E' →L[𝕜] F)) (λ x, one_jet_bundle.mk _ _ (h x)) x₀)
  (hg : smooth_at J' ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) (λ x, one_jet_bundle.mk _ _ (g x)) x₀) :
  smooth_at J' ((I.prod J).prod 𝓘(𝕜, E →L[𝕜] F))
    (λ x, one_jet_bundle.mk (f1 x) (f3 x) (h x ∘L g x) : N' → one_jet_bundle I M J N) x₀ :=
begin
  rw [smooth_at_one_jet_bundle_mk] at hh hg ⊢,
  exact ⟨hg.1, hh.2.1, hh.2.2.clm_comp_in_coordinates_core hg.2.1.continuous_at hg.2.2⟩
end

lemma smooth.one_jet_comp {f1 : N' → M} (f2 : N' → M') {f3 : N' → N}
  {h : ∀ x : N', one_jet_space I' J (f2 x, f3 x)} {g : ∀ x : N', one_jet_space I I' (f1 x, f2 x)}
  (hh : smooth J' ((I'.prod J).prod 𝓘(𝕜, E' →L[𝕜] F)) (λ x, one_jet_bundle.mk _ _ (h x)))
  (hg : smooth J' ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) (λ x, one_jet_bundle.mk _ _ (g x))) :
  smooth J' ((I.prod J).prod 𝓘(𝕜, E →L[𝕜] F))
    (λ x, one_jet_bundle.mk (f1 x) (f3 x) (h x ∘L g x) : N' → one_jet_bundle I M J N) :=
λ x₀, hh.smooth_at.one_jet_comp I' f2 (hg x₀)

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
  simp_rw [in_coordinates_core, in_coordinates_core', continuous_linear_map.add_comp,
    continuous_linear_map.comp_add],
  exact ⟨hϕ.1, hϕ.2.1, hϕ.2.2.add hϕ'.2.2⟩
end

variables (I' J')
/-- A useful definition to define maps between two one_jet_bundles. -/
protected def one_jet_bundle.map (f : M → N) (g : M' → N')
  (Dfinv : ∀ x : M, tangent_space J (f x) →L[𝕜] tangent_space I x) :
  one_jet_bundle I M I' M' → one_jet_bundle J N J' N' :=
λ p, one_jet_bundle.mk (f p.1.1) (g p.1.2) ((mfderiv I' J' g p.1.2 ∘L p.2) ∘L Dfinv p.1.1)
variables {I' J'}

lemma one_jet_bundle.map_map {f₂ : N → M₂} {f : M → N} {g₂ : N' → M₃} {g : M' → N'}
  {Dfinv : ∀ x : M, tangent_space J (f x) →L[𝕜] tangent_space I x}
  {Df₂inv : ∀ x : N, tangent_space I₂ (f₂ x) →L[𝕜] tangent_space J x}
  {x : J¹MM'}
  (hg₂ : mdifferentiable_at J' I₃ g₂ (g x.1.2)) (hg : mdifferentiable_at I' J' g x.1.2) :
  one_jet_bundle.map J' I₃ f₂ g₂ Df₂inv (one_jet_bundle.map I' J' f g Dfinv x) =
  one_jet_bundle.map I' I₃ (f₂ ∘ f) (g₂ ∘ g) (λ x, Dfinv x ∘L Df₂inv (f x)) x :=
begin
  ext _, { refl }, { refl },
  dsimp only [one_jet_bundle.map, one_jet_bundle.mk],
  simp_rw [← continuous_linear_map.comp_assoc, mfderiv_comp x.1.2 hg₂ hg]
end

lemma one_jet_bundle.map_id (x : J¹MM') :
  one_jet_bundle.map I' I' id id (λ x, continuous_linear_map.id 𝕜 (tangent_space I x)) x = x :=
begin
  ext _, { refl }, { refl },
  dsimp only [one_jet_bundle.map, one_jet_bundle.mk],
  simp_rw [mfderiv_id],
  -- note: rw fails since we have to unfold the type `bundle.pullback`
  erw [continuous_linear_map.id_comp],
end

lemma smooth_at.one_jet_bundle_map {f : M'' → M → N} {g : M'' → M' → N'} {x₀ : M''}
  {Dfinv : ∀ (z : M'') (x : M), tangent_space J (f z x) →L[𝕜] tangent_space I x}
  {k : M'' → J¹MM'}
  (hf : smooth_at (I''.prod I) J f.uncurry (x₀, (k x₀).1.1))
  (hg : smooth_at (I''.prod I') J' g.uncurry (x₀, (k x₀).1.2))
  (hDfinv : smooth_at I'' 𝓘(𝕜, F →L[𝕜] E)
    (in_coordinates_core J I (λ x, f x (k x).1.1) (λ x, (k x).1.1) (λ x, Dfinv x (k x).1.1) x₀) x₀)
  (hk : smooth_at I'' ((I.prod I').prod (𝓘(𝕜, E →L[𝕜] E'))) k x₀) :
  smooth_at I'' ((J.prod J').prod (𝓘(𝕜, F →L[𝕜] F')))
    (λ z, one_jet_bundle.map I' J' (f z) (g z) (Dfinv z) (k z)) x₀ :=
begin
  rw [smooth_at_one_jet_bundle] at hk,
  refine smooth_at.one_jet_comp _ _ _ _,
  refine smooth_at.one_jet_comp _ _ _ _,
  { refine hk.2.1.one_jet_bundle_mk (hg.comp x₀ (smooth_at_id.prod_mk hk.2.1)) _,
    exact cont_mdiff_at.mfderiv''' g (λ x, (k x).1.2) hg hk.2.1 le_rfl },
  { exact hk.1.one_jet_bundle_mk hk.2.1 hk.2.2 },
  exact (hf.comp x₀ (smooth_at_id.prod_mk hk.1)).one_jet_bundle_mk hk.1 hDfinv,
end

/-- A useful definition to define maps between two one_jet_bundles. -/
def map_left (f : M → N) (Dfinv : ∀ x : M, tangent_space J (f x) →L[𝕜] tangent_space I x) :
  J¹MM' → one_jet_bundle J N I' M' :=
λ p, one_jet_bundle.mk (f p.1.1) p.1.2 (p.2 ∘L Dfinv p.1.1)

lemma map_left_eq_map (f : M → N) (Dfinv : ∀ x : M, tangent_space J (f x) →L[𝕜] tangent_space I x) :
  map_left f Dfinv = one_jet_bundle.map I' I' f (id : M' → M') Dfinv :=
by { ext x, refl, refl, dsimp only [one_jet_bundle.map, map_left, one_jet_bundle_mk_snd],
  simp_rw [mfderiv_id, continuous_linear_map.id_comp] }

lemma smooth_at.map_left {f : N' → M → N} {x₀ : N'}
  {Dfinv : ∀ (z : N') (x : M), tangent_space J (f z x) →L[𝕜] tangent_space I x}
  {g : N' → J¹MM'}
  (hf : smooth_at (J'.prod I) J f.uncurry (x₀, (g x₀).1.1))
  (hDfinv : smooth_at J' 𝓘(𝕜, F →L[𝕜] E)
    (in_coordinates_core J I (λ x, f x (g x).1.1) (λ x, (g x).1.1) (λ x, Dfinv x (g x).1.1) x₀) x₀)
  (hg : smooth_at J' ((I.prod I').prod (𝓘(𝕜, E →L[𝕜] E'))) g x₀) :
  smooth_at J' ((J.prod I').prod (𝓘(𝕜, F →L[𝕜] E'))) (λ z, map_left (f z) (Dfinv z) (g z)) x₀ :=
by { simp_rw [map_left_eq_map], exact hf.one_jet_bundle_map smooth_at_snd hDfinv hg }

/-- The projection `J¹(E × P, F) → J¹(E, F)`. Not actually used. -/
def bundle_fst : one_jet_bundle (J.prod I) (N × M) I' M' → one_jet_bundle J N I' M' :=
map_left prod.fst $ λ x, continuous_linear_map.inl 𝕜 F E

/-- The projection `J¹(P × E, F) → J¹(E, F)`. -/
def bundle_snd : one_jet_bundle (J.prod I) (N × M) I' M' → J¹MM' :=
map_left prod.snd $ λ x, mfderiv I (J.prod I) (λ y, (x.1, y)) x.2

lemma bundle_snd_eq (x : one_jet_bundle (J.prod I) (N × M) I' M') :
  bundle_snd x = map_left prod.snd (λ x, continuous_linear_map.inr 𝕜 F E) x :=
by simp_rw [bundle_snd, mfderiv_prod_right]

lemma smooth_bundle_snd :
  smooth (((J.prod I).prod I').prod 𝓘(𝕜, F × E →L[𝕜] E')) ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E'))
    (bundle_snd : one_jet_bundle (J.prod I) (N × M) I' M' → J¹MM') :=
begin
  intro x₀,
  refine smooth_at.map_left _ _ smooth_at_id,
  { exact smooth_at_snd.snd },
  apply cont_mdiff_at.mfderiv'''
    (λ (x : one_jet_bundle (J.prod I) (N × M) I' M') (y : M), (x.1.1.1, y))
    (λ (x : one_jet_bundle (J.prod I) (N × M) I' M'), x.1.1.2) _ _ le_top,
  { apply_instance },
  { exact (smooth_one_jet_bundle_proj.fst.fst.prod_map smooth_id).smooth_at }, -- slow
  { exact smooth_one_jet_bundle_proj.fst.snd.smooth_at }, -- slow
end

end maps

-- move
lemma local_equiv_eq_equiv {α β} {f : local_equiv α β} {e : α ≃ β}
  (h1 : ∀ x, f x = e x) (h2 : f.source = univ) (h3 : f.target = univ) : f = e.to_local_equiv :=
begin
  refine local_equiv.ext h1 (λ y, _) h2,
  conv_rhs { rw [← f.right_inv ((set.ext_iff.mp h3 y).mpr (mem_univ y)), h1] },
  exact (e.left_inv _).symm
end

local notation `𝓜` := model_prod (model_prod H H') (E →L[𝕜] E')
/-- In the one_jet bundle to the model space, the charts are just the canonical identification
between a product type and a sigma type, a.k.a. `sigma_equiv_prod`. -/
@[simp, mfld_simps] lemma one_jet_bundle_model_space_chart_at (p : one_jet_bundle I H I' H') :
  (chart_at 𝓜 p).to_local_equiv = (sigma_equiv_prod (H × H') (E →L[𝕜] E')).to_local_equiv :=
begin
  apply local_equiv_eq_equiv,
  { intros x,
    rw [local_homeomorph.coe_coe, one_jet_bundle_chart_at I H I' H',
      in_coordinates_core'_tangent_bundle_core_model_space],
    ext; refl },
  { simp_rw [one_jet_bundle_chart_source, prod_charted_space_chart_at, chart_at_self_eq,
      local_homeomorph.refl_prod_refl],
    refl },
  { simp_rw [one_jet_bundle_chart_target, prod_charted_space_chart_at, chart_at_self_eq,
      local_homeomorph.refl_prod_refl],
    refl },
end

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
-- note: this proof works for all vector bundles where we have proven
-- `∀ p, chart_at _ p = f.to_local_equiv`
def one_jet_bundle_model_space_homeomorph : one_jet_bundle I H I' H' ≃ₜ 𝓜 :=
{ continuous_to_fun :=
  begin
    let p : one_jet_bundle I H I' H' := ⟨(I.symm (0 : E), I'.symm (0 : E')), 0⟩,
    have : continuous (chart_at 𝓜 p),
    { rw continuous_iff_continuous_on_univ,
      convert local_homeomorph.continuous_on _,
      simp only with mfld_simps },
    simpa only with mfld_simps using this,
  end,
  continuous_inv_fun :=
  begin
    let p : one_jet_bundle I H I' H' := ⟨(I.symm (0 : E), I'.symm (0 : E')), 0⟩,
    have : continuous (chart_at 𝓜 p).symm,
    { rw continuous_iff_continuous_on_univ,
      convert local_homeomorph.continuous_on _,
      simp only with mfld_simps },
    simpa only with mfld_simps using this,
  end,
  .. sigma_equiv_prod (H × H') (E →L[𝕜] E') }

-- unused
@[simp, mfld_simps] lemma one_jet_bundle_model_space_homeomorph_coe :
  (one_jet_bundle_model_space_homeomorph H I H' I' : one_jet_bundle I H I' H' → 𝓜) =
  sigma_equiv_prod (H × H') (E →L[𝕜] E') :=
rfl

-- unused
@[simp, mfld_simps] lemma one_jet_bundle_model_space_homeomorph_coe_symm :
  ((one_jet_bundle_model_space_homeomorph H I H' I').symm : 𝓜 → one_jet_bundle I H I' H') =
  (sigma_equiv_prod (H × H') (E →L[𝕜] E')).symm :=
rfl
