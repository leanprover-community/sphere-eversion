/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import topology.vector_bundle.basic
import to_mathlib.geometry.manifold.fiber_bundle
import to_mathlib.geometry.manifold.cont_mdiff

/-!
# Smooth vector bundles

In this file we define smooth vector bundles.

-/

noncomputable theory

open bundle set
open_locale classical manifold

variables {𝕜 : Type*} {B V V' V'' H H' H'' : Type*}

variables [nondiscrete_normed_field 𝕜]
variables [normed_group V] [normed_space 𝕜 V] [normed_group V'] [normed_space 𝕜 V']
variables [normed_group V''] [normed_space 𝕜 V'']
variables [topological_space H] [topological_space H'] [topological_space H'']
variables (I : model_with_corners 𝕜 V H) (I' : model_with_corners 𝕜 V' H')
variables (I'' : model_with_corners 𝕜 V'' H'')
variables (F F' : Type*) (E E' : B → Type*)
variables [∀ x, normed_group (E x)] [∀ x, normed_space 𝕜 (E x)]
variables [∀ x, normed_group (E' x)] [∀ x, normed_space 𝕜 (E' x)]
variables [normed_group F] [normed_space 𝕜 F]
variables [normed_group F'] [normed_space 𝕜 F']
variables [topological_space B] [charted_space H B] -- [smooth_manifold_with_corners I B]

variables [topological_space (total_space E)] [charted_space H' (total_space E)]
variables [topological_space (total_space E')] [charted_space H'' (total_space E')]
-- variables [smooth_manifold_with_corners I' (total_space E)]

/-- Local trivialization for smooth vector bundles. -/
@[ext, nolint has_inhabited_instance]
structure smooth_vector_bundle.trivialization extends to_fiber_bundle :
  smooth_fiber_bundle.trivialization I 𝓘(𝕜, F) I' F (@total_space.proj B E) :=
(linear' : ∀ x ∈ base_set, is_linear_map 𝕜 (λ y : E x, (to_fun y).2))

open smooth_vector_bundle

namespace smooth_vector_bundle.trivialization

variables {𝕜 I I' F E} (e : trivialization I I' F E) {x : total_space E} {b : B} {y : E b}

/-- Natural identification as a `trivialization` of a topological vector bundle. -/
def to_topological : topological_vector_bundle.trivialization 𝕜 F E :=
{ ..e.to_fiber_bundle.to_topological, ..e }

def to_topological_injective : function.injective (λ e : trivialization I I' F E, e.to_topological) :=
by { intros e e', rw [trivialization.ext_iff,
  ← smooth_fiber_bundle.trivialization.to_topological_injective.eq_iff,
  topological_vector_bundle.trivialization.ext_iff], exact id }

/-- The local homeomorph defined by the trivialization. -/
def to_local_homeomorph : local_homeomorph (total_space E) (B × F) :=
e.to_topological.to_local_homeomorph

instance : has_coe_to_fun (trivialization I I' F E) (λ _, total_space E → B × F) := ⟨λ e, e.to_fun⟩

instance : has_coe (trivialization I I' F E) (topological_vector_bundle.trivialization 𝕜 F E) :=
⟨smooth_vector_bundle.trivialization.to_topological⟩

instance : has_coe (trivialization I I' F E)
  (smooth_fiber_bundle.trivialization I 𝓘(𝕜, F) I' F (@total_space.proj B E)) :=
⟨smooth_vector_bundle.trivialization.to_fiber_bundle⟩

-- protected lemma linear : ∀ x ∈ e.base_set, is_linear_map 𝕜 (λ y : (E x), (e y).2) := e.linear'
protected lemma smooth_on : smooth_on I' (I.prod 𝓘(𝕜, F)) e e.source :=
e.to_fiber_bundle.smooth_on

protected lemma smooth_on_symm' :
  smooth_on (I.prod 𝓘(𝕜, F)) I' e.to_local_homeomorph.symm e.target :=
e.smooth_on_inv_fun

@[simp, mfld_simps] lemma coe_coe : ⇑e.to_local_equiv = e := rfl
@[simp, mfld_simps] lemma coe_fst (ex : x ∈ e.source) : (e x).1 = x.proj := e.proj_to_fun x ex
lemma mem_source : x ∈ e.source ↔ x.proj ∈ e.base_set := by rw [e.source_eq, mem_preimage]
lemma coe_mem_source : ↑y ∈ e.source ↔ b ∈ e.base_set := e.mem_source
lemma coe_fst' (ex : x.proj ∈ e.base_set) : (e x).1 = x.proj :=
e.coe_fst (e.mem_source.2 ex)

protected lemma eq_on : eq_on (prod.fst ∘ e) total_space.proj e.source := λ x hx, e.coe_fst hx
lemma mk_proj_snd (ex : x ∈ e.source) : (x.proj, (e x).2) = e x :=
prod.ext (e.coe_fst ex).symm rfl
lemma mk_proj_snd' (ex : x.proj ∈ e.base_set) : (x.proj, (e x).2) = e x :=
prod.ext (e.coe_fst' ex).symm rfl

lemma open_target : is_open e.target :=
by { rw e.target_eq, exact e.open_base_set.prod is_open_univ }

@[simp, mfld_simps] lemma coe_coe_fst (hb : b ∈ e.base_set) : (e y).1 = b :=
e.coe_fst (e.mem_source.2 hb)

lemma source_inter_preimage_target_inter (s : set (B × F)) :
  e.source ∩ (e ⁻¹' (e.target ∩ s)) = e.source ∩ (e ⁻¹' s) :=
e.to_local_homeomorph.source_inter_preimage_target_inter s

lemma mem_target {x : B × F} : x ∈ e.target ↔ x.1 ∈ e.base_set :=
e.to_topological.mem_target

lemma mk_mem_target {y : F} : (b, y) ∈ e.target ↔ b ∈ e.base_set :=
e.to_topological.mem_target

lemma map_target {x : B × F} (hx : x ∈ e.target) : e.to_local_homeomorph.symm x ∈ e.source :=
e.to_local_homeomorph.map_target hx

lemma proj_symm_apply {x : B × F} (hx : x ∈ e.target) :
  (e.to_local_homeomorph.symm x).proj = x.1 :=
e.to_topological.proj_symm_apply hx

lemma proj_symm_apply' {b : B} {x : F} (hx : b ∈ e.base_set) :
  (e.to_local_homeomorph.symm (b, x)).proj  = b :=
e.to_topological.proj_symm_apply' hx

lemma apply_symm_apply {x : B × F} (hx : x ∈ e.target) : e (e.to_local_homeomorph.symm x) = x :=
e.to_local_homeomorph.right_inv hx

lemma apply_symm_apply' {b : B} {x : F} (hx : b ∈ e.base_set) :
  e (e.to_local_homeomorph.symm (b, x)) = (b, x) :=
e.to_topological.apply_symm_apply' hx

lemma symm_apply_apply {x : total_space E} (hx : x ∈ e.source) :
  e.to_local_homeomorph.symm (e x) = x :=
e.to_local_equiv.left_inv hx

@[simp, mfld_simps] lemma symm_coe_proj {x : B} {y : F} (h : x ∈ e.base_set) :
  (e.to_local_homeomorph.symm (x, y)).1 = x := e.proj_symm_apply' h

/-- A fiberwise inverse to `e`. The function `F → E x` that induces a local inverse
  `B × F → total_space E` of `e` on `e.base_set`. It is defined to be `0` outside `e.base_set`. -/
protected def symm (e : trivialization I I' F E) (b : B) (y : F) : E b :=
e.to_topological.symm b y

lemma symm_apply (e : trivialization I I' F E) {b : B} (hb : b ∈ e.base_set) (y : F) :
  e.symm b y = cast (congr_arg E (e.symm_coe_proj hb)) (e.to_local_homeomorph.symm (b, y)).2 :=
dif_pos hb

lemma symm_apply_of_not_mem (e : trivialization I I' F E) {b : B} (hb : b ∉ e.base_set) (y : F) :
  e.symm b y = 0 :=
dif_neg hb

lemma mk_symm (e : trivialization I I' F E) {b : B} (hb : b ∈ e.base_set) (y : F) :
  total_space_mk b (e.symm b y) = e.to_local_homeomorph.symm (b, y) :=
e.to_topological.mk_symm hb y

lemma symm_proj_apply (e : trivialization I I' F E) (z : total_space E)
  (hz : z.proj ∈ e.base_set) : e.symm z.proj (e z).2 = z.2 :=
e.to_topological.symm_proj_apply z hz

lemma symm_apply_apply_mk (e : trivialization I I' F E) {b : B} (hb : b ∈ e.base_set) (y : E b) :
  e.symm b (e (total_space_mk b y)).2 = y :=
e.symm_proj_apply (total_space_mk b y) hb

lemma apply_mk_symm (e : trivialization I I' F E) {b : B} (hb : b ∈ e.base_set) (y : F) :
  e (total_space_mk b (e.symm b y)) = (b, y) :=
e.to_topological.apply_mk_symm hb y

lemma smooth_on_symm (e : trivialization I I' F E) :
  smooth_on (I.prod 𝓘(𝕜, F)) I' (λ z : B × F, total_space_mk z.1 (e.symm z.1 z.2))
    (e.base_set ×ˢ (univ : set F)) :=
begin
  have : ∀ (z : B × F) (hz : z ∈ e.base_set ×ˢ (univ : set F)),
    total_space_mk z.1 (e.symm z.1 z.2) = e.to_local_homeomorph.symm z,
  { rintro x ⟨hx : x.1 ∈ e.base_set, _⟩, simp_rw [e.mk_symm hx, prod.mk.eta] },
  refine cont_mdiff_on.congr _ this,
  rw [← e.target_eq],
  exact e.smooth_on_symm'
end

/-- A coordinate change function between two trivializations, as a continuous linear equivalence.
  Defined to be the identity when `b` does not lie in the base set of both trivializations. -/
def coord_change (e e' : trivialization I I' F E) (b : B) : F ≃L[𝕜] F :=
e.to_topological.coord_change e'.to_topological b

lemma coord_change_apply (e e' : trivialization I I' F E) {b : B}
  (hb : b ∈ e.base_set ∩ e'.base_set) (y : F) :
  coord_change e e' b y = (e' (total_space_mk b (e.symm b y))).2 :=
congr_arg (λ f, linear_equiv.to_fun f y) (dif_pos hb)

lemma mk_coord_change (e e' : trivialization I I' F E) {b : B}
  (hb : b ∈ e.base_set ∩ e'.base_set) (y : F) :
  (b, coord_change e e' b y) = e' (total_space_mk b (e.symm b y)) :=
begin
  ext,
  { rw [e.mk_symm hb.1 y, e'.coe_fst', e.proj_symm_apply' hb.1],
    rw [e.proj_symm_apply' hb.1], exact hb.2 },
  { exact e.coord_change_apply e' hb y }
end

/-- A version of `coord_change_apply` that fully unfolds `coord_change`. The right-hand side is
ugly, but has good definitional properties for specifically defined trivializations. -/
lemma coord_change_apply' (e e' : trivialization I I' F E) {b : B}
  (hb : b ∈ e.base_set ∩ e'.base_set) (y : F) :
  coord_change e e' b y = (e' (e.to_local_homeomorph.symm (b, y))).2 :=
by rw [e.coord_change_apply e' hb, e.mk_symm hb.1]

end smooth_vector_bundle.trivialization

open smooth_vector_bundle

/-- The space `total_space E` (for `E : B → Type*` such that each `E x` is a topological vector
space) has a topological vector space structure with fiber `F` (denoted with
`smooth_vector_bundle 𝕜 F E`) if around every point there is a fiber bundle trivialization
which is linear in the fibers. -/
class smooth_vector_bundle :=
-- does this also need to induce the manifold structure? I don't see a condition like that in Serge Lang's book?
(total_space_mk_inducing [] : ∀ (b : B), inducing (@total_space_mk B E b))
(trivialization_atlas [] : set (trivialization I I' F E))
(trivialization_at [] : B → trivialization I I' F E)
(mem_base_set_trivialization_at [] : ∀ b : B, b ∈ (trivialization_at b).base_set)
(trivialization_mem_atlas [] : ∀ b : B, trivialization_at b ∈ trivialization_atlas)
(smooth_on_coord_change [] : ∀ (e e' ∈ trivialization_atlas), smooth_on I 𝓘(𝕜, F →L[𝕜] F)
  (λ b, trivialization.coord_change e e' b : B → F →L[𝕜] F) (e.base_set ∩ e'.base_set))
-- (coe_trivialization : _ '' trivialization_atlas = atlas H' (total_space E))
-- maybe there should be a equiv (or map) H × F ≃ H' which we can use to formulate coe_trivialization?

export smooth_vector_bundle (trivialization_atlas trivialization_at
  mem_base_set_trivialization_at trivialization_mem_atlas smooth_on_coord_change)

variable [smooth_vector_bundle I I' F E]

namespace smooth_vector_bundle

@[simp, mfld_simps] lemma mem_source_trivialization_at (z : total_space E) :
  z ∈ (trivialization_at I I' F E z.1).source :=
by { rw smooth_fiber_bundle.trivialization.mem_source, apply mem_base_set_trivialization_at }

variables {𝕜 I I' F E}

@[priority 10, nolint dangerous_instance]
-- probably not terrible as an instance: I and I' become metavariables
instance to_topological : topological_vector_bundle 𝕜 F E :=
{ total_space_mk_inducing := total_space_mk_inducing I I' F E,
  trivialization_atlas := trivialization.to_topological '' trivialization_atlas I I' F E,
  trivialization_at := λ b, (trivialization_at I I' F E b).to_topological,
  mem_base_set_trivialization_at := mem_base_set_trivialization_at I I' F E,
  trivialization_mem_atlas := λ b, mem_image_of_mem _ (trivialization_mem_atlas I I' F E b),
  continuous_on_coord_change := by { rintro _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩,
    exact (smooth_on_coord_change e he e' he').continuous_on } }

@[simp] lemma to_topological_mem_trivialization_atlas {e₁ : trivialization I I' F E} :
  e₁.to_topological ∈ topological_vector_bundle.trivialization_atlas 𝕜 F E ↔
  e₁ ∈ trivialization_atlas I I' F E :=
trivialization.to_topological_injective.mem_set_image

-- include I' F E
-- this is tricky: we need an assumption that the atlas on B gives the trivializations
-- def to_basic_smooth_vector_bundle_core [smooth_manifold_with_corners I B] :
--   basic_smooth_vector_bundle_core I B F :=
-- { coord_change := λ e e' x, _,
--   coord_change_self := _,
--   coord_change_comp := _,
--   coord_change_smooth_clm := _ }
-- omit I' F E

section trivial

instance {B : Type*} {F : Type*} [normed_group F] (b : B) :
  normed_group (bundle.trivial B F b) := ‹normed_group F›

instance {B : Type*} {F : Type*} [normed_group F] [normed_space 𝕜 F] (b : B) :
  normed_space 𝕜 (bundle.trivial B F b) := ‹normed_space 𝕜 F›

-- instance charted_space_total_space_trivial :
--   charted_space (model_prod H F) (total_space (trivial B F)) :=
-- sorry

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

-- end trivial_smooth_vector_bundle

end trivial

variables (I I' B F)
/- Not registered as an instance because of a metavariable. -/
lemma is_smooth_fiber_bundle_proj :
  is_smooth_fiber_bundle I 𝓘(𝕜, F) I' F (@total_space.proj B E) :=
λ x, ⟨(trivialization_at I I' F E x).to_fiber_bundle, mem_base_set_trivialization_at I I' F E x⟩


variables {I I' B F}

include 𝕜 F

-- lemma smooth_total_space_mk (x : B) : smooth 𝓘(𝕜, E x) I' (@total_space_mk B E x) :=
-- sorry

variables (𝕜 B F)

lemma smooth_proj : smooth I' I (@total_space.proj B E) :=
is_smooth_fiber_bundle.smooth_proj (is_smooth_fiber_bundle_proj B I I' F)

end smooth_vector_bundle

namespace basic_smooth_vector_bundle_core

variables {F I} [smooth_manifold_with_corners I B] (Z : basic_smooth_vector_bundle_core I B F)

instance normed_group_fiber (x : B) : normed_group (Z.to_topological_vector_bundle_core.fiber x) :=
by delta_instance topological_vector_bundle_core.fiber
instance normed_space_fiber (x : B) :
  normed_space 𝕜 (Z.to_topological_vector_bundle_core.fiber x) :=
by delta_instance topological_vector_bundle_core.fiber

/-- The `smooth_fiber_bundle_core` constructed from a `basic_smooth_vector_bundle_core`. -/
def to_smooth_fiber_bundle_core : smooth_fiber_bundle_core I 𝓘(𝕜, F) B F :=
{ coord_change := λ i j x, Z.coord_change i j (i.1 x),
  smooth_on_coord_change := begin
    intros i j,
    have := Z.coord_change_smooth_clm i j,
    rw [smooth_on_iff_of_subset_source],
    swap, refine (smooth_manifold_with_corners.subset_maximal_atlas $ mem_image2_of_mem i.2 $
      charted_space_self_atlas.mpr rfl),
    swap, exact structure_groupoid.id_mem_maximal_atlas _,
    swap, exact prod_mono (inter_subset_left _ _) subset.rfl,
    swap, exact subset_univ _,
    refine ⟨Z.to_topological_vector_bundle_core.to_topological_fiber_bundle_core
      .coord_change_continuous i j, _⟩,
    simp only [local_homeomorph.extend, local_homeomorph.refl_local_equiv, model_with_corners_self_local_equiv,
  local_equiv.refl_trans, local_equiv.refl_coe, local_homeomorph.prod_to_local_equiv,
  model_with_corners_prod_to_local_equiv, local_equiv.prod_trans, local_equiv.prod_symm, local_equiv.refl_symm,
  local_equiv.prod_coe, local_equiv.coe_trans_symm, local_homeomorph.coe_coe_symm,
  model_with_corners.to_local_equiv_coe_symm, function.comp_app, id.def, function.comp.left_id, local_equiv.prod_target,
  local_equiv.trans_target, model_with_corners.target_eq, local_equiv.refl_target, local_equiv.refl_source,
  preimage_univ, inter_univ, function.comp],
  sorry -- this is an uncurried version of the lemma below
  end,
  ..Z.to_topological_vector_bundle_core }

/-- Extended version of the local trivialization of a smooth vector bundle constructed from core,
registering additionally in its type that it is a smooth local bundle trivialization. -/
def local_triv (i : atlas H B) :
  trivialization I (I.prod 𝓘(𝕜, F)) F Z.to_topological_vector_bundle_core.fiber :=
{ .. Z.to_topological_vector_bundle_core.local_triv i,
  .. Z.to_smooth_fiber_bundle_core.local_triv i }


/-- Preferred local trivialization of a smooth vector bundle constructed from core,
  at a given point, as a bundle trivialization -/
def local_triv_at (b : B) :
  trivialization I (I.prod 𝓘(𝕜, F)) F Z.to_topological_vector_bundle_core.fiber :=
Z.local_triv ⟨chart_at H b, chart_mem_atlas H b⟩

lemma local_triv_coord_change_eq {x : H} (i j : atlas H B)
  (hx : x ∈ i.1.target ∩ i.1.symm ⁻¹' j.1.source)
  (v : F) : (Z.local_triv i).coord_change (Z.local_triv j) (i.1.symm x) v =
  Z.coord_change i j x v :=
begin
  refine (Z.to_topological_vector_bundle_core.local_triv_coord_change_eq i j
    ⟨i.1.symm.maps_to hx.1, hx.2⟩ v).trans _,
  simp_rw [basic_smooth_vector_bundle_core.to_topological_vector_bundle_core,
    local_homeomorph.right_inv i.1 hx.1]
end

instance to_smooth_vector_bundle :
  smooth_vector_bundle I (I.prod 𝓘(𝕜, F)) F Z.to_topological_vector_bundle_core.fiber :=
{ trivialization_atlas := range Z.local_triv,
  trivialization_at := Z.local_triv_at,
  trivialization_mem_atlas := λ b, mem_range_self _,
  smooth_on_coord_change := begin -- todo: cleanup
    rintros _ ⟨i, rfl⟩ _ ⟨i', rfl⟩,
    have := Z.coord_change_smooth_clm i i',
    rw [smooth_on_iff_of_subset_source (smooth_manifold_with_corners.subset_maximal_atlas i.2)],
    swap, exact structure_groupoid.id_mem_maximal_atlas _,
    swap, { exact inter_subset_left _ _ },
    swap, { refine subset_univ _ },
    all_goals { try {apply_instance}},
    refine ⟨continuous_on_coord_change (Z.to_topological_vector_bundle_core.local_triv i)
      ⟨i, rfl⟩ (Z.to_topological_vector_bundle_core.local_triv i') ⟨i', rfl⟩, _⟩,
    simp only [local_homeomorph.extend, local_homeomorph.refl_local_equiv, model_with_corners_self_local_equiv,
  local_equiv.refl_trans, local_equiv.refl_coe, local_equiv.coe_trans_symm,
  local_homeomorph.coe_coe_symm, model_with_corners.to_local_equiv_coe_symm, function.comp.left_id,
  local_equiv.trans_target, model_with_corners.target_eq, local_equiv.refl_source, preimage_univ, inter_univ,
  preimage_inter],
    refine (this.congr _).mono _,
    { rintro _ ⟨x, hx, rfl⟩,
      ext y,
      simp only [function.comp_app, model_with_corners.left_inv, continuous_linear_equiv.coe_coe],
      rw [local_triv_coord_change_eq],
      rw [← local_equiv.symm_source],
      exact hx },
    simp only [local_homeomorph.trans_to_local_equiv, local_homeomorph.symm_to_local_equiv,
  local_equiv.trans_source, local_equiv.symm_source, local_homeomorph.coe_coe_symm],
    rw [model_with_corners.image_eq, inter_comm _ (range I), preimage_inter, ← preimage_comp,
      ← inter_assoc (range I)],
    exact inter_subset_inter subset.rfl (inter_subset_right _ _),
  end,
  ..topological_vector_bundle_core.fiber.topological_vector_bundle
    Z.to_topological_vector_bundle_core }

instance normed_group_tangent_space (x : B) : normed_group (tangent_space I x) :=
by delta_instance tangent_space
instance normed_space_tangent_space (x : B) : normed_space 𝕜 (tangent_space I x) :=
by delta_instance tangent_space

instance smooth_tangent_bundle :
  smooth_vector_bundle I (I.prod 𝓘(𝕜, V)) V (tangent_space I : B → Type*) :=
(tangent_bundle_core I B).to_smooth_vector_bundle

end basic_smooth_vector_bundle_core

/-! ### Smooth vector prebundle -/

section

open smooth_vector_bundle topological_vector_bundle (pretrivialization)
/-- Smooth version of `topological_vector_prebundle` -/
@[nolint has_inhabited_instance]
structure smooth_vector_prebundle :=
(pretrivialization_atlas : set (pretrivialization 𝕜 F E))
(pretrivialization_at : B → pretrivialization 𝕜 F E)
(mem_base_pretrivialization_at : ∀ x : B, x ∈ (pretrivialization_at x).base_set)
(pretrivialization_mem_atlas : ∀ x : B, pretrivialization_at x ∈ pretrivialization_atlas)
(exists_coord_change : ∀ (e e' ∈ pretrivialization_atlas), ∃ f : B → F →L[𝕜] F,
  smooth_on I 𝓘(𝕜, F →L[𝕜] F) f (e.base_set ∩ e'.base_set) ∧
  ∀ (b : B) (hb : b ∈ e.base_set ∩ e'.base_set) (v : F),
    f b v = (e' (total_space_mk b (e.symm b v))).2)

namespace smooth_vector_prebundle

variables {I E F}

/-- A randomly chosen coordinate change on a `smooth_vector_prebundle`, given by
  the field `exists_coord_change`. -/
def coord_change (a : smooth_vector_prebundle I F E)
  {e e' : pretrivialization 𝕜 F E} (he : e ∈ a.pretrivialization_atlas)
  (he' : e' ∈ a.pretrivialization_atlas) (b : B) : F →L[𝕜] F :=
classical.some (a.exists_coord_change e he e' he') b

lemma smooth_on_coord_change (a : smooth_vector_prebundle I F E)
  {e e' : pretrivialization 𝕜 F E} (he : e ∈ a.pretrivialization_atlas)
  (he' : e' ∈ a.pretrivialization_atlas) :
  smooth_on I 𝓘(𝕜, F →L[𝕜] F) (a.coord_change he he') (e.base_set ∩ e'.base_set) :=
(classical.some_spec (a.exists_coord_change e he e' he')).1

lemma coord_change_apply (a : smooth_vector_prebundle I F E)
  {e e' : pretrivialization 𝕜 F E} (he : e ∈ a.pretrivialization_atlas)
  (he' : e' ∈ a.pretrivialization_atlas) {b : B} (hb : b ∈ e.base_set ∩ e'.base_set) (v : F) :
  a.coord_change he he' b v = (e' (total_space_mk b (e.symm b v))).2 :=
(classical.some_spec (a.exists_coord_change e he e' he')).2 b hb v

lemma mk_coord_change (a : smooth_vector_prebundle I F E)
  {e e' : pretrivialization 𝕜 F E} (he : e ∈ a.pretrivialization_atlas)
  (he' : e' ∈ a.pretrivialization_atlas) {b : B} (hb : b ∈ e.base_set ∩ e'.base_set) (v : F) :
  (b, a.coord_change he he' b v) = e' (total_space_mk b (e.symm b v)) :=
begin
  ext,
  { rw [e.mk_symm hb.1 v, e'.coe_fst', e.proj_symm_apply' hb.1],
    rw [e.proj_symm_apply' hb.1], exact hb.2 },
  { exact a.coord_change_apply he he' hb v }
end

/-- Natural identification of `smooth_vector_prebundle` as a `smooth_fiber_prebundle`. -/
def to_smooth_fiber_prebundle (a : smooth_vector_prebundle I F E) :
  smooth_fiber_prebundle F (@total_space.proj B E) :=
{ pretrivialization_atlas :=
    pretrivialization.to_fiber_bundle_pretrivialization '' a.pretrivialization_atlas,
  pretrivialization_at := λ x, (a.pretrivialization_at x).to_fiber_bundle_pretrivialization,
  pretrivialization_mem_atlas := λ x, ⟨_, a.pretrivialization_mem_atlas x, rfl⟩,
  continuous_triv_change := begin
    rintros _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩,
    have := is_bounded_bilinear_map_apply.continuous.comp_continuous_on
      ((a.continuous_on_coord_change he' he).prod_map continuous_on_id),
    have H : e'.to_fiber_bundle_pretrivialization.to_local_equiv.target ∩
      e'.to_fiber_bundle_pretrivialization.to_local_equiv.symm ⁻¹'
      e.to_fiber_bundle_pretrivialization.to_local_equiv.source =
      (e'.base_set ∩ e.base_set) ×ˢ (univ : set F),
    { rw [e'.target_eq, e.source_eq],
      ext ⟨b, f⟩,
      simp only [-total_space.proj, and.congr_right_iff, e'.proj_symm_apply', iff_self,
        implies_true_iff] with mfld_simps {contextual := tt} },
    rw [H],
    refine (continuous_on_fst.prod this).congr _,
    rintros ⟨b, f⟩ ⟨hb, -⟩,
    dsimp only [function.comp, prod.map],
    rw [a.mk_coord_change _ _ hb, e'.mk_symm hb.1],
    refl,
  end,
  .. a }

/-- Topology on the total space that will make the prebundle into a bundle. -/
def total_space_topology (a : smooth_vector_prebundle I F E) :
  topological_space (total_space E) :=
a.to_topological_fiber_prebundle.total_space_topology

/-- Promotion from a `topologial_vector_prebundle.trivialization` to a
  `topological_vector_bundle.trivialization`. -/
def trivialization_of_mem_pretrivialization_atlas (a : smooth_vector_prebundle I F E)
  {e : topological_vector_bundle.pretrivialization 𝕜 F E} (he : e ∈ a.pretrivialization_atlas) :
  @topological_vector_bundle.trivialization R _ F E _ _ _ _ _ _ _ a.total_space_topology :=
begin
  letI := a.total_space_topology,
  exact { linear' := λ b, e.linear,
  ..a.to_topological_fiber_prebundle.trivialization_of_mem_pretrivialization_atlas ⟨e, he, rfl⟩ }
end

variable (a : smooth_vector_prebundle I F E)

lemma mem_trivialization_at_source (b : B) (x : E b) :
  total_space_mk b x ∈ (a.pretrivialization_at b).source :=
begin
  simp only [(a.pretrivialization_at b).source_eq, mem_preimage, total_space.proj],
  exact a.mem_base_pretrivialization_at b,
end

@[simp] lemma total_space_mk_preimage_source (b : B) :
  (total_space_mk b) ⁻¹' (a.pretrivialization_at b).source = univ :=
begin
  apply eq_univ_of_univ_subset,
  rw [(a.pretrivialization_at b).source_eq, ←preimage_comp, function.comp],
  simp only [total_space.proj],
  rw preimage_const_of_mem _,
  exact a.mem_base_pretrivialization_at b,
end

/-- Topology on the fibers `E b` induced by the map `E b → E.total_space`. -/
def fiber_topology (b : B) : topological_space (E b) :=
topological_space.induced (total_space_mk b) a.total_space_topology

@[continuity] lemma inducing_total_space_mk (b : B) :
  @inducing _ _ (a.fiber_topology b) a.total_space_topology (total_space_mk b) :=
by { letI := a.total_space_topology, letI := a.fiber_topology b, exact ⟨rfl⟩ }

@[continuity] lemma continuous_total_space_mk (b : B) :
  @continuous _ _ (a.fiber_topology b) a.total_space_topology (total_space_mk b) :=
begin
  letI := a.total_space_topology, letI := a.fiber_topology b,
  exact (a.inducing_total_space_mk b).continuous
end

/-- Make a `topological_vector_bundle` from a `smooth_vector_prebundle`.  Concretely this means
that, given a `smooth_vector_prebundle` structure for a sigma-type `E` -- which consists of a
number of "pretrivializations" identifying parts of `E` with product spaces `U × F` -- one
establishes that for the topology constructed on the sigma-type using
`smooth_vector_prebundle.total_space_topology`, these "pretrivializations" are actually
"trivializations" (i.e., homeomorphisms with respect to the constructed topology). -/
def to_topological_vector_bundle :
  @topological_vector_bundle R _ F E _ _ _ _ _ _ a.total_space_topology a.fiber_topology :=
{ total_space_mk_inducing := a.inducing_total_space_mk,
  trivialization_atlas := {e | ∃ e₀ (he₀ : e₀ ∈ a.pretrivialization_atlas),
    e = a.trivialization_of_mem_pretrivialization_atlas he₀},
  trivialization_at := λ x, a.trivialization_of_mem_pretrivialization_atlas
    (a.pretrivialization_mem_atlas x),
  mem_base_set_trivialization_at := a.mem_base_pretrivialization_at,
  trivialization_mem_atlas := λ x, ⟨_, a.pretrivialization_mem_atlas x, rfl⟩,
  continuous_on_coord_change := begin
    rintros _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩,
    refine (a.continuous_on_coord_change he he').congr _,
    intros b hb,
    ext v,
    rw [a.coord_change_apply he he' hb v, continuous_linear_equiv.coe_coe,
      trivialization.coord_change_apply],
    exacts [rfl, hb]
  end }

/-- The total space of a basic smooth bundle is endowed with a charted space structure, where the
charts are in bijection with the charts of the basis. -/
instance to_charted_space :
  charted_space (model_prod H F) (total_space E) :=
{ atlas := ⋃(e ∈ atlas H B), {Z.chart he},
  chart_at := λ p, Z.chart (chart_mem_atlas H p.1),
  mem_chart_source := λ p, by simp [mem_chart_source],
  chart_mem_atlas := λ p, begin
    simp only [mem_Union, mem_singleton_iff, chart_mem_atlas],
    exact ⟨chart_at H p.1, chart_mem_atlas H p.1, rfl⟩
  end }

/-- Smooth manifold structure on the total space of a basic smooth bundle -/
instance to_smooth_manifold [smooth_manifold_with_corners I B] :
  smooth_manifold_with_corners (I.prod (𝓘(𝕜, F))) (total_space E) :=
begin
  sorry
  /- We have to check that the charts belong to the smooth groupoid, i.e., they are smooth on their
  source, and their inverses are smooth on the target. Since both objects are of the same kind, it
  suffices to prove the first statement in A below, and then glue back the pieces at the end. -/
  -- let J := model_with_corners.to_local_equiv (I.prod (𝓘(𝕜, F))),
  -- have A : ∀ (e e' : local_homeomorph M H) (he : e ∈ atlas H M) (he' : e' ∈ atlas H M),
  --   cont_diff_on 𝕜 ∞
  --   (J ∘ ((Z.chart he).symm.trans (Z.chart he')) ∘ J.symm)
  --   (J.symm ⁻¹' ((Z.chart he).symm.trans (Z.chart he')).source ∩ range J),
  -- { assume e e' he he',
  --   have : J.symm ⁻¹' ((chart Z he).symm.trans (chart Z he')).source ∩ range J =
  --     (I.symm ⁻¹' (e.symm.trans e').source ∩ range I) ×ˢ (univ : set F),
  --     by { simp only [J, chart, model_with_corners.prod], mfld_set_tac },
  --   rw this,
  --   -- check separately that the two components of the coordinate change are smooth
  --   apply cont_diff_on.prod,
  --   show cont_diff_on 𝕜 ∞ (λ (p : E × F), (I ∘ e' ∘ e.symm ∘ I.symm) p.1)
  --        ((I.symm ⁻¹' (e.symm.trans e').source ∩ range I) ×ˢ (univ : set F)),
  --   { -- the coordinate change on the base is just a coordinate change for `M`, smooth since
  --     -- `M` is smooth
  --     have A : cont_diff_on 𝕜 ∞ (I ∘ (e.symm.trans e') ∘ I.symm)
  --       (I.symm ⁻¹' (e.symm.trans e').source ∩ range I) :=
  --     (has_groupoid.compatible (cont_diff_groupoid ∞ I) he he').1,
  --     have B : cont_diff_on 𝕜 ∞ (λ p : E × F, p.1)
  --       ((I.symm ⁻¹' (e.symm.trans e').source ∩ range I) ×ˢ (univ : set F)) :=
  --     cont_diff_fst.cont_diff_on,
  --     exact cont_diff_on.comp A B (prod_subset_preimage_fst _ _) },
  --   show cont_diff_on 𝕜 ∞ (λ (p : E × F),
  --     Z.coord_change ⟨chart_at H (e.symm (I.symm p.1)), _⟩ ⟨e', he'⟩
  --        ((chart_at H (e.symm (I.symm p.1)) : M → H) (e.symm (I.symm p.1)))
  --     (Z.coord_change ⟨e, he⟩ ⟨chart_at H (e.symm (I.symm p.1)), _⟩
  --       (e (e.symm (I.symm p.1))) p.2))
  --     ((I.symm ⁻¹' (e.symm.trans e').source ∩ range I) ×ˢ (univ : set F)),
  --   { /- The coordinate change in the fiber is more complicated as its definition involves the
  --     reference chart chosen at each point. However, it appears with its inverse, so using the
  --     cocycle property one can get rid of it, and then conclude using the smoothness of the
  --     cocycle as given in the definition of basic smooth bundles. -/
  --     have := Z.coord_change_smooth ⟨e, he⟩ ⟨e', he'⟩,
  --     rw I.image_eq at this,
  --     apply cont_diff_on.congr this,
  --     rintros ⟨x, v⟩ hx,
  --     simp only with mfld_simps at hx,
  --     let f := chart_at H (e.symm (I.symm x)),
  --     have A : I.symm x ∈ ((e.symm.trans f).trans (f.symm.trans e')).source,
  --       by simp only [hx.1.1, hx.1.2] with mfld_simps,
  --     rw e.right_inv hx.1.1,
  --     have := Z.coord_change_comp ⟨e, he⟩ ⟨f, chart_mem_atlas _ _⟩ ⟨e', he'⟩ (I.symm x) A v,
  --     simpa only [] using this } },
  -- refine @smooth_manifold_with_corners.mk _ _ _ _ _ _ _ _ _ _ _ ⟨_⟩,
  -- assume e₀ e₀' he₀ he₀',
  -- rcases (Z.mem_atlas_iff _).1 he₀ with ⟨e, he, rfl⟩,
  -- rcases (Z.mem_atlas_iff _).1 he₀' with ⟨e', he', rfl⟩,
  -- rw [cont_diff_groupoid, mem_groupoid_of_pregroupoid],
  -- exact ⟨A e e' he he', A e' e he' he⟩
end

end smooth_vector_prebundle
