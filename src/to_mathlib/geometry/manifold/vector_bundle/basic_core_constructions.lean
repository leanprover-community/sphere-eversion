/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/

import geometry.manifold.vector_bundle.pullback
import topology.vector_bundle.hom
import to_mathlib.geometry.manifold.misc_manifold

/-!
# Pullbacks of basic smooth vector bundle core
-/

noncomputable theory

open bundle set topological_space local_homeomorph
open_locale classical manifold

-- variables {𝕜 𝕜₁ 𝕜₂ B F F₁ F₂ M M₁ M₂ : Type*}
--   {E : B → Type*} {E₁ : B → Type*} {E₂ : B → Type*}
--   [nontrivially_normed_field 𝕜] [nontrivially_normed_field 𝕜₁] [nontrivially_normed_field 𝕜₂]
--   (σ : 𝕜₁ →+* 𝕜₂)
--   [∀ x, add_comm_monoid (E x)] [∀ x, module 𝕜 (E x)]
--   [normed_add_comm_group F] [normed_space 𝕜 F]
--   [topological_space (total_space E)] [∀ x, topological_space (E x)]
--   [∀ x, add_comm_monoid (E₁ x)] [∀ x, module 𝕜₁ (E₁ x)]
--   [normed_add_comm_group F₁] [normed_space 𝕜₁ F₁]
--   [topological_space (total_space E₁)] [∀ x, topological_space (E₁ x)]
--   [∀ x, add_comm_monoid (E₂ x)] [∀ x, module 𝕜₂ (E₂ x)]
--   [normed_add_comm_group F₂] [normed_space 𝕜₂ F₂]
--   [topological_space (total_space E₂)] [∀ x, topological_space (E₂ x)]

--   {EB : Type*} [normed_add_comm_group EB] [normed_space 𝕜 EB]
--   {HB : Type*} [topological_space HB] (IB₁ : model_with_corners 𝕜 EB HB)
--   [topological_space B] [charted_space HB B] [smooth_manifold_with_corners IB₁ B]
--   {EM : Type*} [normed_add_comm_group EM] [normed_space 𝕜 EM]
--   {HM : Type*} [topological_space HM] {IM : model_with_corners 𝕜 EM HM}
--   [topological_space M] [charted_space HM M] [Is : smooth_manifold_with_corners IM M]
--   {n : ℕ∞}
--   [fiber_bundle F₁ E₁] [vector_bundle 𝕜₁ F₁ E₁] [smooth_vector_bundle F₁ E₁ IB₁]
--   [fiber_bundle F₂ E₂] [vector_bundle 𝕜₂ F₂ E₂] [smooth_vector_bundle F₂ E₂ IB₂]
--   [∀ (x : B), has_continuous_add (E₂ x)] [∀ (x : B), has_continuous_smul 𝕜₂ (E₂ x)],
--     vector_bundle 𝕜₂ (F₁ →SL[σ] F₂) (continuous_linear_map σ F₁ E₁ F₂ E₂)

variables {𝕜 B F F₁ F₂ M M₁ M₂ : Type*}
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

  {EB : Type*} [normed_add_comm_group EB] [normed_space 𝕜 EB]
  {HB : Type*} [topological_space HB] (IB : model_with_corners 𝕜 EB HB)
  [topological_space B] [charted_space HB B] [smooth_manifold_with_corners IB B]
  {EM : Type*} [normed_add_comm_group EM] [normed_space 𝕜 EM]
  {HM : Type*} [topological_space HM] {IM : model_with_corners 𝕜 EM HM}
  [topological_space M] [charted_space HM M] [Is : smooth_manifold_with_corners IM M]
  {n : ℕ∞}
  [fiber_bundle F₁ E₁] [vector_bundle 𝕜 F₁ E₁] [smooth_vector_bundle F₁ E₁ IB]
  [fiber_bundle F₂ E₂] [vector_bundle 𝕜 F₂ E₂] [smooth_vector_bundle F₂ E₂ IB]
  [∀ x, has_continuous_add (E₂ x)] [∀ x, has_continuous_smul 𝕜 (E₂ x)]

namespace basic_smooth_vector_bundle_core

-- variables [smooth_manifold_with_corners IB' B']

-- lemma pullback_prod_aux {e₁ : local_homeomorph B HB} {e₂ : local_homeomorph B' HB'}
--   (h : (e₁.prod e₂).source.nonempty)
--   (he₁ : e₁ ∈ atlas HB B) (he₂ : e₂ ∈ atlas HB' B') :
--   image2.some local_homeomorph.prod (atlas HB B) (atlas HB' B') ⟨_, mem_image2_of_mem he₁ he₂⟩ =
--   (⟨e₁, he₁⟩, ⟨e₂, he₂⟩) :=
-- begin
--   obtain ⟨h₁, h₂⟩ :=
--     (prod_eq_prod_of_nonempty' h).mp (image2.some_spec local_homeomorph.prod he₁ he₂),
--   simp_rw [prod.ext_iff, subtype.ext_iff, h₁, h₂, subtype.coe_mk, eq_self_iff_true, and_self]
-- end

-- lemma trivial_coord_change_at {b b' : B} (x : HB) :
--   (trivial_basic_smooth_vector_bundle_core IB B F).coord_change (achart HB b) (achart HB b') x =
--   1 :=
-- rfl

-- lemma tangent_space_self_coord_change_at {b b' x : F} :
--   (tangent_bundle_core 𝓘(𝕜, F) F).coord_change (achart F b) (achart F b') x = 1 :=
-- begin
--   simp_rw [tangent_bundle_core_coord_change, model_with_corners_self_coe,
--     model_with_corners_self_coe_symm, achart_def, range_id, chart_at_self_eq, function.comp,
--     local_homeomorph.refl_symm, local_homeomorph.refl_apply, function.id_def],
--   exact fderiv_within_id unique_diff_within_at_univ
-- end


-- include Z

-- /-- The pullback of `basic_smooth_vector_bundle_core`, assuming `f` preserves the specific chart
--   structure of the manifold. This will be true in particular if `f` is a projection from `M × N` to
--   either `M` or `N`. Some hypotheses in this def might be redundant.
--   The hypotheses h1v, h1g and h2g can probably be weakened to assume that the point lies in the
--   appropriate source/target, but this stronger hypothesis is also true for the projections. -/
-- @[simps]
-- def pullback (v : VB' → VB) (hv : cont_diff 𝕜 ∞ v) (h : HB' → HB)
--   (h1v : ∀ x : VB', IB.symm (v x) = h (IB'.symm x))
--   (h2v : range IB' ⊆ v ⁻¹' range IB)
--   (g : atlas HB' B' → atlas HB B)
--   (h1g : ∀ (e : atlas HB' B') (b : B'), (g e).1 (f b) = h (e.1 b))
--   (h2g : ∀ (e : atlas HB' B') (x : HB'), (g e).1.symm (h x) = f (e.1.symm x))
--   (hf : ∀ (e : atlas HB' B'), maps_to f e.1.source (g e).1.source)
--   (hh : ∀ (e : atlas HB' B'), maps_to h e.1.target (g e).1.target) :
--   basic_smooth_vector_bundle_core IB' B' F :=
-- { coord_change := λ e e' b, Z.coord_change (g e) (g e') (h b),
--   coord_change_self := λ e x hx v, Z.coord_change_self (g e) (h x) (hh e hx) v,
--   coord_change_comp := begin
--     intros i j k x hx v,
--     rw [← Z.coord_change_comp (g i) (g j) (g k) (h x) _ v],
--     { simp_rw [trans_apply, h2g, h1g] },
--     simp only with mfld_simps at hx ⊢,
--     refine ⟨⟨hh i hx.1.1, _⟩, ⟨_, _⟩⟩,
--     { rw [h2g], exact hf j hx.1.2 },
--     { rw [h2g, h1g], exact hh j hx.2.1 },
--     { rw [h2g, h1g, h2g], exact hf k hx.2.2 },
--   end,
--   coord_change_smooth_clm := begin
--     intros i j,
--     convert (Z.coord_change_smooth_clm (g i) (g j)).comp hv.cont_diff_on _,
--     { ext1 b, simp_rw [function.comp_apply, h1v] },
--     { simp_rw [model_with_corners.image_eq, trans_source, preimage_inter,
--         preimage_preimage, h1v, h2g, ← @preimage_preimage _ _ _ h IB'.symm],
--       refine inter_subset_inter (inter_subset_inter (preimage_mono $ hh i) (λ x hx, hf j hx)) h2v }
--   end }

-- lemma pullback_chart {v : VB' → VB} {hv : cont_diff 𝕜 ∞ v} {h : HB' → HB}
--   {h1v : ∀ x : VB', IB.symm (v x) = h (IB'.symm x)}
--   {h2v : range IB' ⊆ v ⁻¹' range IB}
--   {g : atlas HB' B' → atlas HB B}
--   {h1g : ∀ (e : atlas HB' B') (b : B'), (g e).1 (f b) = h (e.1 b)}
--   {h2g : ∀ (e : atlas HB' B') (x : HB'), (g e).1.symm (h x) = f (e.1.symm x)}
--   {hf : ∀ (e : atlas HB' B'), maps_to f e.1.source (g e).1.source}
--   {hh : ∀ (e : atlas HB' B'), maps_to h e.1.target (g e).1.target}
--   (g_at : ∀ b : B', g (achart HB' b) = achart HB (f b))
--   (h_at : ∀ b x : B', h (chart_at HB' b x) = chart_at HB (f b) (f x))
--   (x : (pullback f Z v hv h h1v h2v g h1g h2g hf hh).to_vector_bundle_core.total_space)
--   {e : local_homeomorph B' HB'} (he : e ∈ atlas HB' B') :
--   (Z.pullback f v hv h h1v h2v g h1g h2g hf hh).chart he x =
--   (e x.1, (Z.chart (g ⟨e, he⟩).2 ⟨f x.1, x.2⟩).2) :=
-- by simp_rw [chart, trans_apply, prod_apply, trivialization.coe_coe, local_homeomorph.refl_apply,
--   function.id_def, vector_bundle_core.local_triv_apply,
--   to_vector_bundle_core_coord_change, to_vector_bundle_core_index_at,
--   pullback_coord_change, g_at, achart_def, h_at, subtype.eta]

-- variables (IB' B')

-- /-- The pullback of `basic_smooth_vector_bundle_core` along the map `B × B' → B` -/
-- def pullback_fst : basic_smooth_vector_bundle_core (IB.prod IB') (B × B') F :=
-- begin
--   refine Z.pullback cont_mdiff_map.fst prod.fst cont_diff_fst prod.fst
--     (λ x, rfl) _ (λ e, (image2.some local_homeomorph.prod _ _ e).1) _ _ _ _,
--   { simp_rw [model_with_corners_prod_coe, range_prod_map, prod_subset_preimage_fst] },
--   { rintro ⟨_, ⟨e₁, e₂, he₁, he₂, rfl⟩⟩ b,
--     obtain ⟨e₂', he₂', heq⟩ := image2.some_spec_fst local_homeomorph.prod he₁ he₂,
--     exact congr_arg (λ e : local_homeomorph (B × B') (HB × HB'), (e b).1) heq },
--   { rintro ⟨_, ⟨e₁, e₂, he₁, he₂, rfl⟩⟩ x,
--     obtain ⟨e₂', he₂', heq⟩ := image2.some_spec_fst local_homeomorph.prod he₁ he₂,
--     exact congr_arg (λ e : local_homeomorph (B × B') (HB × HB'), (e.symm x).1) heq },
--   { rintro ⟨_, ⟨e₁, e₂, he₁, he₂, rfl⟩⟩ b hb,
--     obtain ⟨e₂', he₂', heq⟩ := image2.some_spec_fst local_homeomorph.prod he₁ he₂,
--     apply_fun (λ e : local_homeomorph (B × B') (HB × HB'), b ∈ e.source) at heq,
--     exact (heq.mpr hb).1 },
--   { rintro ⟨_, ⟨e₁, e₂, he₁, he₂, rfl⟩⟩ x hx,
--     obtain ⟨e₂', he₂', heq⟩ := image2.some_spec_fst local_homeomorph.prod he₁ he₂,
--     apply_fun (λ e : local_homeomorph (B × B') (HB × HB'), x ∈ e.target) at heq,
--     exact (heq.mpr hx).1 }
-- end

-- variables {IB' B'}

-- def pullback_fst_coord_change
--   {e₁ e₁' : local_homeomorph B HB} {e₂ e₂' : local_homeomorph B' HB'} (he₁ : e₁ ∈ atlas HB B)
--   (he₁' : e₁' ∈ atlas HB B) (he₂ : e₂ ∈ atlas HB' B') (he₂' : e₂' ∈ atlas HB' B')
--   (h : (e₁.prod e₂).source.nonempty) (h' : (e₁'.prod e₂').source.nonempty)
--   (b : model_prod HB HB') : (Z.pullback_fst B' IB').coord_change
--   ⟨_, mem_image2_of_mem he₁ he₂⟩ ⟨_, mem_image2_of_mem he₁' he₂'⟩ b =
--   Z.coord_change ⟨e₁, he₁⟩ ⟨e₁', he₁'⟩ b.1 :=
-- by simp_rw [pullback_fst, pullback, pullback_prod_aux h, pullback_prod_aux h']

-- def pullback_fst_coord_change_at {b b' : B × B'}
--   (x : model_prod HB HB') : (Z.pullback_fst B' IB').coord_change
--   (achart (model_prod HB HB') b) (achart (model_prod HB HB') b') x =
--   Z.coord_change (achart HB b.1) (achart HB b'.1) x.1 :=
-- Z.pullback_fst_coord_change _ _ (chart_mem_atlas HB' b.2) (chart_mem_atlas HB' b'.2)
--   ⟨b, mk_mem_prod (mem_chart_source HB b.1) (mem_chart_source HB' b.2)⟩
--   ⟨b', mk_mem_prod (mem_chart_source HB b'.1) (mem_chart_source HB' b'.2)⟩ x

-- lemma pullback_fst_chart
--   (x : (Z.pullback_fst B' IB').to_vector_bundle_core.total_space)
--   {e : local_homeomorph B HB} {e' : local_homeomorph B' HB'} (he : e ∈ atlas HB B)
--   (he' : e' ∈ atlas HB' B') (h : (e.prod e').source.nonempty) :
--   (Z.pullback_fst B' IB').chart (mem_image2_of_mem he he') x =
--   ((e x.1.1, e' x.1.2), (Z.chart he ⟨x.1.1, x.2⟩).2) :=
-- begin
--   refine (pullback_chart _ Z _ _ x _).trans _,
--   { intros b,
--     obtain ⟨e₂, he₂, heq⟩ := image2.some_spec_fst local_homeomorph.prod
--       (chart_mem_atlas HB b.1) (chart_mem_atlas HB' b.2),
--     have h2e₂ : e₂.source.nonempty,
--     { have := congr_arg (λ e : local_homeomorph (B × B') (HB × HB'), b ∈ e.source) heq,
--       exact ⟨b.2, ((iff_of_eq this).mpr ⟨mem_chart_source HB b.1, mem_chart_source HB' b.2⟩).2⟩ },
--     ext1, ext1 x,
--     exact congr_arg (λ e : local_homeomorph (B × B') (HB × HB'), (e (x, b.2)).1) heq,
--     exact λ y, congr_arg (λ e : local_homeomorph (B × B') (HB × HB'), (e.symm (y, e' b.2)).1) heq,
--     have := congr_arg (λ e : local_homeomorph (B × B') (HB × HB'), prod.fst '' e.source) heq,
--     simp_rw [local_homeomorph.prod_source, fst_image_prod _ h2e₂,
--       fst_image_prod _ ⟨b.2, mem_chart_source HB' b.2⟩] at this,
--     exact this },
--   { intros b x, refl },
--   { congr', rw [pullback_prod_aux h] }
-- end

-- lemma pullback_fst_chart_at
--   (x : (Z.pullback_fst B' IB').to_vector_bundle_core.total_space)
--   (b : B) (b' : B') : (Z.pullback_fst B' IB').chart
--   (mem_image2_of_mem (chart_mem_atlas HB b) (chart_mem_atlas HB' b')) x =
--   ((chart_at HB b x.1.1, chart_at HB' b' x.1.2), (Z.chart (chart_mem_atlas HB b) ⟨x.1.1, x.2⟩).2) :=
-- Z.pullback_fst_chart x _ _
--   ⟨(b, b'), mk_mem_prod (mem_chart_source HB b) (mem_chart_source HB' b')⟩

-- omit Z
-- variables (IB B)

-- /-- The pullback of `basic_smooth_vector_bundle_core` along the map `B × B' → B` -/
-- def pullback_snd (Z : basic_smooth_vector_bundle_core IB' B' F) :
--   basic_smooth_vector_bundle_core (IB.prod IB') (B × B') F :=
-- begin
--   refine Z.pullback cont_mdiff_map.snd prod.snd cont_diff_snd prod.snd
--     (λ x, rfl) _ (λ e, (image2.some local_homeomorph.prod _ _ e).2) _ _ _ _,
--   { simp_rw [model_with_corners_prod_coe, range_prod_map, prod_subset_preimage_snd] },
--   { rintro ⟨_, ⟨e₁, e₂, he₁, he₂, rfl⟩⟩ b,
--     obtain ⟨e₂', he₂', heq⟩ := image2.some_spec_snd local_homeomorph.prod he₁ he₂,
--     exact congr_arg (λ e : local_homeomorph (B × B') (HB × HB'), (e b).2) heq },
--   { rintro ⟨_, ⟨e₁, e₂, he₁, he₂, rfl⟩⟩ x,
--     obtain ⟨e₂', he₂', heq⟩ := image2.some_spec_snd local_homeomorph.prod he₁ he₂,
--     exact congr_arg (λ e : local_homeomorph (B × B') (HB × HB'), (e.symm x).2) heq },
--   { rintro ⟨_, ⟨e₁, e₂, he₁, he₂, rfl⟩⟩ b hb,
--     obtain ⟨e₂', he₂', heq⟩ := image2.some_spec_snd local_homeomorph.prod he₁ he₂,
--     apply_fun (λ e : local_homeomorph (B × B') (HB × HB'), b ∈ e.source) at heq,
--     exact (heq.mpr hb).2 },
--   { rintro ⟨_, ⟨e₁, e₂, he₁, he₂, rfl⟩⟩ x hx,
--     obtain ⟨e₂', he₂', heq⟩ := image2.some_spec_snd local_homeomorph.prod he₁ he₂,
--     apply_fun (λ e : local_homeomorph (B × B') (HB × HB'), x ∈ e.target) at heq,
--     exact (heq.mpr hx).2 }
-- end

-- variables {IB B}

-- def pullback_snd_coord_change (Z : basic_smooth_vector_bundle_core IB' B' F)
--   {e₁ e₁' : local_homeomorph B HB} {e₂ e₂' : local_homeomorph B' HB'} (he₁ : e₁ ∈ atlas HB B)
--   (he₁' : e₁' ∈ atlas HB B) (he₂ : e₂ ∈ atlas HB' B') (he₂' : e₂' ∈ atlas HB' B')
--   (h : (e₁.prod e₂).source.nonempty) (h' : (e₁'.prod e₂').source.nonempty)
--   (x : model_prod HB HB') : (Z.pullback_snd B IB).coord_change
--   ⟨_, mem_image2_of_mem he₁ he₂⟩ ⟨_, mem_image2_of_mem he₁' he₂'⟩ x =
--   Z.coord_change ⟨e₂, he₂⟩ ⟨e₂', he₂'⟩ x.2 :=
-- by simp_rw [pullback_snd, pullback, pullback_prod_aux h, pullback_prod_aux h']

-- def pullback_snd_coord_change_at (Z : basic_smooth_vector_bundle_core IB' B' F) {b b' : B × B'}
--   (x : model_prod HB HB') : (Z.pullback_snd B IB).coord_change
--   (achart (model_prod HB HB') b) (achart (model_prod HB HB') b') x =
--   Z.coord_change (achart HB' b.2) (achart HB' b'.2) x.2 :=
-- Z.pullback_snd_coord_change (chart_mem_atlas HB b.1) (chart_mem_atlas HB b'.1) _ _
--   ⟨b, mk_mem_prod (mem_chart_source HB b.1) (mem_chart_source HB' b.2)⟩
--   ⟨b', mk_mem_prod (mem_chart_source HB b'.1) (mem_chart_source HB' b'.2)⟩ x

-- lemma pullback_snd_chart (Z : basic_smooth_vector_bundle_core IB' B' F)
--   (x : (Z.pullback_snd B IB).to_vector_bundle_core.total_space)
--   {e : local_homeomorph B HB} {e' : local_homeomorph B' HB'} (he : e ∈ atlas HB B)
--   (he' : e' ∈ atlas HB' B') (h : (e.prod e').source.nonempty) :
--   (Z.pullback_snd B IB).chart (mem_image2_of_mem he he') x =
--   ((e x.1.1, e' x.1.2), (Z.chart he' ⟨x.1.2, x.2⟩).2) :=
-- begin
--   refine (pullback_chart _ Z _ _ x _).trans _,
--   { intros b,
--     obtain ⟨e₂, he₂, heq⟩ := image2.some_spec_snd local_homeomorph.prod
--       (chart_mem_atlas HB b.1) (chart_mem_atlas HB' b.2),
--     have h2e₂ : e₂.source.nonempty,
--     { have := congr_arg (λ e : local_homeomorph (B × B') (HB × HB'), b ∈ e.source) heq,
--       exact ⟨b.1, ((iff_of_eq this).mpr ⟨mem_chart_source HB b.1, mem_chart_source HB' b.2⟩).1⟩ },
--     ext1, ext1 x,
--     exact congr_arg (λ e : local_homeomorph (B × B') (HB × HB'), (e (b.1, x)).2) heq,
--     exact λ y, congr_arg (λ e₀ : local_homeomorph (B × B') (HB × HB'), (e₀.symm (e b.1, y)).2) heq,
--     have := congr_arg (λ e : local_homeomorph (B × B') (HB × HB'), prod.snd '' e.source) heq,
--     simp_rw [local_homeomorph.prod_source, snd_image_prod h2e₂,
--       snd_image_prod ⟨b.1, mem_chart_source HB b.1⟩] at this,
--     exact this },
--   { intros b x, refl },
--   { congr', rw [pullback_prod_aux h] }
-- end

-- lemma pullback_snd_chart_at (Z : basic_smooth_vector_bundle_core IB' B' F)
--   (x : (Z.pullback_snd B IB).to_vector_bundle_core.total_space)
--   (b : B) (b' : B') : (Z.pullback_snd B IB).chart
--   (mem_image2_of_mem (chart_mem_atlas HB b) (chart_mem_atlas HB' b')) x =
--   ((chart_at HB b x.1.1, chart_at HB' b' x.1.2), (Z.chart (chart_mem_atlas HB' b') ⟨x.1.2, x.2⟩).2) :=
-- Z.pullback_snd_chart x _ _
--   ⟨(b, b'), mk_mem_prod (mem_chart_source HB b) (mem_chart_source HB' b')⟩


/-!
### Homs of smooth vector bundles over the same base space
-/

open continuous_linear_map

local notation `LE₁E₂'` := bundle.continuous_linear_map (ring_hom.id 𝕜) F₁ E₁ F₂ E₂

def topological_space.continuous_linear_map' (x) :
  topological_space ((bundle.continuous_linear_map (ring_hom.id 𝕜) F₁ E₁ F₂ E₂) x) :=
by apply_instance
attribute [instance] topological_space.continuous_linear_map' -- why is this needed?

instance smooth_vector_bundle.continuous_linear_map :
  smooth_vector_bundle (F₁ →L[𝕜] F₂)
    (bundle.continuous_linear_map (ring_hom.id 𝕜) F₁ E₁ F₂ E₂) IB :=
{ smooth_on_coord_change := begin
    rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩, resetI,
    sorry,
    -- -- basic_smooth_vector_bundle_core proof
    -- refine ((compL 𝕜 F₁ F₂ F₂).cont_diff.comp_cont_diff_on
    --   (smooth_on_coord_change e e')).clm_comp _,
    -- refine (compL 𝕜 F₁ F₁ F₂).flip.cont_diff.comp_cont_diff_on _,
    -- refine (((Z.coord_change_smooth_clm j i).comp (cont_diff_on_coord_change' IB i.2 j.2) _).congr
    --   _).mono _,
    -- { rw [@preimage_comp _ _ _ _ IB, IB.preimage_image, @preimage_comp _ _ _ IB.symm],
    --   exact (inter_subset_left _ _).trans (preimage_mono $ local_homeomorph.maps_to _) },
    -- { intros x hx, simp_rw [function.comp_apply, trans_apply, IB.left_inv] },
    -- { rw [← IB.image_eq] },
    -- -- pullback proof
    -- refine ((smooth_on_coord_change e e').comp f.smooth.smooth_on
    --   (λ b hb, hb)).congr _,
    -- rintro b (hb : f b ∈ e.base_set ∩ e'.base_set), ext v,
    -- show ((e.pullback f).coord_changeL 𝕜 (e'.pullback f) b) v = (e.coord_changeL 𝕜 e' (f b)) v,
    -- rw [e.coord_changeL_apply e' hb, (e.pullback f).coord_changeL_apply' _],
    -- exacts [rfl, hb]
  end }

#exit
lemma hom_chart' (x : LE₁E₂')
  {e : local_homeomorph B HB} (he : e ∈ atlas HB B) :
  (Z.hom Z').chart he x = (e x.1, Z'.coord_change (achart HB x.1) ⟨e, he⟩ (chart_at HB x.1 x.1) ∘L
    x.2 ∘L Z.coord_change ⟨e, he⟩ (achart HB x.1) (e x.1)) :=
by simp_rw [chart, trans_apply, local_homeomorph.prod_apply, trivialization.coe_coe,
  local_homeomorph.refl_apply, function.id_def, vector_bundle_core.local_triv_apply,
  to_vector_bundle_core_coord_change, to_vector_bundle_core_index_at,
  hom_coord_change, comp_apply, flip_apply, compL_apply, achart_def,
  (chart_at HB x.1).left_inv (mem_chart_source HB x.1)]

lemma hom_chart (x : LE₁E₂') (x₀ : B) :
  (Z.hom Z').chart (chart_mem_atlas HB x₀) x =
  (chart_at HB x₀ x.1, in_coordinates' Z Z' x₀ x.1 x₀ x.1 x.2) :=
by simp_rw [hom_chart', in_coordinates', achart_def]

lemma hom_chart_source (x₀ : B) :
  ((Z.hom Z').chart (chart_mem_atlas HB x₀)).source =
  sigma.fst ⁻¹' (chart_at HB x₀).source :=
begin
  -- simp_rw [chart, trans_source],
  -- simp only with mfld_simps,
  set ZZ' := (Z.hom Z').to_vector_bundle_core,
  change ZZ'.proj ⁻¹' (chart_at HB x₀).source ∩
    (λ x, ZZ'.local_triv (achart HB x₀) x) ⁻¹' (chart_at HB x₀).source ×ˢ univ = _,
  simp_rw [vector_bundle_core.local_triv_apply, mk_preimage_prod, preimage_univ,
    inter_univ],
  exact inter_self _
end

lemma hom_chart_target (x₀ : B) :
  ((Z.hom Z').chart (chart_mem_atlas HB x₀)).target =
  prod.fst ⁻¹' (chart_at HB x₀).target :=
begin
  simp_rw [chart, trans_target],
  simp only with mfld_simps,
  simp_rw [prod_univ, preimage_preimage, inter_eq_left_iff_subset],
  rw [← @preimage_preimage _ _ _ (chart_at HB x₀).symm],
  refine preimage_mono _,
  rw [← image_subset_iff],
  exact (chart_at HB x₀).symm.bij_on.image_eq.subset
end

lemma hom_ext_chart_at {v v' : LE₁E₂'} :
  ext_chart_at (IB.prod 𝓘(𝕜, F →L[𝕜] F')) v v' =
  (ext_chart_at IB v.1 v'.1, in_coordinates' Z Z' v.1 v'.1 v.1 v'.1 v'.2) :=
by simp_rw [ext_chart_at_coe, function.comp_apply, to_charted_space_chart_at, hom_chart,
    model_with_corners.prod_apply, model_with_corners_self_coe, function.id_def]

lemma smooth_at.hom_bundle_mk {f : M → B} {ϕ : M → F →L[𝕜] F'} {x₀ : M}
  (hf : smooth_at IM IB f x₀)
  (hϕ : smooth_at IM 𝓘(𝕜, F →L[𝕜] F')
    (λ x, in_coordinates' Z Z' (f x₀) (f x) (f x₀) (f x) (ϕ x)) x₀) :
  smooth_at IM (IB.prod 𝓘(𝕜, F →L[𝕜] F')) (λ x, total_space_mk (f x) (ϕ x) : M → LE₁E₂') x₀ :=
begin
  rw [smooth_at, (Z.hom Z').cont_mdiff_at_iff_target],
  refine ⟨hf.continuous_at, _⟩,
  simp_rw [function.comp, hom_ext_chart_at],
  exact (cont_mdiff_at_ext_chart_at.comp _ hf).prod_mk_space hϕ
end

lemma smooth_at_hom_bundle {f : M → LE₁E₂'} {x₀ : M} :
  smooth_at IM (IB.prod 𝓘(𝕜, F →L[𝕜] F')) f x₀ ↔
  smooth_at IM IB (λ x, (f x).1) x₀ ∧
  smooth_at IM 𝓘(𝕜, F →L[𝕜] F')
    (λ x, in_coordinates' I I Z' (f x₀).1 (f x).1 (f x₀).1 (f x).1 (f x).2) x₀ :=
begin
  refine ⟨λ h, ⟨_, _⟩, λ h, _⟩,
  { apply ((Z.hom Z').smooth_proj _).comp x₀ h },
  { rw [smooth_at, (Z.hom Z').cont_mdiff_at_iff_target, ← smooth_at] at h,
    have h2 := (cont_diff_at_snd.cont_mdiff_at.comp _ h.2),
    simp_rw [function.comp, hom_ext_chart_at] at h2,
    exact h2 },
  { convert smooth_at.hom_bundle_mk Z Z' h.1 h.2, ext; refl }
end

section cech_cocycles

/- Clearly `coord_change_equiv` is actually a result about topological vector bundles. I think it
should be possible to define this as follows:
```
noncomputable def coord_change_equiv : F ≃L[𝕜] F :=
trivialization.coord_change
  (trivialization_at 𝕜 F Z.to_vector_bundle_core.fiber x)
  (trivialization_at 𝕜 F Z.to_vector_bundle_core.fiber (j.val.symm (i x))) x
```
However the API for this part of the library seems to need of a lot of work so I gave up attempting
to use it.
-/

variables {i j : atlas HB B} {x : B}

protected lemma coord_change_equiv_aux
  (hx₁ : x ∈ (i : local_homeomorph B HB).source)
  (hx₂ : x ∈ (j : local_homeomorph B HB).source) (v : F) :
  Z.coord_change j i (j x) (Z.coord_change i j (i x) v) = v :=
begin
  have : i x ∈ ((i.val.symm.trans j.val).trans (j.val.symm.trans i.val)).to_local_equiv.source,
  { simp only [subtype.val_eq_coe, local_homeomorph.trans_to_local_equiv,
      local_homeomorph.symm_to_local_equiv, local_equiv.trans_source, local_equiv.symm_source,
      local_homeomorph.coe_coe_symm, local_equiv.coe_trans, local_homeomorph.coe_coe,
      set.mem_inter_iff, set.mem_preimage, function.comp_app],
    refine ⟨⟨_, _⟩, _, _⟩,
    { exact i.val.map_source hx₁, },
    { erw i.val.left_inv hx₁, exact hx₂, },
    { erw i.val.left_inv hx₁, exact j.val.map_source hx₂, },
    { erw [i.val.left_inv hx₁, j.val.left_inv hx₂], exact hx₁, }, },
  have hx' : i.val.symm.trans j.val (i x) = j x,
  { simp only [subtype.val_eq_coe, local_homeomorph.coe_trans, function.comp_app],
    erw i.val.left_inv hx₁, refl, },
  rw [← hx', Z.coord_change_comp i j i (i x) this v,
    Z.coord_change_self i (i x) (i.val.map_source hx₁)],
end

variables (i j x)

/-- Čech cocycle representatives for this bundle relative to the chosen atlas (taking the junk
value `1` outside the intersection of the sources of the two charts). -/
noncomputable def coord_change_equiv : F ≃L[𝕜] F :=
if hx : x ∈ (i : local_homeomorph B HB).source ∩ (j : local_homeomorph B HB).source then
{ to_fun    := Z.coord_change i j (i x),
  inv_fun   := Z.coord_change j i (j x),
  left_inv  := Z.coord_change_equiv_aux hx.1 hx.2,
  right_inv := Z.coord_change_equiv_aux hx.2 hx.1,
  continuous_inv_fun := (Z.coord_change j i _).continuous,
  .. Z.coord_change i j (i x) }
else 1

variables {i j x}

lemma coe_coord_change_equiv
  (hx : x ∈ (i : local_homeomorph B HB).source ∩ (j : local_homeomorph B HB).source) :
  (Z.coord_change_equiv i j x : F → F) = (Z.coord_change i j (i x) : F → F) :=
by simpa only [coord_change_equiv, dif_pos hx]

end cech_cocycles

end basic_smooth_vector_bundle_core
