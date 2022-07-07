/-
Copyright © 2022 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/

import geometry.manifold.cont_mdiff_map
import to_mathlib.geometry.manifold.bundle_prelims

/-!
# Pullbacks of basic smooth vector bundle core
-/

noncomputable theory

open bundle set topological_space topological_vector_bundle local_homeomorph
open_locale classical manifold

variables {𝕜 B B' M VB VB' VM HB HB' HM : Type*}
variables [nondiscrete_normed_field 𝕜]
variables [normed_group VB] [normed_space 𝕜 VB] [normed_group VB'] [normed_space 𝕜 VB']
variables [normed_group VM] [normed_space 𝕜 VM]
variables [topological_space HB] [topological_space HB'] [topological_space HM]
variables {IB : model_with_corners 𝕜 VB HB} {IB' : model_with_corners 𝕜 VB' HB'}
variables {IM : model_with_corners 𝕜 VM HM}
variables {F F' : Type*}
variables [normed_group F] [normed_space 𝕜 F] [normed_group F'] [normed_space 𝕜 F']
variables [topological_space B] [charted_space HB B] [smooth_manifold_with_corners IB B]
variables [topological_space B'] [charted_space HB' B'] [smooth_manifold_with_corners IB' B']
variables [topological_space M] [charted_space HM M] [smooth_manifold_with_corners IM M]
variables (f : C^∞⟮IB', B'; IB, B⟯) -- todo: define cont_mdiff_map_class
variables (Z : basic_smooth_vector_bundle_core IB B F)
variables (Z' : basic_smooth_vector_bundle_core IB B F')

namespace basic_smooth_vector_bundle_core

include Z

/-- The pullback of `basic_smooth_vector_bundle_core`, assuming `f` preserves the specific chart
  structure of the manifold. This will be true in particular if `f` is a projection from `M × N` to
  either `M` or `N`. Some hypotheses in this def might be redundant.
  The hypotheses h1v, h1g and h2g can probably be weakened to assume that the point lies in the
  appropriate source/target, but this stronger hypothesis is also true for the projections. -/
@[simps]
def pullback (v : VB' → VB) (hv : cont_diff 𝕜 ∞ v) (h : HB' → HB)
  (h1v : ∀ x : VB', IB.symm (v x) = h (IB'.symm x))
  (h2v : range IB' ⊆ v ⁻¹' range IB)
  (g : atlas HB' B' → atlas HB B)
  (h1g : ∀ (e : atlas HB' B') (b : B'), (g e).1 (f b) = h (e.1 b))
  (h2g : ∀ (e : atlas HB' B') (x : HB'), (g e).1.symm (h x) = f (e.1.symm x))
  (hf : ∀ (e : atlas HB' B'), maps_to f e.1.source (g e).1.source)
  (hh : ∀ (e : atlas HB' B'), maps_to h e.1.target (g e).1.target) :
  basic_smooth_vector_bundle_core IB' B' F :=
{ coord_change := λ e e' b, Z.coord_change (g e) (g e') (h b),
  coord_change_self := λ e x hx v, Z.coord_change_self (g e) (h x) (hh e hx) v,
  coord_change_comp := begin
    intros i j k x hx v,
    rw [← Z.coord_change_comp (g i) (g j) (g k) (h x) _ v],
    { simp_rw [trans_apply, h2g, h1g] },
    simp only with mfld_simps at hx ⊢,
    refine ⟨⟨hh i hx.1.1, _⟩, ⟨_, _⟩⟩,
    { rw [h2g], exact hf j hx.1.2 },
    { rw [h2g, h1g], exact hh j hx.2.1 },
    { rw [h2g, h1g, h2g], exact hf k hx.2.2 },
  end,
  coord_change_smooth_clm := begin
    intros i j,
    convert (Z.coord_change_smooth_clm (g i) (g j)).comp hv.cont_diff_on _,
    { ext1 b, simp_rw [function.comp_apply, h1v] },
    { simp_rw [model_with_corners.image_eq, trans_source, preimage_inter,
        preimage_preimage, h1v, h2g, ← @preimage_preimage _ _ _ h IB'.symm],
      refine inter_subset_inter (inter_subset_inter (preimage_mono $ hh i) (λ x hx, hf j hx)) h2v }
  end }

attribute [simps coord_change index_at] to_topological_vector_bundle_core

lemma pullback.chart_eq {v : VB' → VB} {hv : cont_diff 𝕜 ∞ v} {h : HB' → HB}
  {h1v : ∀ x : VB', IB.symm (v x) = h (IB'.symm x)}
  {h2v : range IB' ⊆ v ⁻¹' range IB}
  {g : atlas HB' B' → atlas HB B}
  {h1g : ∀ (e : atlas HB' B') (b : B'), (g e).1 (f b) = h (e.1 b)}
  {h2g : ∀ (e : atlas HB' B') (x : HB'), (g e).1.symm (h x) = f (e.1.symm x)}
  {hf : ∀ (e : atlas HB' B'), maps_to f e.1.source (g e).1.source}
  {hh : ∀ (e : atlas HB' B'), maps_to h e.1.target (g e).1.target}
  (g_at : ∀ b : B', g (achart HB' b) = achart HB (f b))
  (h_at : ∀ b x : B', h (chart_at HB' b x) = chart_at HB (f b) (f x))
  (x : (pullback f Z v hv h h1v h2v g h1g h2g hf hh).to_topological_vector_bundle_core.total_space)
  {e : local_homeomorph B' HB'} (he : e ∈ atlas HB' B') :
  (Z.pullback f v hv h h1v h2v g h1g h2g hf hh).chart he x =
  (e x.1, (Z.chart (g ⟨e, he⟩).2 ⟨f x.1, x.2⟩).2) :=
by simp_rw [chart, trans_apply, prod_apply, trivialization.coe_coe, local_homeomorph.refl_apply,
  function.id_def, topological_vector_bundle_core.local_triv_apply,
  to_topological_vector_bundle_core_coord_change, to_topological_vector_bundle_core_index_at,
  pullback_coord_change, ← achart_def, g_at, h_at, subtype.eta]

variables (IB' B')

/-- The pullback of `basic_smooth_vector_bundle_core` along the map `B × B' → B` -/
def pullback_fst : basic_smooth_vector_bundle_core (IB.prod IB') (B × B') F :=
begin
  refine Z.pullback cont_mdiff_map.fst prod.fst cont_diff_fst prod.fst
    (λ x, rfl) _ (λ e, (image2.some local_homeomorph.prod _ _ e).1) _ _ _ _,
  { simp_rw [model_with_corners_prod_coe, range_prod_map, prod_subset_preimage_fst] },
  { rintro ⟨_, ⟨e₁, e₂, he₁, he₂, rfl⟩⟩ b,
    obtain ⟨e₂', he₂', heq⟩ := image2.some_spec_fst local_homeomorph.prod he₁ he₂,
    exact congr_arg (λ e : local_homeomorph (B × B') (HB × HB'), (e b).1) heq },
  { rintro ⟨_, ⟨e₁, e₂, he₁, he₂, rfl⟩⟩ x,
    obtain ⟨e₂', he₂', heq⟩ := image2.some_spec_fst local_homeomorph.prod he₁ he₂,
    exact congr_arg (λ e : local_homeomorph (B × B') (HB × HB'), (e.symm x).1) heq },
  { rintro ⟨_, ⟨e₁, e₂, he₁, he₂, rfl⟩⟩ b hb,
    obtain ⟨e₂', he₂', heq⟩ := image2.some_spec_fst local_homeomorph.prod he₁ he₂,
    apply_fun (λ e : local_homeomorph (B × B') (HB × HB'), b ∈ e.source) at heq,
    exact (heq.mpr hb).1 },
  { rintro ⟨_, ⟨e₁, e₂, he₁, he₂, rfl⟩⟩ x hx,
    obtain ⟨e₂', he₂', heq⟩ := image2.some_spec_fst local_homeomorph.prod he₁ he₂,
    apply_fun (λ e : local_homeomorph (B × B') (HB × HB'), x ∈ e.target) at heq,
    exact (heq.mpr hx).1 }
end

variables {IB' B'}

lemma pullback_fst.chart_eq
  (x : (Z.pullback_fst B' IB').to_topological_vector_bundle_core.total_space)
  {e : local_homeomorph B HB} {e' : local_homeomorph B' HB'} (he : e ∈ atlas HB B)
  (he' : e' ∈ atlas HB' B') (h : (e.prod e').source.nonempty) :
  (Z.pullback_fst B' IB').chart (mem_image2_of_mem he he') x =
  ((e x.1.1, e' x.1.2), (Z.chart he ⟨x.1.1, x.2⟩).2) :=
begin
  refine (pullback.chart_eq _ Z _ _ x _).trans _,
  { intros b,
    obtain ⟨e₂, he₂, heq⟩ := image2.some_spec_fst local_homeomorph.prod
      (chart_mem_atlas HB b.1) (chart_mem_atlas HB' b.2),
    have h2e₂ : e₂.source.nonempty,
    { have := congr_arg (λ e : local_homeomorph (B × B') (HB × HB'), b ∈ e.source) heq,
      exact ⟨b.2, ((iff_of_eq this).mpr ⟨mem_chart_source HB b.1, mem_chart_source HB' b.2⟩).2⟩ },
    ext1, ext1 x,
    exact congr_arg (λ e : local_homeomorph (B × B') (HB × HB'), (e (x, b.2)).1) heq,
    exact λ y, congr_arg (λ e : local_homeomorph (B × B') (HB × HB'), (e.symm (y, e' b.2)).1) heq,
    have := congr_arg (λ e : local_homeomorph (B × B') (HB × HB'), prod.fst '' e.source) heq,
    simp_rw [local_homeomorph.prod_source, fst_image_prod _ h2e₂,
      fst_image_prod _ ⟨b.2, mem_chart_source HB' b.2⟩] at this,
    exact this },
  { intros b x, refl },
  obtain ⟨e₂, he₂, heq⟩ := image2.some_spec_fst local_homeomorph.prod he he',
  obtain ⟨h₁, h₂⟩ := (prod_eq_prod_of_nonempty' h).mp heq,
  congr'
end

omit Z
variables (IB B)

/-- The pullback of `basic_smooth_vector_bundle_core` along the map `B × B' → B` -/
def pullback_snd (Z : basic_smooth_vector_bundle_core IB' B' F) :
  basic_smooth_vector_bundle_core (IB.prod IB') (B × B') F :=
begin
  refine Z.pullback cont_mdiff_map.snd prod.snd cont_diff_snd prod.snd
    (λ x, rfl) _ (λ e, (image2.some local_homeomorph.prod _ _ e).2) _ _ _ _,
  { simp_rw [model_with_corners_prod_coe, range_prod_map, prod_subset_preimage_snd] },
  { rintro ⟨_, ⟨e₁, e₂, he₁, he₂, rfl⟩⟩ b,
    obtain ⟨e₂', he₂', heq⟩ := image2.some_spec_snd local_homeomorph.prod he₁ he₂,
    exact congr_arg (λ e : local_homeomorph (B × B') (HB × HB'), (e b).2) heq },
  { rintro ⟨_, ⟨e₁, e₂, he₁, he₂, rfl⟩⟩ x,
    obtain ⟨e₂', he₂', heq⟩ := image2.some_spec_snd local_homeomorph.prod he₁ he₂,
    exact congr_arg (λ e : local_homeomorph (B × B') (HB × HB'), (e.symm x).2) heq },
  { rintro ⟨_, ⟨e₁, e₂, he₁, he₂, rfl⟩⟩ b hb,
    obtain ⟨e₂', he₂', heq⟩ := image2.some_spec_snd local_homeomorph.prod he₁ he₂,
    apply_fun (λ e : local_homeomorph (B × B') (HB × HB'), b ∈ e.source) at heq,
    exact (heq.mpr hb).2 },
  { rintro ⟨_, ⟨e₁, e₂, he₁, he₂, rfl⟩⟩ x hx,
    obtain ⟨e₂', he₂', heq⟩ := image2.some_spec_snd local_homeomorph.prod he₁ he₂,
    apply_fun (λ e : local_homeomorph (B × B') (HB × HB'), x ∈ e.target) at heq,
    exact (heq.mpr hx).2 }
end

variables {IB B}


lemma pullback_snd.chart_eq
  (Z : basic_smooth_vector_bundle_core IB' B' F)
  (x : (Z.pullback_snd B IB).to_topological_vector_bundle_core.total_space)
  {e : local_homeomorph B HB} {e' : local_homeomorph B' HB'} (he : e ∈ atlas HB B)
  (he' : e' ∈ atlas HB' B') (h : (e.prod e').source.nonempty) :
  (Z.pullback_snd B IB).chart (mem_image2_of_mem he he') x =
  ((e x.1.1, e' x.1.2), (Z.chart he' ⟨x.1.2, x.2⟩).2) :=
begin
  refine (pullback.chart_eq _ Z _ _ x _).trans _,
  { intros b,
    obtain ⟨e₂, he₂, heq⟩ := image2.some_spec_snd local_homeomorph.prod
      (chart_mem_atlas HB b.1) (chart_mem_atlas HB' b.2),
    have h2e₂ : e₂.source.nonempty,
    { have := congr_arg (λ e : local_homeomorph (B × B') (HB × HB'), b ∈ e.source) heq,
      exact ⟨b.1, ((iff_of_eq this).mpr ⟨mem_chart_source HB b.1, mem_chart_source HB' b.2⟩).1⟩ },
    ext1, ext1 x,
    exact congr_arg (λ e : local_homeomorph (B × B') (HB × HB'), (e (b.1, x)).2) heq,
    exact λ y, congr_arg (λ e₀ : local_homeomorph (B × B') (HB × HB'), (e₀.symm (e b.1, y)).2) heq,
    have := congr_arg (λ e : local_homeomorph (B × B') (HB × HB'), prod.snd '' e.source) heq,
    simp_rw [local_homeomorph.prod_source, snd_image_prod h2e₂,
      snd_image_prod ⟨b.1, mem_chart_source HB b.1⟩] at this,
    exact this },
  { intros b x, refl },
  obtain ⟨e₂, he₂, heq⟩ := image2.some_spec_snd local_homeomorph.prod he he',
  obtain ⟨h₁, h₂⟩ := (prod_eq_prod_of_nonempty' h).mp heq,
  congr'
end

/-!
### Homs of basic smooth vector bundle core
-/

open continuous_linear_map

@[simps] def hom : basic_smooth_vector_bundle_core IB B (F →L[𝕜] F') :=
{ coord_change := λ e e' b,
    compL 𝕜 F F' F' (Z'.coord_change e e' b) ∘L
    (compL 𝕜 F F F').flip (Z.coord_change e' e (e'.1 (e.1.symm b))),
  coord_change_self := λ e x hx L, begin
    ext v,
    simp_rw [comp_apply, flip_apply, compL_apply, comp_apply, e.1.right_inv hx,
      Z.coord_change_self e x hx, Z'.coord_change_self e x hx],
  end,
  coord_change_comp := begin
    intros i j k x hx L,
    ext v,
    simp_rw [comp_apply, flip_apply, compL_apply, comp_apply, Z'.coord_change_comp i j k x hx],
    have h2x := hx,
    simp_rw [trans_source, symm_source, mem_inter_iff, mem_preimage, trans_apply, mem_inter_iff,
      mem_preimage] at hx,
    rw [← Z.coord_change_comp k j i (k.1 (i.1.symm x)) _ v],
    swap, { rw [← j.1.left_inv hx.1.2], apply source_subset_preimage_target h2x },
    simp_rw [trans_apply],
    have := hx.2.2, -- for some reason I cannot rewrite in `hx` directly?
    rw [j.1.left_inv hx.1.2] at this ⊢,
    rw [k.1.left_inv this]
  end,
  coord_change_smooth_clm := begin
    intros i j,
    refine ((compL 𝕜 F F' F').cont_diff.comp_cont_diff_on
      (Z'.coord_change_smooth_clm i j)).clm_comp _,
    refine (compL 𝕜 F F F').flip.cont_diff.comp_cont_diff_on _,
    refine (((Z.coord_change_smooth_clm j i).comp (cont_diff_on_coord_change IB i.2 j.2) _).congr
      _).mono _,
    { rw [@preimage_comp _ _ _ _ IB, IB.preimage_image, @preimage_comp _ _ _ IB.symm],
      exact (inter_subset_left _ _).trans (preimage_mono source_subset_preimage_target) },
    { intros x hx, simp_rw [function.comp_apply, trans_apply, IB.left_inv] },
    { rw [← IB.image_eq] }
  end }

lemma hom.chart_eq
  (x : (Z.hom Z').to_topological_vector_bundle_core.total_space)
  {e : local_homeomorph B HB} (he : e ∈ atlas HB B) :
  (Z.hom Z').chart he x = (e x.1, Z'.coord_change (achart HB x.1) ⟨e, he⟩ (chart_at HB x.1 x.1) ∘L
    x.2 ∘L Z.coord_change ⟨e, he⟩ (achart HB x.1) (e x.1)) :=
by simp_rw [chart, trans_apply, local_homeomorph.prod_apply, trivialization.coe_coe,
  local_homeomorph.refl_apply, function.id_def, topological_vector_bundle_core.local_triv_apply,
  to_topological_vector_bundle_core_coord_change, to_topological_vector_bundle_core_index_at,
  hom_coord_change, comp_apply, flip_apply, compL_apply, ← achart_def,
  (chart_at HB x.1).left_inv (mem_chart_source HB x.1)]

end basic_smooth_vector_bundle_core
