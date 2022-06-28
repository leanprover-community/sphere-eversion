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

open bundle set topological_space topological_vector_bundle
open_locale classical manifold

variables {𝕜 B B' VB VB' HB HB' : Type*}
variables [nondiscrete_normed_field 𝕜]
variables [normed_group VB] [normed_space 𝕜 VB] [normed_group VB'] [normed_space 𝕜 VB']
variables [topological_space HB] [topological_space HB']
variables {IB : model_with_corners 𝕜 VB HB} (IB' : model_with_corners 𝕜 VB' HB')
variables {F : Type*}
variables [normed_group F] [normed_space 𝕜 F]
variables [topological_space B] [charted_space HB B] [smooth_manifold_with_corners IB B]
variables [topological_space B'] [charted_space HB' B'] [smooth_manifold_with_corners IB' B']
variables (f : C^∞⟮IB', B'; IB, B⟯) -- todo: define cont_mdiff_map_class
variables (Z : basic_smooth_vector_bundle_core IB B F)

namespace basic_smooth_vector_bundle_core

include Z

def pullback (v : VB' → VB) (hv : cont_diff 𝕜 ∞ v)
  (h : HB' → HB)
  (h1v : ∀ x : VB', IB.symm (v x) = h (IB'.symm x))
  (h2v : ∀ x : HB', IB (h x) = v (IB' x))
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
    { simp_rw [local_homeomorph.coe_trans, function.comp_apply, h2g, h1g] },
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
    { simp_rw [model_with_corners.image_eq, local_homeomorph.trans_source, preimage_inter, preimage_preimage, h1v, h2g, ← @preimage_preimage _ _ _ h IB'.symm],
      refine inter_subset_inter (inter_subset_inter (preimage_mono $ hh i) (λ x hx, hf j hx)) _,
      simp_rw [← image_subset_iff, ← @image_univ _ _ IB', image_image, ← h2v, ← image_image IB h,
        image_subset_range] }
  end }

def pullback_fst : basic_smooth_vector_bundle_core (IB.prod IB') (B × B') F :=
begin
  refine Z.pullback (IB.prod IB') cont_mdiff_map.fst prod.fst cont_diff_fst prod.fst
    (λ x, rfl) (λ x, rfl) (λ e, (image2.some local_homeomorph.prod _ _ e).1) _ _ _ _,
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

omit Z

def pullback_snd (Z : basic_smooth_vector_bundle_core IB' B' F) :
  basic_smooth_vector_bundle_core (IB.prod IB') (B × B') F :=
begin
  refine Z.pullback (IB.prod IB') cont_mdiff_map.snd prod.snd cont_diff_snd prod.snd
    (λ x, rfl) (λ x, rfl) (λ e, (image2.some local_homeomorph.prod _ _ e).2) _ _ _ _,
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

end basic_smooth_vector_bundle_core
