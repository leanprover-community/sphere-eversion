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
  (hvh : ∀ x : VB', IB.symm (v x) = h (IB'.symm x))
  (g : atlas HB' B' → atlas HB B)
  (hg : ∀ (e : atlas HB' B') (b : B'), (g e).1 (f b) = h (e.1 b))
  (hh : ∀ (e : atlas HB' B'), maps_to h e.1.target (g e).1.target)
  (hgh : ∀ (e e' : atlas HB' B') (x : HB'), -- probably only some x
    h (e'.1 (e.1.symm x)) = (g e').1 ((g e).1.symm (h x))) :
  basic_smooth_vector_bundle_core IB' B' F :=
{ coord_change := λ e e' b, Z.coord_change (g e) (g e') (h b),
  coord_change_self := λ e x hx v, Z.coord_change_self (g e) (h x) (hh e hx) v,
  coord_change_comp := begin
    intros i j k x hx v,
    rw [← Z.coord_change_comp (g i) (g j) (g k) (h x) _ v],
    simp_rw [local_homeomorph.coe_trans, function.comp_apply, hgh],
    simp only with mfld_simps at hx ⊢,
    refine ⟨⟨hh i hx.1.1, _⟩, ⟨_, _⟩⟩,
    all_goals { sorry },

  end,
  coord_change_smooth_clm := begin
    intros i j,
    have := (Z.coord_change_smooth_clm (g i) (g j)).comp hv.cont_diff_on subset.rfl,
    convert this,
    ext1 b, simp_rw [function.comp_apply, hvh],
    sorry
  end }




def pullback_fst : basic_smooth_vector_bundle_core (IB.prod IB') (B × B') F :=
begin
  refine Z.pullback (IB.prod IB') cont_mdiff_map.fst prod.fst cont_diff_fst prod.fst
    (λ x, rfl) (λ e, (image2.some local_homeomorph.prod _ _ e).1) _ _ _,
  { rintro ⟨_, ⟨e₁, e₂, he₁, he₂, rfl⟩⟩ b,
    obtain ⟨e₂', he₂', heq⟩ := image2.some_spec_fst local_homeomorph.prod he₁ he₂,
    exact congr_arg (λ e : local_homeomorph (B × B') (HB × HB'), (e b).1) heq },
  { rintro ⟨_, ⟨e₁, e₂, he₁, he₂, rfl⟩⟩ b hb,
    obtain ⟨e₂', he₂', heq⟩ := image2.some_spec_fst local_homeomorph.prod he₁ he₂,
    apply_fun (λ e : local_homeomorph (B × B') (HB × HB'), b ∈ e.target) at heq,
    simp at heq,
    sorry
    -- exact congr_arg (λ e : local_homeomorph (B × B') (HB × HB'), (e (b, b')).1) heq
    },
  { sorry }
end

end basic_smooth_vector_bundle_core
