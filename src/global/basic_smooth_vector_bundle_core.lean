/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import geometry.manifold.cont_mdiff_map

noncomputable theory

open set equiv
open_locale manifold

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {F : Type*} [normed_group F] [normed_space 𝕜 F]
  {H : Type*} [topological_space H]
  (I : model_with_corners 𝕜 F H)
  (M : Type*) [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
  {F' : Type*} [normed_group F'] [normed_space 𝕜 F']
  {H' : Type*} [topological_space H']
  (I' : model_with_corners 𝕜 F' H')
  (M' : Type*) [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M']

def pullback (f : C^∞⟮I, M; I', M'⟯) (Z : basic_smooth_vector_bundle_core I' M' F) :
  basic_smooth_vector_bundle_core I M F :=
/- oh, this is really annoying, since the atlas in the domain might be a lot coarser than the one in
the codomain -/
sorry
