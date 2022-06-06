/-
Copyright (c) 2022 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import geometry.manifold.cont_mdiff

import local.relation
import global.one_jet_bundle

/-!
# Sections of 1-jet bundles

In this file we study sections of 1-jet bundles. This is the direct continuation
of `one_jet_bundle.lean` but it imports more things more mathlib, hence the cut.


## Main definitions

In this file we consider two manifolds `M` and `M'` with models `I` and `I'`

* `one_jet_ext I M I' M' f`: the 1-jet extension of a map `f : M → M'`
* `one_jet_sec I M I' M'`: smooth sections of `one_jet_bundle I M I' M' → M`
-/

noncomputable theory

open set function filter charted_space smooth_manifold_with_corners
open_locale topological_space manifold

section general

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
-- declare a smooth manifold `M` over the pair `(E, H)`.
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{H : Type*} [topological_space H] (I : model_with_corners 𝕜 E H)
{M : Type*} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
-- declare a smooth manifold `M'` over the pair `(E', H')`.
{E' : Type*} [normed_group E'] [normed_space 𝕜 E']
{H' : Type*} [topological_space H'] (I' : model_with_corners 𝕜 E' H')
{M' : Type*} [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M']

/-- The one-jet extension of a function -/
def one_jet_ext (f : M → M') : M → one_jet_bundle I M I' M' :=
λ x, ⟨(x, f x), (mfderiv I I' f x : tangent_space I x →L[𝕜] tangent_space I' (f x))⟩

@[simp, mfld_simps] lemma one_jet_ext_one_jet_bundle_proj {f : M → M'} {x :  M} :
  one_jet_bundle.proj I M I' M' (one_jet_ext I I' f x) = (x, f x) := rfl

@[simp, mfld_simps] lemma one_jet_ext_proj {f : M → M'} {x :  M} :
  (one_jet_ext I I' f x).1 = (x, f x) := rfl

variables (I I' M M')

/-- A section of a 1-jet bundle seen as a bundle over the source manifold. -/
structure one_jet_sec :=
(to_fun : M → one_jet_bundle I M I' M')
(is_sec' : ∀ x : M, (to_fun x).1.1 = x)
(smooth' : cont_mdiff I ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) ⊤ to_fun)

instance : has_coe_to_fun (one_jet_sec I M I' M') (λ S, M → one_jet_bundle I M I' M'):=
⟨one_jet_sec.to_fun⟩

variables {I I' M M'}

lemma one_jet_sec.is_sec (F : one_jet_sec I M I' M') (x : M) : (F x).1.1 = x :=
F.is_sec' x

lemma one_jet_sec.smooth (F : one_jet_sec I M I' M') :
  cont_mdiff I ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) ⊤  F :=
F.smooth'

/-- The base map corresponding to a section of J¹(M, M') → M. -/
def one_jet_sec.bs (F : one_jet_sec I M I' M') : M → M' :=
λ x, (F x).1.2

/-- A section of J¹(M, M') is holonomic at (x : M) if its linear map part is the derivative
of its base map at x. -/
def one_jet_sec.is_holonomic_at (F : one_jet_sec I M I' M') (x : M) : Prop :=
mfderiv I I' (F.bs) x = (F x).2

/-- A section of J¹(M, M') is holonomic at (x : M) iff it coincides with the 1-jet extension of
its base map at x. -/
lemma one_jet_sec.is_holonomic_at_iff {F : one_jet_sec I M I' M'} {x : M} :
  F.is_holonomic_at x ↔ one_jet_ext I I' F.bs x = F x :=
begin
  dsimp only [one_jet_sec.is_holonomic_at, one_jet_ext],
  split,
  { intros h,
    ext,
    { rw F.is_sec x },
    { refl },
    { rw h } },
  { intros h,
    rw ← h },
end

/-- A map from M to J¹(M, M') is holonomic if its linear map part is the derivative
of its base map at every point. -/
def one_jet_sec.is_holonomic (F : one_jet_sec I M I' M') : Prop :=
∀ x, F.is_holonomic_at x

end general
