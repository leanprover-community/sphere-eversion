/-
Copyright (c) 2022 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Floris van Doorn
-/
import local.relation
import global.one_jet_bundle

/-!
# Sections of 1-jet bundles

In this file we study sections of 1-jet bundles. This is the direct continuation
of `one_jet_bundle.lean` but it imports more files, hence the cut.

## Main definitions

In this file we consider two manifolds `M` and `M'` with models `I` and `I'`

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

variables (I I' M M')

/-- A section of a 1-jet bundle seen as a bundle over the source manifold. -/
structure one_jet_sec :=
(to_fun : M → one_jet_bundle I M I' M')
(is_sec' : ∀ x : M, (to_fun x).1.1 = x)
(smooth' : smooth I ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) to_fun)

instance : has_coe_to_fun (one_jet_sec I M I' M') (λ S, M → one_jet_bundle I M I' M'):=
⟨one_jet_sec.to_fun⟩

variables {I I' M M'}

namespace one_jet_sec

lemma is_sec (F : one_jet_sec I M I' M') (x : M) : (F x).1.1 = x :=
F.is_sec' x

/-- The base map corresponding to a section of J¹(M, M') → M. -/
def bs (F : one_jet_sec I M I' M') : M → M' :=
λ x, (F x).1.2

lemma fst_eq (F : one_jet_sec I M I' M') (x : M) : (F x).1 = (x, F.bs x) :=
prod.ext (F.is_sec x) rfl

protected lemma smooth (F : one_jet_sec I M I' M') :
  smooth I ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) F :=
F.smooth'

lemma smooth_eta (F : one_jet_sec I M I' M') : smooth I ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E'))
  (λ x, one_jet_bundle.mk x (F.bs x) (F x).2 : M → one_jet_bundle I M I' M') :=
by { convert F.smooth, ext1, rw [one_jet_bundle.mk, ← F.fst_eq x, sigma.eta] }

lemma smooth_bs (F : one_jet_sec I M I' M') : smooth I I' F.bs :=
(smooth_snd.comp $ basic_smooth_vector_bundle_core.smooth_proj _).comp F.smooth

/-- A section of J¹(M, M') is holonomic at (x : M) if its linear map part is the derivative
of its base map at x. -/
def is_holonomic_at (F : one_jet_sec I M I' M') (x : M) : Prop :=
mfderiv I I' (F.bs) x = (F x).2

/-- A section of J¹(M, M') is holonomic at (x : M) iff it coincides with the 1-jet extension of
its base map at x. -/
lemma is_holonomic_at_iff {F : one_jet_sec I M I' M'} {x : M} :
  F.is_holonomic_at x ↔ one_jet_ext I I' F.bs x = F x :=
by simp_rw [is_holonomic_at, one_jet_ext, sigma.ext_iff, heq_iff_eq, F.fst_eq, eq_self_iff_true,
    true_and]

/-- A map from M to J¹(M, M') is holonomic if its linear map part is the derivative
of its base map at every point. -/
def is_holonomic (F : one_jet_sec I M I' M') : Prop :=
∀ x, F.is_holonomic_at x

end one_jet_sec

/-- The one-jet extension of a function, seen as a section of the 1-jet bundle. -/
def one_jet_ext_sec (f : C^∞⟮I, M; I', M'⟯) : one_jet_sec I M I' M' :=
⟨one_jet_ext I I' f, λ x, rfl, f.smooth.one_jet_ext⟩

end general

section real
variables
{E : Type*} [normed_group E] [normed_space ℝ E]
{H : Type*} [topological_space H] (I : model_with_corners ℝ E H)
(M : Type*) [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
{E' : Type*} [normed_group E'] [normed_space ℝ E']
{H' : Type*} [topological_space H'] (I' : model_with_corners ℝ E' H')
(M' : Type*) [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M']
{F : Type*} [normed_group F] [normed_space ℝ F]
{G : Type*} [topological_space G] (J : model_with_corners ℝ F G)
(N : Type*) [topological_space N] [charted_space G N] [smooth_manifold_with_corners J N]
{F' : Type*} [normed_group F'] [normed_space ℝ F']
{G' : Type*} [topological_space G'] (J' : model_with_corners ℝ F' G')
(N' : Type*) [topological_space N'] [charted_space G' N'] [smooth_manifold_with_corners J' N']

/-- A family of jet sections indexed by manifold `N` is a function from `N` into jet sections
  in such a way that the function is smooth as a function of all arguments. -/
structure family_one_jet_sec :=
(to_fun : N → M → one_jet_bundle I M I' M')
(is_sec' : ∀ (t : N) (x : M), (to_fun t x).1.1 = x)
(smooth' : smooth (J.prod I) ((I.prod I').prod 𝓘(ℝ, E →L[ℝ] E')) (uncurry to_fun))

instance : has_coe_to_fun (family_one_jet_sec I M I' M' J N) (λ S, N → one_jet_sec I M I' M') :=
⟨λ S t,
 { to_fun := S.to_fun t,
   is_sec' := S.is_sec' t,
   smooth' := λ x, (S.smooth' (t, x)).comp x $ smooth_at_const.prod_mk smooth_at_id }⟩

namespace family_one_jet_sec

variables {I M I' M' J N J' N'}

/-- Reindex a family along a smooth function `f`. -/
def reindex (S : family_one_jet_sec I M I' M' J' N') (f : C^∞⟮J, N; J', N'⟯) :
  family_one_jet_sec I M I' M' J N :=
{ to_fun := λ t, S (f t),
  is_sec' := λ t, S.is_sec' (f t),
  smooth' := λ x, (S.smooth' (f x.1, x.2)).comp x $ (f.smooth.smooth_at).prod_map' smooth_at_id }

end family_one_jet_sec

/-- A homotopy of formal solutions is a family indexed by `ℝ` -/
abbreviation htpy_one_jet_sec := family_one_jet_sec I M I' M' 𝓘(ℝ, ℝ) ℝ

example : has_coe_to_fun (htpy_one_jet_sec I M I' M') (λ S, ℝ → one_jet_sec I M I' M') :=
by apply_instance

end real
