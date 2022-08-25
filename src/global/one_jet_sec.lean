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

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
-- declare a smooth manifold `M` over the pair `(E, H)`.
{E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
{H : Type*} [topological_space H] (I : model_with_corners 𝕜 E H)
{M : Type*} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
-- declare a smooth manifold `M'` over the pair `(E', H')`.
{E' : Type*} [normed_add_comm_group E'] [normed_space 𝕜 E']
{H' : Type*} [topological_space H'] (I' : model_with_corners 𝕜 E' H')
{M' : Type*} [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M']

variables (I I' M M')

/-- A section of a 1-jet bundle seen as a bundle over the source manifold. -/
structure one_jet_sec :=
(bs : M → M')
(ϕ : ∀ x : M, tangent_space I x →L[𝕜] tangent_space I' (bs x))
(smooth' : smooth I ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) (λ x, one_jet_bundle.mk x (bs x) (ϕ x)))

instance : has_coe_to_fun (one_jet_sec I M I' M') (λ S, M → one_jet_bundle I M I' M') :=
⟨λ S x, one_jet_bundle.mk x (S.bs x) (S.ϕ x)⟩

variables {I I' M M'}

namespace one_jet_sec

lemma coe_apply (F : one_jet_sec I M I' M') (x : M) : F x = ⟨(x, F.bs x), (F.ϕ x)⟩ := rfl
lemma fst_eq (F : one_jet_sec I M I' M') (x : M) : (F x).1 = (x, F.bs x) := rfl
lemma snd_eq (F : one_jet_sec I M I' M') (x : M) : (F x).2 = F.ϕ x := rfl
lemma is_sec (F : one_jet_sec I M I' M') (x : M) : (F x).1.1 = x := rfl
lemma bs_eq (F : one_jet_sec I M I' M') (x : M) : F.bs x = (F x).1.2 := rfl

protected lemma smooth (F : one_jet_sec I M I' M') :
  smooth I ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) F :=
F.smooth'

lemma smooth_eta (F : one_jet_sec I M I' M') : smooth I ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E'))
  (λ x, one_jet_bundle.mk x (F.bs x) (F x).2 : M → one_jet_bundle I M I' M') :=
F.smooth

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
⟨f, mfderiv I I' f, f.smooth.one_jet_ext⟩

end general

section real
variables
{E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
{H : Type*} [topological_space H] (I : model_with_corners ℝ E H)
(M : Type*) [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
{E' : Type*} [normed_add_comm_group E'] [normed_space ℝ E']
{H' : Type*} [topological_space H'] (I' : model_with_corners ℝ E' H')
(M' : Type*) [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M']
{F : Type*} [normed_add_comm_group F] [normed_space ℝ F]
{G : Type*} [topological_space G] (J : model_with_corners ℝ F G)
(N : Type*) [topological_space N] [charted_space G N] [smooth_manifold_with_corners J N]
{F' : Type*} [normed_add_comm_group F'] [normed_space ℝ F']
{G' : Type*} [topological_space G'] (J' : model_with_corners ℝ F' G')
(N' : Type*) [topological_space N'] [charted_space G' N'] [smooth_manifold_with_corners J' N']

/-- A family of jet sections indexed by manifold `N` is a function from `N` into jet sections
  in such a way that the function is smooth as a function of all arguments. -/
structure family_one_jet_sec :=
(bs : N → M → M')
(ϕ : ∀ (n : N) (m : M), tangent_space I m →L[ℝ] tangent_space I' (bs n m))
(smooth' : smooth (J.prod I) ((I.prod I').prod 𝓘(ℝ, E →L[ℝ] E'))
  (λ p : N × M, one_jet_bundle.mk p.2 (bs p.1 p.2) (ϕ p.1 p.2)))

instance : has_coe_to_fun (family_one_jet_sec I M I' M' J N) (λ S, N → one_jet_sec I M I' M') :=
⟨λ S t,
 { bs := S.bs t,
   ϕ := S.ϕ t,
   smooth' := λ x, (S.smooth' (t, x)).comp x $ smooth_at_const.prod_mk smooth_at_id }⟩

namespace family_one_jet_sec

variables {I M I' M' J N J' N'}

protected lemma smooth (S : family_one_jet_sec I M I' M' J N) :
  smooth (J.prod I) ((I.prod I').prod 𝓘(ℝ, E →L[ℝ] E')) (λ p : N × M, S p.1 p.2) := S.smooth'

lemma smooth_bs (S : family_one_jet_sec I M I' M' J N) :
  smooth (J.prod I) I' (λ p : N × M, S.bs p.1 p.2) :=
(smooth_snd.comp $ basic_smooth_vector_bundle_core.smooth_proj _).comp S.smooth

/-- Reindex a family along a smooth function `f`. -/
def reindex (S : family_one_jet_sec I M I' M' J' N') (f : C^∞⟮J, N; J', N'⟯) :
  family_one_jet_sec I M I' M' J N :=
{ bs := λ t, S.bs (f t),
  ϕ := λ t, S.ϕ (f t),
  smooth' := λ x, (S.smooth' (f x.1, x.2)).comp x $ (f.smooth.smooth_at).prod_map' smooth_at_id }

/-- Turn a family of sections of `J¹(M, M')` parametrized by `N` into a section of `J¹(N × M, M')`.
-/
def uncurry (S : family_one_jet_sec I M I' M' J N) : one_jet_sec (J.prod I) (N × M) I' M' :=
{ bs := λ p, S.bs p.1 p.2,
  ϕ := λ p, mfderiv J I' (λ z, S.bs z p.2) p.1 ∘L mfderiv (J.prod I) J prod.fst p +
    S.ϕ p.1 p.2 ∘L mfderiv (J.prod I) I prod.snd p,
  smooth' := begin
    refine smooth.one_jet_add _ _,
    { refine smooth.one_jet_comp J (λ p, p.1) _ smooth_fst.one_jet_ext,
      -- have := S.smooth_bs.comp (smooth_id.prod_mk smooth_const), dsimp [function.comp] at this,
      -- have := smooth.one_jet_ext this,
      sorry
       },
    { refine smooth.one_jet_comp I (λ p, p.2) S.smooth smooth_snd.one_jet_ext,
      -- exact S.smooth.comp (smooth_snd.prod_mk smooth_fst)
      }
  end  }

/- -- attempted version with one one `mfderiv` left of addition
def uncurry (S : family_one_jet_sec I M I' M' J N) : one_jet_sec (I.prod J) (M × N) I' M' :=
{ bs := λ p, S.bs p.2 p.1,
  ϕ := λ p, (mfderiv (I.prod J) I' (λ z : M × N, S.bs z.2 p.1) p : _) +
    S.ϕ p.2 p.1 ∘L mfderiv (I.prod J) I prod.fst p,
  smooth' := begin
    refine smooth.one_jet_add _ _,
    { refine smooth.one_jet_ext _, -- nope
     },
    { refine smooth.one_jet_comp I (λ p, p.1) _ smooth_fst.one_jet_ext,
      exact S.smooth.comp (smooth_snd.prod_mk smooth_fst) }
  end  }

-/

lemma is_holonomic_uncurry (S : family_one_jet_sec I M I' M' J N) {p : N × M} :
  S.uncurry.is_holonomic_at p ↔ (S p.1).is_holonomic_at p.2 :=
sorry

end family_one_jet_sec

/-- A homotopy of formal solutions is a family indexed by `ℝ` -/
@[reducible] def htpy_one_jet_sec := family_one_jet_sec I M I' M' 𝓘(ℝ, ℝ) ℝ

example : has_coe_to_fun (htpy_one_jet_sec I M I' M') (λ S, ℝ → one_jet_sec I M I' M') :=
by apply_instance

end real
