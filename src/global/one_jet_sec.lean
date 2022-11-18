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

variables (I M I' M')

/-- A section of a 1-jet bundle seen as a bundle over the source manifold. -/
@[ext] structure one_jet_sec :=
(bs : M → M')
(ϕ : ∀ x : M, tangent_space I x →L[𝕜] tangent_space I' (bs x))
(smooth' : smooth I ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) (λ x, one_jet_bundle.mk x (bs x) (ϕ x)))

instance : has_coe_to_fun (one_jet_sec I M I' M') (λ S, M → one_jet_bundle I M I' M') :=
⟨λ S x, one_jet_bundle.mk x (S.bs x) (S.ϕ x)⟩

variables {I M I' M'}

namespace one_jet_sec

protected def mk' (F : M → one_jet_bundle I M I' M') (hF : ∀ m, (F m).1.1 = m)
  (h2F : smooth I ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) F) : one_jet_sec I M I' M' :=
⟨λ x, (F x).1.2, λ x, (F x).2, by { convert h2F, ext m, exact (hF m).symm, refl, refl }⟩

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
smooth_one_jet_bundle_proj.snd.comp F.smooth

/-- A section of J¹(M, M') is holonomic at (x : M) if its linear map part is the derivative
of its base map at x. -/
def is_holonomic_at (F : one_jet_sec I M I' M') (x : M) : Prop :=
mfderiv I I' (F.bs) x = (F x).2

/-- A section of J¹(M, M') is holonomic at (x : M) iff it coincides with the 1-jet extension of
its base map at x. -/
lemma is_holonomic_at_iff {F : one_jet_sec I M I' M'} {x : M} :
  F.is_holonomic_at x ↔ one_jet_ext I I' F.bs x = F x :=
by simp_rw [is_holonomic_at, one_jet_ext, sigma.ext_iff, heq_iff_eq, F.fst_eq,
  one_jet_bundle_mk_fst, eq_self_iff_true, true_and, one_jet_bundle_mk_snd]

lemma is_holonomic_at.congr {F F' : one_jet_sec I M I' M'} {x : M}
  (hF : F.is_holonomic_at x) (h : F =ᶠ[𝓝 x] F') : F'.is_holonomic_at x :=
begin
  rw [is_holonomic_at] at hF ⊢,
  rw [← h.self_of_nhds, ← hF],
  exact (h.symm.fun_comp (λ x, x.1.2)).mfderiv_eq
end

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
{EP : Type*} [normed_add_comm_group EP] [normed_space ℝ EP]
{HP : Type*} [topological_space HP] {IP : model_with_corners ℝ EP HP}
{P : Type*} [topological_space P] [charted_space HP P] [smooth_manifold_with_corners IP P]

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

protected def mk' (FF : N → M → one_jet_bundle I M I' M') (hF : ∀ n m, (FF n m).1.1 = m)
  (h2F : smooth (J.prod I) ((I.prod I').prod 𝓘(ℝ, E →L[ℝ] E')) (uncurry FF)) :
  family_one_jet_sec I M I' M' J N :=
⟨λ s x, (FF s x).1.2, λ s x, (FF s x).2,
  by { convert h2F, ext ⟨s, m⟩, exact (hF s m).symm, refl, refl }⟩

lemma coe_mk' (FF : N → M → one_jet_bundle I M I' M') (hF : ∀ n m, (FF n m).1.1 = m)
  (h2F : smooth (J.prod I) ((I.prod I').prod 𝓘(ℝ, E →L[ℝ] E')) (uncurry FF)) (x : N) :
  family_one_jet_sec.mk' FF hF h2F x =
  one_jet_sec.mk' (FF x) (hF x) (h2F.comp (smooth_const.prod_mk smooth_id)) :=
rfl

@[simp] lemma bs_eq_coe_bs (S : family_one_jet_sec I M I' M' J N) (s : N) : S.bs s = (S s).bs :=
rfl
lemma bs_eq (S : family_one_jet_sec I M I' M' J N) (s : N) (x : M) : S.bs s x = (S s x).1.2 := rfl
@[simp] lemma coe_ϕ (S : family_one_jet_sec I M I' M' J N) (s : N) : (S s).ϕ = S.ϕ s := rfl

protected lemma smooth (S : family_one_jet_sec I M I' M' J N) :
  smooth (J.prod I) ((I.prod I').prod 𝓘(ℝ, E →L[ℝ] E')) (λ p : N × M, S p.1 p.2) := S.smooth'

lemma smooth_bs (S : family_one_jet_sec I M I' M' J N) :
  smooth (J.prod I) I' (λ p : N × M, S.bs p.1 p.2) :=
smooth_one_jet_bundle_proj.snd.comp S.smooth

lemma _root_.smooth_at.family_one_jet_sec_bs {S : family_one_jet_sec I M I' M' J N}
  {f : N' → N} {g : N' → M} {z : N'} (hf : smooth_at J' J f z) (hg : smooth_at J' I g z) :
  smooth_at J' I' (λ z, S.bs (f z) (g z)) z :=
(S.smooth_bs _).comp z (hf.prod_mk hg)

lemma smooth_coe_bs (S : family_one_jet_sec I M I' M' J N) {p : N} : smooth I I' (S.bs p) :=
(S p).smooth_bs

/-- Reindex a family along a smooth function `f`. -/
def reindex (S : family_one_jet_sec I M I' M' J' N') (f : C^∞⟮J, N; J', N'⟯) :
  family_one_jet_sec I M I' M' J N :=
{ bs := λ t, S.bs (f t),
  ϕ := λ t, S.ϕ (f t),
  smooth' := λ x, (S.smooth' (f x.1, x.2)).comp x $ (f.smooth.smooth_at).prod_map' smooth_at_id }

/-- Turn a family of sections of `J¹(M, M')` parametrized by `N` into a section of `J¹(N × M, M')`.
-/
@[simps]
def uncurry (S : family_one_jet_sec I M I' M' IP P) : one_jet_sec (IP.prod I) (P × M) I' M' :=
{ bs := λ p, S.bs p.1 p.2,
  ϕ := λ p, (show EP × E →L[ℝ] E', from mfderiv (IP.prod I) I' (λ z : P × M, S.bs z.1 p.2) p) +
    S.ϕ p.1 p.2 ∘L mfderiv (IP.prod I) I prod.snd p,
  smooth' := begin
    refine smooth.one_jet_add _ _,
    { intro y,
      refine smooth_at_id.one_jet_bundle_mk (S.smooth_bs y) _,
      have : smooth_at ((IP.prod I).prod (IP.prod I)) I'
        (function.uncurry (λ x z : P × M, S.bs z.1 x.2)) (y, y),
      { exact S.smooth_bs.comp (smooth_snd.fst.prod_mk smooth_fst.snd) (y, y) },
      apply cont_mdiff_at.mfderiv'' (λ x z : P × M, S.bs z.1 x.2) this le_top },
    { refine smooth.one_jet_comp I (λ p, p.2) S.smooth smooth_snd.one_jet_ext }
  end }

lemma uncurry_ϕ' (S : family_one_jet_sec I M I' M' IP P) (p : P × M) :
  (S.uncurry).ϕ p = mfderiv IP I' (λ z, S.bs z p.2) p.1 ∘L continuous_linear_map.fst ℝ EP E +
  S.ϕ p.1 p.2 ∘L continuous_linear_map.snd ℝ EP E :=
begin
  simp_rw [S.uncurry_ϕ, mfderiv_snd],
  congr' 1,
  convert mfderiv_comp p
    ((S.smooth_bs.comp (smooth_id.prod_mk smooth_const)).mdifferentiable p.1)
    (smooth_fst.mdifferentiable p),
  simp_rw [mfderiv_fst],
end

lemma is_holonomic_uncurry (S : family_one_jet_sec I M I' M' IP P) {p : P × M} :
  S.uncurry.is_holonomic_at p ↔ (S p.1).is_holonomic_at p.2 :=
begin
  simp_rw [one_jet_sec.is_holonomic_at, one_jet_sec.snd_eq, S.uncurry_ϕ],
  rw [show S.uncurry.bs = λ x, S.uncurry.bs x, from rfl, funext S.uncurry_bs],
  simp_rw [mfderiv_prod_eq_add (S.smooth_bs.mdifferentiable _), mfderiv_snd, add_right_inj],
  dsimp only,
  rw [mfderiv_comp p S.smooth_coe_bs.mdifferentiable_at smooth_snd.mdifferentiable_at, mfderiv_snd,
    (show surjective (continuous_linear_map.snd ℝ EP E), from prod.snd_surjective)
      .clm_comp_injective.eq_iff],
  refl
end

end family_one_jet_sec

/-- A homotopy of 1-jet sections is a family of 1-jet sections indexed by `ℝ` -/
@[reducible] def htpy_one_jet_sec := family_one_jet_sec I M I' M' 𝓘(ℝ, ℝ) ℝ

example : has_coe_to_fun (htpy_one_jet_sec I M I' M') (λ S, ℝ → one_jet_sec I M I' M') :=
by apply_instance

end real
