/-
Copyright (c) 2022 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
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

variables {I I'}

@[simp, mfld_simps] lemma one_jet_ext_one_jet_bundle_proj {f : M → M'} {x :  M} :
  one_jet_bundle.proj I M I' M' (one_jet_ext I I' f x) = (x, f x) := rfl

@[simp, mfld_simps] lemma one_jet_ext_proj {f : M → M'} {x :  M} :
  (one_jet_ext I I' f x).1 = (x, f x) := rfl

open basic_smooth_vector_bundle_core
def model_with_corners.simps.apply (𝕜 : Type*) [nondiscrete_normed_field 𝕜]
  (E : Type*) [normed_group E] [normed_space 𝕜 E] (H : Type*) [topological_space H]
  (I : model_with_corners 𝕜 E H) : H → E := I

def model_with_corners.simps.symm_apply (𝕜 : Type*) [nondiscrete_normed_field 𝕜]
  (E : Type*) [normed_group E] [normed_space 𝕜 E] (H : Type*) [topological_space H]
  (I : model_with_corners 𝕜 E H) : E → H := I.symm

initialize_simps_projections model_with_corners
  (to_local_equiv_to_fun → apply, to_local_equiv_inv_fun → symm_apply,
   to_local_equiv_source → source, to_local_equiv_target → target, -to_local_equiv)

attribute [simps] model_with_corners.prod

lemma smooth_one_jet_ext {f : M → M'} (hf : smooth I I' f) :
  smooth I ((I.prod I').prod 𝓘(𝕜, E →L[𝕜] E')) (one_jet_ext I I' f) :=
begin
  intro x,
  rw [(one_jet_bundle_core I M I' M').cont_mdiff_at_iff_target],
  refine ⟨continuous_at_id.prod (hf x).continuous_at, _⟩,
  simp_rw [ext_chart_at, local_equiv.coe_trans, function.comp, to_charted_space_chart_at],
  dsimp only [one_jet_bundle_core],
  simp_rw [local_homeomorph.coe_coe, hom_chart, ← achart_def, pullback_fst_coord_change_at,
    pullback_snd_coord_change_at, model_with_corners.to_local_equiv_coe,
    model_with_corners.prod_apply, model_with_corners_self_coe, id, prod_charted_space_chart_at,
    local_homeomorph.prod_apply],
  refine (cont_mdiff_at_ext_chart_at.prod_mk_space $ cont_mdiff_at_ext_chart_at.comp _ (hf x))
    .prod_mk_space _,
  refine cont_mdiff_at.clm_comp _ ((hf.mfderiv x).clm_comp _),
  { exact (hf x).coord_change'' (tangent_bundle_core I' M') cont_mdiff_at_const (hf x) rfl },
  { exact cont_mdiff_at_const.coord_change'' (tangent_bundle_core I M) cont_mdiff_at_id
      cont_mdiff_at_id rfl }
end

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

/-- The one-jet extension of a function, seen as a section of the 1-jet bundle. -/
def one_jet_ext_sec (f : C^∞⟮I, M; I', M'⟯) : one_jet_sec I M I' M' :=
⟨one_jet_ext I I' f, λ x, rfl, smooth_one_jet_ext f.smooth⟩

end general

section real
variables
{E : Type*} [normed_group E] [normed_space ℝ E]
{H : Type*} [topological_space H] (I : model_with_corners ℝ E H)
(M : Type*) [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
{E' : Type*} [normed_group E'] [normed_space ℝ E']
{H' : Type*} [topological_space H'] (I' : model_with_corners ℝ E' H')
(M' : Type*) [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M']


structure htpy_one_jet_sec :=
(to_fun : ℝ → M → one_jet_bundle I M I' M')
(is_sec' : ∀ (t : ℝ) (x : M), (to_fun t x).1.1 = x)
(smooth' : cont_mdiff (𝓘(ℝ, ℝ).prod I) ((I.prod I').prod 𝓘(ℝ, E →L[ℝ] E')) ⊤ (uncurry to_fun))

instance : has_coe_to_fun (htpy_one_jet_sec I M I' M') (λ S, ℝ → one_jet_sec I M I' M') :=
⟨λ S t,
 { to_fun := S.to_fun t,
   is_sec' := S.is_sec' t,
   smooth' := begin
     intros x,
     apply cont_mdiff_at.comp x (S.smooth' (t, x)),
     sorry
   end }⟩
end real
