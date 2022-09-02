/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import global.one_jet_sec

noncomputable theory

open set equiv
open_locale manifold

section arbitrary_field

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
  {H : Type*} [topological_space H]
  (I : model_with_corners 𝕜 E H)
  (M : Type*) [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
  (V : Type*) [normed_add_comm_group V] [normed_space 𝕜 V]
  (V' : Type*) [normed_add_comm_group V'] [normed_space 𝕜 V']

/- Given a smooth manifold `M` and a normed space `V`, the total space of the bundle Hom(TM, V) of
homomorphisms from TM to V. This is naturally a smooth manifold. -/
local notation `J¹MV` :=
topological_vector_bundle_core.total_space $
basic_smooth_vector_bundle_core.to_topological_vector_bundle_core $
(tangent_bundle_core I M).hom (trivial_basic_smooth_vector_bundle_core I M V)

section sections

/-- A section of a 1-jet bundle seen as a bundle over the source manifold. -/
@[ext] structure one_jet_eucl_sec :=
(to_fun : M → J¹MV)
(is_sec' : ∀ p, (to_fun p).1 = p)
(smooth' : smooth I (I.prod 𝓘(𝕜, E →L[𝕜] V)) to_fun)

variables {I M V}

instance : has_coe_to_fun (one_jet_eucl_sec I M V) (λ S, M → J¹MV) :=
⟨λ S x, S.to_fun x⟩

@[simp] lemma one_jet_eucl_sec.is_sec (s : one_jet_eucl_sec I M V) (p : M) : (s p).1 = p :=
s.is_sec' p

@[simp] lemma one_jet_eucl_sec.smooth (s : one_jet_eucl_sec I M V) :
  smooth I (I.prod 𝓘(𝕜, E →L[𝕜] V)) s :=
s.smooth'


end sections

section proj

/- Given a smooth manifold `M` and a normed space `V`, there is a canonical projection from the
one-jet bundle of maps from `M` to `V` to the bundle of homomorphisms from `TM` to `V`. This is
constructed using the fact that each tangent space to `V` is canonically isomorphic to `V`. -/
def proj (v : one_jet_bundle I M 𝓘(𝕜, V) V) : J¹MV :=
⟨v.1.1, v.2⟩

lemma smooth_proj :
  smooth ((I.prod 𝓘(𝕜, V)).prod 𝓘(𝕜, E →L[𝕜] V)) (I.prod 𝓘(𝕜, E →L[𝕜] V)) (proj I M V) :=
sorry -- nontrivially exploits triviality of tangent bundles to `V`

variables {I M V}

def drop (s : one_jet_sec I M 𝓘(𝕜, V) V) : one_jet_eucl_sec I M V :=
{ to_fun := (proj I M V).comp s,
  is_sec' := λ p, rfl,
  smooth' := (smooth_proj I M V).comp s.smooth }

end proj

section incl

/- Given a smooth manifold `M` and a normed space `V`, there is a canonical map from the
the product with V of the bundle of homomorphisms from `TM` to `V` to the one-jet bundle of maps
from `M` to `V`. In fact this map is a diffeomorphism.  This is constructed using the fact that each
tangent space to `V` is canonically isomorphic to `V`. -/
def incl (v : J¹MV × V) : one_jet_bundle I M 𝓘(𝕜, V) V :=
⟨(v.1.1, v.2), v.1.2⟩

lemma smooth_incl :
  smooth
    ((I.prod 𝓘(𝕜, E →L[𝕜] V)).prod 𝓘(𝕜, V))
    ((I.prod 𝓘(𝕜, V)).prod 𝓘(𝕜, E →L[𝕜] V))
    (incl I M V) :=
sorry -- nontrivially exploits triviality of tangent bundles to `V`

@[simp] lemma incl_fst_fst (v : J¹MV × V) : (incl I M V v).1.1 = v.1.1 := rfl
@[simp] lemma incl_snd (v : J¹MV × V) : (incl I M V v).1.2 = v.2 := rfl

end incl

end arbitrary_field

section family_twist
variables
  {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
  {H : Type*} [topological_space H] (I : model_with_corners ℝ E H)
  (M : Type*) [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
  (V : Type*) [normed_add_comm_group V] [normed_space ℝ V]
  (V' : Type*) [normed_add_comm_group V'] [normed_space ℝ V']
  {F : Type*} [normed_add_comm_group F] [normed_space ℝ F]
  {G : Type*} [topological_space G] (J : model_with_corners ℝ F G)
  (N : Type*) [topological_space N] [charted_space G N] [smooth_manifold_with_corners J N]

local notation `J¹MV` :=
topological_vector_bundle_core.total_space $
basic_smooth_vector_bundle_core.to_topological_vector_bundle_core $
(tangent_bundle_core I M).hom (trivial_basic_smooth_vector_bundle_core I M V)

/-- A section of a 1-jet bundle seen as a bundle over the source manifold. -/
@[ext] structure family_one_jet_eucl_sec :=
(to_fun : N × M → J¹MV)
(is_sec' : ∀ p, (to_fun p).1 = p.2)
(smooth' : smooth (J.prod I) (I.prod 𝓘(ℝ, E →L[ℝ] V)) to_fun)

instance : has_coe_to_fun (family_one_jet_eucl_sec I M V J N) (λ S, N × M → J¹MV) :=
⟨λ S x, S.to_fun x⟩

variables {I M V J N}

@[simp] lemma family_one_jet_eucl_sec.is_sec (s : family_one_jet_eucl_sec I M V J N) (p : N × M) :
  (s p).1 = p.2 :=
s.is_sec' p

@[simp] lemma family_one_jet_eucl_sec.smooth (s : family_one_jet_eucl_sec I M V J N) :
  smooth (J.prod I) (I.prod 𝓘(ℝ, E →L[ℝ] V)) s :=
s.smooth'

variables {I M V J N V'}

def family_join
  {f : N × M → V}
  (hf : smooth (J.prod I) 𝓘(ℝ, V) f)
  (s : family_one_jet_eucl_sec I M V J N) :
  family_one_jet_sec I M 𝓘(ℝ, V) V J N :=
{ bs := λ n m, (incl I M V (s (n, m), f (n, m))).1.2,
  ϕ := λ n m, (incl I M V (s (n, m), f (n, m))).2,
  smooth' := begin
    convert (smooth_incl I M V).comp (s.smooth.prod_mk hf),
    ext p,
    { simp },
    { simp },
    have : (p.1, p.2) = p := prod.ext rfl rfl,
    rw [this],
    simp,
  end }

@[simp] lemma family_join_bs
  {f : N × M → V}
  (hf : smooth (J.prod I) 𝓘(ℝ, V) f)
  (s : family_one_jet_eucl_sec I M V J N) (n : N) (m : M) :
  (family_join hf s n).bs m = f (n, m) :=
rfl

def family_twist
  (s : one_jet_eucl_sec I M V)
  (i : N × M → (V →L[ℝ] V'))
  (i_smooth : smooth (J.prod I) 𝓘(ℝ, V →L[ℝ] V') i) :
  family_one_jet_eucl_sec I M V' J N :=
{ to_fun := λ p, ⟨p.2, (i p).comp (s p.2).2⟩,
  is_sec' := λ p, rfl,
  smooth' := sorry } -- nontrivially exploits triviality of tangent bundles to `V`

end family_twist
