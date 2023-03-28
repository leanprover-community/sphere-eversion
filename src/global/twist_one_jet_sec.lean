/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import global.one_jet_sec

noncomputable theory

open set equiv bundle
open_locale manifold bundle topology

section arbitrary_field

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
  {H : Type*} [topological_space H] (I : model_with_corners 𝕜 E H)
  (M : Type*) [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
  {F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]
  {G : Type*} [topological_space G] {J : model_with_corners 𝕜 F G}
  {N : Type*} [topological_space N] [charted_space G N] [smooth_manifold_with_corners J N]
  (V : Type*) [normed_add_comm_group V] [normed_space 𝕜 V]
  (V' : Type*) [normed_add_comm_group V'] [normed_space 𝕜 V']

/- Given a smooth manifold `M` and a normed space `V`, the total space of the bundle Hom(TM, V) of
homomorphisms from TM to V. This is naturally a smooth manifold. -/
local notation `σ` := ring_hom.id 𝕜
local notation `FJ¹MV` :=
  bundle.continuous_linear_map σ E (tangent_space I : M → Type*) V (bundle.trivial M V)
local notation `J¹MV` := total_space FJ¹MV

section smoothness

variables {I M V} {f : N → J¹MV}

-- todo: remove or use to prove `smooth_at_one_jet_eucl_bundle`
lemma smooth_at_one_jet_eucl_bundle' {x₀ : N} :
  smooth_at J (I.prod 𝓘(𝕜, E →L[𝕜] V)) f x₀ ↔
  smooth_at J I (λ x, (f x).1) x₀ ∧
  smooth_at J 𝓘(𝕜, E →L[𝕜] V) (λ x, show E →L[𝕜] V, from
    (f x).2 ∘L (trivialization_at E (tangent_space I : M → Type*) (f x₀).1).symmL 𝕜 (f x).1) x₀ :=
begin
  convert smooth_at_hom_bundle I,
  ext1 x,
  dsimp only,
  simp_rw [in_coordinates', trivial.trivialization_at,
    trivial.trivialization_continuous_linear_map_at],
  exact (continuous_linear_map.id_comp _).symm
end

lemma smooth_at_one_jet_eucl_bundle {x₀ : N} :
  smooth_at J (I.prod 𝓘(𝕜, E →L[𝕜] V)) f x₀ ↔
  smooth_at J I (λ x, (f x).1) x₀ ∧
  smooth_at J 𝓘(𝕜, E →L[𝕜] V) (λ x, show E →L[𝕜] V, from (f x).2 ∘L
    (tangent_bundle_core I M).coord_change (achart H (f x₀).proj) (achart H (f x).proj) (f x).proj)
    x₀ :=
begin
  rw [smooth_at_hom_bundle I, and.congr_right_iff],
  intros hf,
  refine filter.eventually_eq.cont_mdiff_at_iff _,
  have := hf.continuous_at.preimage_mem_nhds
    (((tangent_bundle_core I M).is_open_base_set (achart H (f x₀).proj)).mem_nhds
    ((tangent_bundle_core I M).mem_base_set_at (f x₀).proj)),
  filter_upwards [this] with x hx,
  simp_rw [in_coordinates', trivial.trivialization_at,
    trivial.trivialization_continuous_linear_map_at, ← continuous_linear_map.comp_assoc],
  congr' 1,
  { apply continuous_linear_map.id_comp },
  exact (tangent_bundle_core I M).local_triv_symmL hx
end

lemma smooth_at.one_jet_eucl_bundle_mk' {f : N → M} {ϕ : N → E →L[𝕜] V} {x₀ : N}
  (hf : smooth_at J I f x₀)
  (hϕ : smooth_at J 𝓘(𝕜, E →L[𝕜] V) (λ x, show E →L[𝕜] V, from
    ϕ x ∘L (trivialization_at E (tangent_space I : M → Type*) (f x₀)).symmL 𝕜 (f x)) x₀) :
  smooth_at J (I.prod 𝓘(𝕜, E →L[𝕜] V)) (λ x, bundle.total_space_mk (f x) (ϕ x) : N → J¹MV) x₀ :=
smooth_at_one_jet_eucl_bundle'.mpr ⟨hf, hϕ⟩

lemma smooth_at.one_jet_eucl_bundle_mk {f : N → M} {ϕ : N → E →L[𝕜] V} {x₀ : N}
  (hf : smooth_at J I f x₀)
  (hϕ : smooth_at J 𝓘(𝕜, E →L[𝕜] V) (λ x, show E →L[𝕜] V, from
    ϕ x ∘L (tangent_bundle_core I M).coord_change (achart H (f x₀)) (achart H (f x))
    (f x)) x₀) :
  smooth_at J (I.prod 𝓘(𝕜, E →L[𝕜] V)) (λ x, bundle.total_space_mk (f x) (ϕ x) : N → J¹MV) x₀ :=
smooth_at_one_jet_eucl_bundle.mpr ⟨hf, hϕ⟩

end smoothness

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

instance pi_bug_instance_restatement (x : M) :
  topological_space (bundle.continuous_linear_map σ E (tangent_space I) V (trivial M V) x) :=
by apply_instance
instance pi_bug_instance_restatement2 (x : M × V) :
  topological_space (one_jet_space I 𝓘(𝕜, V) x) :=
by apply_instance

/- Given a smooth manifold `M` and a normed space `V`, there is a canonical projection from the
one-jet bundle of maps from `M` to `V` to the bundle of homomorphisms from `TM` to `V`. This is
constructed using the fact that each tangent space to `V` is canonically isomorphic to `V`. -/
def proj (v : one_jet_bundle I M 𝓘(𝕜, V) V) : J¹MV :=
⟨v.1.1, v.2⟩

lemma smooth_proj :
  smooth ((I.prod 𝓘(𝕜, V)).prod 𝓘(𝕜, E →L[𝕜] V)) (I.prod 𝓘(𝕜, E →L[𝕜] V)) (proj I M V) :=
begin
  intro x₀,
  have : smooth_at ((I.prod 𝓘(𝕜, V)).prod 𝓘(𝕜, E →L[𝕜] V)) _ id x₀ := smooth_at_id,
  simp_rw [smooth_at_one_jet_bundle, in_coordinates_core, in_coordinates_core',
    tangent_bundle_core_index_at,
    tangent_bundle.coord_change_at_self,
    continuous_linear_map.one_def, continuous_linear_map.id_comp] at this,
  exact this.1.one_jet_eucl_bundle_mk this.2.2
end

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
begin
  intro x₀,
  have : smooth_at ((I.prod 𝓘(𝕜, E →L[𝕜] V)).prod 𝓘(𝕜, V)) _ prod.fst x₀ := smooth_at_fst,
  rw [smooth_at_one_jet_eucl_bundle] at this,
  refine this.1.one_jet_bundle_mk smooth_at_snd _,
  simp_rw [in_coordinates_core, in_coordinates_core', tangent_bundle_core_index_at,
    tangent_bundle.coord_change_at_self, continuous_linear_map.one_def,
    continuous_linear_map.id_comp],
  exact this.2
end

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

local notation `σ` := ring_hom.id ℝ
local notation `FJ¹MV` :=
  bundle.continuous_linear_map σ E (tangent_space I : M → Type*) V (bundle.trivial M V)
local notation `J¹MV` := total_space FJ¹MV

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

def family_twist
  (s : one_jet_eucl_sec I M V)
  (i : N × M → (V →L[ℝ] V'))
  (i_smooth : ∀ x₀ : N × M, smooth_at (J.prod I) 𝓘(ℝ, V →L[ℝ] V') i x₀) :
  family_one_jet_eucl_sec I M V' J N :=
{ to_fun := λ p, ⟨p.2, (i p).comp (s p.2).2⟩,
  is_sec' := λ p, rfl,
  smooth' := begin
    intro x₀,
    refine smooth_at_snd.one_jet_eucl_bundle_mk' _,
    simp_rw [continuous_linear_map.comp_assoc],
    have : smooth_at (J.prod I) _ (λ x : N × M, _) x₀ := s.smooth.comp smooth_snd x₀,
    simp_rw [smooth_at_one_jet_eucl_bundle', s.is_sec] at this,
    refine (i_smooth x₀).clm_comp _,
    convert this.2,
    ext z,
    rw [s.is_sec],
  end }

end family_twist
