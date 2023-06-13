import to_mathlib.analysis.calculus
import geometry.manifold.diffeomorph
import geometry.manifold.algebra.monoid
import geometry.manifold.metrizable

open bundle set function filter
open_locale manifold topology
noncomputable theory

section smooth_manifold_with_corners
open smooth_manifold_with_corners

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
  {E' : Type*} [normed_add_comm_group E'] [normed_space 𝕜 E']
  {F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]
  {F' : Type*} [normed_add_comm_group F'] [normed_space 𝕜 F']
  {H : Type*} [topological_space H] {I : model_with_corners 𝕜 E H}
  {H' : Type*} [topological_space H'] {I' : model_with_corners 𝕜 E' H'}
  {G : Type*} [topological_space G] {J : model_with_corners 𝕜 F G}
  {G' : Type*} [topological_space G'] {J' : model_with_corners 𝕜 F' G'}
  {M : Type*} [topological_space M] [charted_space H M]
  {M' : Type*} [topological_space M'] [charted_space H' M']
  {N : Type*} [topological_space N] [charted_space G N]
  {N' : Type*} [topological_space N'] [charted_space G' N']
  {F'' : Type*} [normed_add_comm_group F''] [normed_space 𝕜 F'']
  {E'' : Type*} [normed_add_comm_group E''] [normed_space 𝕜 E'']
  {H'' : Type*} [topological_space H''] {I'' : model_with_corners 𝕜 E'' H''}
  {M'' : Type*} [topological_space M''] [charted_space H'' M'']
  {e : local_homeomorph M H}
variables {f : M → M'} {m n : ℕ∞} {s : set M} {x x' : M}

lemma cont_mdiff_prod {f : M → M' × N'} :
  cont_mdiff I (I'.prod J') n f ↔
  cont_mdiff I I' n (λ x, (f x).1) ∧ cont_mdiff I J' n (λ x, (f x).2) :=
⟨λ h, ⟨h.fst, h.snd⟩, λ h, by { convert h.1.prod_mk h.2, ext x; refl }⟩

lemma cont_mdiff_at_prod {f : M → M' × N'} {x : M} :
  cont_mdiff_at I (I'.prod J') n f x ↔
  cont_mdiff_at I I' n (λ x, (f x).1) x ∧ cont_mdiff_at I J' n (λ x, (f x).2) x :=
⟨λ h, ⟨h.fst, h.snd⟩, λ h, by { convert h.1.prod_mk h.2, ext x; refl }⟩

lemma smooth_prod {f : M → M' × N'} :
  smooth I (I'.prod J') f ↔
  smooth I I' (λ x, (f x).1) ∧ smooth I J' (λ x, (f x).2) :=
cont_mdiff_prod

lemma smooth_at_prod {f : M → M' × N'} {x : M} :
  smooth_at I (I'.prod J') f x ↔
  smooth_at I I' (λ x, (f x).1) x ∧ smooth_at I J' (λ x, (f x).2) x :=
cont_mdiff_at_prod

lemma cont_mdiff_within_at.congr_of_eventually_eq_insert {f f' : M → M'}
  (hf : cont_mdiff_within_at I I' n f s x)
  (h : f' =ᶠ[𝓝[insert x s] x] f) : cont_mdiff_within_at I I' n f' s x :=
hf.congr_of_eventually_eq (h.filter_mono $ nhds_within_mono x $ subset_insert x s) $
  h.self_of_nhds_within (mem_insert x s)

end smooth_manifold_with_corners

section
variables {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
  {H : Type*} [topological_space H] (I : model_with_corners ℝ E H) {M : Type*}
  [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
  {G : Type*} [normed_add_comm_group G] [normed_space ℝ G] [finite_dimensional ℝ G]
  {HG : Type*} [topological_space HG] (IG : model_with_corners ℝ G HG) {N : Type*}
  [topological_space N] [charted_space HG N] [smooth_manifold_with_corners IG N]

def filter.germ.cont_mdiff_at' {x : M} (φ : germ (𝓝 x) N) (n : ℕ∞) : Prop :=
quotient.lift_on' φ (λ f, cont_mdiff_at I IG n f x) (λ f g h, propext begin
  split,
  all_goals { refine λ H, H.congr_of_eventually_eq _ },
  exacts [h.symm, h]
end)
end
