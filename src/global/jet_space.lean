import local.h_principle
import geometry.manifold.cont_mdiff_map
import to_mathlib.geometry.manifold.misc

open_locale manifold

variables {𝕜 E E' H H' Eb : Type*}
variables [nondiscrete_normed_field 𝕜]
variables [normed_group E] [normed_space 𝕜 E] [topological_space H]
variables [normed_group E'] [normed_space 𝕜 E'] [topological_space H']
variables (I : model_with_corners 𝕜 E H)
variables (I' : model_with_corners 𝕜 E' H')
variables (M N : Type*)
variables [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
variables [topological_space N] [charted_space H' N] [smooth_manifold_with_corners I' N]
variables [normed_group Eb] [normed_space 𝕜 Eb]

-- useful declarations
-- #print bundle.total_space
-- #print basic_smooth_vector_bundle_core
-- #print topological_vector_bundle_core.total_space
-- #check@ basic_smooth_vector_bundle_core.to_smooth_manifold

/-!
### needed PRs

#8545: the pullback of a vector bundle is a vector bundle,
* Do we need more work for smooth vector bundles?

continuous linear maps form a vector bundle
* Zulip https://leanprover.zulipchat.com/#narrow/stream/303200-sphere-eversion/topic/bundle.20of.20continuous.20linear.20maps
* branch#vb-hom
* WIP
* Do we need more work for smooth vector bundles?
-/

/-
def jet_bundle (x : M × N) : Type* :=
vector_bundle_continuous_linear_map
  (pullback mcont_diff_map.fst (tangent_bundle I M))
  (pullback mcont_diff_map.snd (tangent_bundle I' N)) x

def jet_space : Type* :=
bundle.total_space (jet_bundle I I' M N)
-/
