import to_mathlib.geometry.manifold.misc_manifold

open_locale manifold

variables {𝕜 E E' H H' M M' N : Type*}
variables [nontrivially_normed_field 𝕜]
variables [normed_add_comm_group E] [normed_space 𝕜 E] [topological_space H]
variables [normed_add_comm_group E'] [normed_space 𝕜 E'] [topological_space H']
variables (I : model_with_corners 𝕜 E H)
variables [topological_space M] [charted_space H M]
variables [topological_space M'] [charted_space H M']
variables (I' : model_with_corners 𝕜 E' H') [topological_space N] [charted_space H' N]
