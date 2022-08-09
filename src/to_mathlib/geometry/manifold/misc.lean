import geometry.manifold.cont_mdiff_map

open_locale manifold

variables {𝕜 E E' H H' M M' N : Type*}
variables [nontrivially_normed_field 𝕜]
variables [normed_add_comm_group E] [normed_space 𝕜 E] [topological_space H]
variables [normed_add_comm_group E'] [normed_space 𝕜 E'] [topological_space H']
variables (I : model_with_corners 𝕜 E H)
variables [topological_space M] [charted_space H M]
variables [topological_space M'] [charted_space H M']
variables (I' : model_with_corners 𝕜 E' H') [topological_space N] [charted_space H' N]

namespace mcont_diff_map

/-- The map `M × N → M` as a `Cⁿ` map between manifolds -/
def fst (n : with_top ℕ) : C^n⟮I.prod I', M × N; I, M⟯ :=
⟨prod.fst, cont_mdiff_fst⟩

/-- The map `M × N → N` as a `Cⁿ` map between manifolds -/
def snd (n : with_top ℕ) : C^n⟮I.prod I', M × N; I', N⟯ :=
⟨prod.snd, cont_mdiff_snd⟩

end mcont_diff_map
