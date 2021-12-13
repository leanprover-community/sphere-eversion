import analysis.calculus.affine_map
import analysis.normed_space.add_torsor_bases

variables {ι 𝕜 E : Type*} [nondiscrete_normed_field 𝕜] [complete_space 𝕜]
variables [normed_group E] [normed_space 𝕜 E] [finite_dimensional 𝕜 E]
variables (b : affine_basis ι 𝕜 E)

lemma smooth_barycentric_coord (i : ι) : times_cont_diff 𝕜 ⊤ (b.coord i) :=
(⟨b.coord i, continuous_barycentric_coord b i⟩ : E →A[𝕜] 𝕜).times_cont_diff
