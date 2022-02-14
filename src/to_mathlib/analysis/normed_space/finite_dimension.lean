import analysis.normed_space.finite_dimension

@[simp]lemma linear_map.ker_to_continuous_linear_map {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {E : Type*} [normed_group E]
  [normed_space 𝕜 E] {F' : Type*} [add_comm_group F'] [module 𝕜 F']
  [topological_space F'] [topological_add_group F'] [has_continuous_smul 𝕜 F']
  [complete_space 𝕜] [finite_dimensional 𝕜 E] (f : E →ₗ[𝕜] F') :
  f.to_continuous_linear_map.ker = f.ker := rfl
