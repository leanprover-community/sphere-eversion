import geometry.manifold.metrizable

noncomputable theory

section
variables {E : Type*} [normed_add_comm_group E] [normed_space ℝ E] [finite_dimensional ℝ E]
  {H : Type*} [topological_space H] (I : model_with_corners ℝ E H) (M : Type*)
  [topological_space M] [charted_space H M]

/-- A metric defining the topology on a sigma-compact T₂ real manifold. -/
def manifold_metric [t2_space M] [sigma_compact_space M] : metric_space M :=
@topological_space.metrizable_space_metric _ _ (manifold_with_corners.metrizable_space I M)
end
