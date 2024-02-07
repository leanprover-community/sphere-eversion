import Mathlib.Geometry.Manifold.Metrizable

noncomputable section

section

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {H : Type _}
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H) (M : Type _) [TopologicalSpace M]
  [ChartedSpace H M]

/-- A metric defining the topology on a σ-compact T₂ real manifold. -/
def manifoldMetric [T2Space M] [SigmaCompactSpace M] : MetricSpace M :=
  @TopologicalSpace.metrizableSpaceMetric _ _ (ManifoldWithCorners.metrizableSpace I M)

end
