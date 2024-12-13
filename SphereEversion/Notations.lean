import Mathlib.Analysis.Calculus.ContDiff.Basic

open scoped Topology

notation "𝒞" => ContDiff ℝ

notation "hull" => convexHull ℝ

notation "D" => fderiv ℝ

notation "smooth_on" => ContDiffOn ℝ (⊤ : ℕ∞)

-- `∀ᶠ x near s, p x` means property `p` holds at every point in a neighborhood of the set `s`.
notation3 (prettyPrint := false)
  "∀ᶠ " (...)" near "s", "r:(scoped p => Filter.Eventually p <| 𝓝ˢ s) => r

notation:70 u " ⬝ " φ:65 => ContinuousLinearMap.comp (ContinuousLinearMap.toSpanSingleton ℝ u) φ
