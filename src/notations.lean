import analysis.calculus.times_cont_diff

open_locale topological_space

notation `I` := set.Icc (0 : ℝ) 1
notation `𝒞` := times_cont_diff ℝ
notation `∞` := ⊤
notation `hull` := convex_hull ℝ
notation `D` := fderiv ℝ
notation `hull` := convex_hull ℝ
notation `smooth_on` := times_cont_diff_on ℝ ⊤

-- `∀ᶠ x near s, p x` means property `p` holds at every point in a neighborhood of the set `s`.
notation `∀ᶠ` binders ` near ` s `, ` r:(scoped p, filter.eventually p $ 𝓝ˢ s) := r

notation u ` ⬝ `:70 φ:65 :=
  continuous_linear_map.comp (continuous_linear_map.to_span_singleton ℝ u) φ
