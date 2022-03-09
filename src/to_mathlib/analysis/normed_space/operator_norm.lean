import analysis.normed_space.operator_norm

local notation u ` ⬝ `:70 φ:65 :=
  continuous_linear_map.comp (continuous_linear_map.to_span_singleton ℝ u) φ

@[simp]
lemma continuous_linear_map.to_span_singleton_zero (𝕜 : Type*) {E : Type*} [semi_normed_group E] [nondiscrete_normed_field 𝕜]
  [normed_space 𝕜 E] : continuous_linear_map.to_span_singleton 𝕜 (0 : E) = 0 :=
begin
  ext u,
  simp only [continuous_linear_map.to_span_singleton_apply, continuous_linear_map.zero_apply,
             linear_map.to_span_singleton_apply, linear_map.mk_continuous_apply, smul_zero]
end

@[simp]
lemma continuous_linear_map.comp_to_span_singleton_apply {E : Type*} [normed_group E] [normed_space ℝ E]
  {F : Type*} [normed_group F] [normed_space ℝ F]
  (φ : E →L[ℝ] ℝ) (v : E) (u : F) : (u ⬝ φ) v = (φ v) • u:=
rfl
