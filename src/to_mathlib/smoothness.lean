import analysis.calculus.specific_functions

/- arguments about smoothness -/

open exp_neg_inv_glue real
lemma iterated_deriv_exp_neg_inv_glue (n : ℕ) : iterated_deriv n exp_neg_inv_glue = f_aux n :=
by simp_rw [← f_aux_zero_eq, f_aux_iterated_deriv]

lemma iterated_deriv_exp_neg_inv_glue_zero (n : ℕ) :
  iterated_deriv n exp_neg_inv_glue 0 = 0 :=
by simp_rw [iterated_deriv_exp_neg_inv_glue, f_aux, le_rfl, if_true]

lemma iterated_deriv_smooth_transition_zero (n : ℕ) : iterated_deriv n smooth_transition 0 = 0 :=
sorry

lemma iterated_deriv_smooth_transition_one {n : ℕ} (hn : 0 < n) :
  iterated_deriv n smooth_transition 1 = 0 :=
sorry

namespace continuous_multilinear_map
variables {R ι M₃ : Type*} {M₁ M₂ : ι → Type*}
variables [decidable_eq ι] [semiring R]
variables [Π i, add_comm_monoid (M₁ i)] [Π i, module R (M₁ i)] [Π i, topological_space (M₁ i)]
variables [Π i, add_comm_monoid (M₂ i)] [Π i, module R (M₂ i)] [Π i, topological_space (M₂ i)]
variables [add_comm_monoid M₃] [module R M₃] [topological_space M₃]
def prod_elim (L₁ : continuous_multilinear_map R M₁ M₃) (L₂ : continuous_multilinear_map R M₂ M₃) :
  continuous_multilinear_map R (λ i, M₁ i × M₂ i) M₃ :=
sorry

end continuous_multilinear_map


section smooth
variables {𝕜 E E' F F' G H K : Type*}
variables [nondiscrete_normed_field 𝕜]
variables [normed_group E] [normed_space 𝕜 E]
variables [normed_group E'] [normed_space 𝕜 E']
variables [normed_group F] [normed_space 𝕜 F]
variables [normed_group G] [normed_space 𝕜 G]
variables [normed_group H] [normed_space 𝕜 H]
variables [normed_group K] [normed_space 𝕜 K]
variables [normed_linear_ordered_field F'] [normed_space 𝕜 F']
variables {n : with_top ℕ}
-- #print continuous.if_le

lemma cont_diff_of_partial {f : E × E' → F} (h1f : ∀ x, cont_diff 𝕜 n (λ y, f (x, y)))
  (h2f : ∀ y, cont_diff 𝕜 n (λ x, f (x, y))) (hn : 1 ≤ n) : cont_diff 𝕜 n f :=
sorry

lemma iterated_fderiv_of_partial {f : E × E' → F} {n : ℕ} (h1f : ∀ x, cont_diff 𝕜 n (λ y, f (x, y)))
  (h2f : ∀ y, cont_diff 𝕜 n (λ x, f (x, y))) (hn : 1 ≤ n) (x : E) (y : E') :
    iterated_fderiv 𝕜 n f (x, y) =
    (iterated_fderiv 𝕜 n (λ x, f (x, y)) x).prod_elim (iterated_fderiv 𝕜 n (λ y, f (x, y)) y) :=
sorry

lemma cont_diff.if_le_of_fderiv {f g : E → F} {a b : E → F'}
  (hf : cont_diff 𝕜 n f) (hg : cont_diff 𝕜 n g) (ha : cont_diff 𝕜 n a) (hb : cont_diff 𝕜 n b)
  (h : ∀ x n, a x = b x → iterated_fderiv 𝕜 n f x = iterated_fderiv 𝕜 n g x) :
  cont_diff 𝕜 n (λ x, if a x ≤ b x then f x else g x) :=
sorry

lemma cont_diff.if_le_of_deriv {n : with_top ℕ} {f g : 𝕜 → F} {a b : 𝕜 → F'}
  (hf : cont_diff 𝕜 n f) (hg : cont_diff 𝕜 n g) (ha : cont_diff 𝕜 n a) (hb : cont_diff 𝕜 n b)
  (h : ∀ x n, a x = b x → iterated_deriv n f x = iterated_deriv n g x) :
  cont_diff 𝕜 n (λ x, if a x ≤ b x then f x else g x) :=
sorry

lemma cont_diff.comp₂ {g : E × F → G} (hg : cont_diff 𝕜 n g) {e : H → E} (he : cont_diff 𝕜 n e)
  {f : H → F} (hf : cont_diff 𝕜 n f) : cont_diff 𝕜 n (λ h, g (e h, f h)) :=
hg.comp $ he.prod hf

lemma cont_diff.comp₃ {g : E × F × K → G} (hg : cont_diff 𝕜 n g)
  {e : H → E} (he : cont_diff 𝕜 n e) {f : H → F} (hf : cont_diff 𝕜 n f)
  {k : H → K} (hk : cont_diff 𝕜 n k) : cont_diff 𝕜 n (λ h, g (e h, f h, k h)) :=
hg.comp $ he.prod $ hf.prod hk

end smooth
