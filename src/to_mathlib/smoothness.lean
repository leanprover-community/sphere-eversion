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


variables {𝕜 E F F' : Type*}
variables [nondiscrete_normed_field 𝕜] [normed_group E] [normed_space 𝕜 E]
variables [normed_group F] [normed_space 𝕜 F]
variables [normed_linear_ordered_field F'] [normed_space 𝕜 F']

lemma cont_diff.if_le_of_fderiv {n : with_top ℕ} {f g : E → F} {a b : E → F'}
  (hf : cont_diff 𝕜 n f) (hg : cont_diff 𝕜 n g) (ha : cont_diff 𝕜 n a) (hb : cont_diff 𝕜 n b)
  (h : ∀ x n, a x = b x → iterated_fderiv 𝕜 n f x = iterated_fderiv 𝕜 n g x) :
  cont_diff 𝕜 n (λ x, if a x ≤ b x then f x else g x) :=
sorry

lemma cont_diff.if_le_of_deriv {n : with_top ℕ} {f g : 𝕜 → F} {a b : 𝕜 → F'}
  (hf : cont_diff 𝕜 n f) (hg : cont_diff 𝕜 n g) (ha : cont_diff 𝕜 n a) (hb : cont_diff 𝕜 n b)
  (h : ∀ x n, a x = b x → iterated_deriv n f x = iterated_deriv n g x) :
  cont_diff 𝕜 n (λ x, if a x ≤ b x then f x else g x) :=
sorry
