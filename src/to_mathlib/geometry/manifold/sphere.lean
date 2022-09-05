import geometry.manifold.instances.sphere

open_locale manifold
open metric finite_dimensional function

variables (E : Type*) [inner_product_space ℝ E] {n : ℕ} [fact (finrank ℝ E = n + 1)]

lemma range_mfderiv_coe_sphere (x : sphere (0:E) 1) :
  (mfderiv (𝓡 n) 𝓘(ℝ, E) (coe : sphere (0:E) 1 → E) x).range = (ℝ ∙ (x:E))ᗮ :=
sorry

lemma mfderiv_coe_sphere_injective (x : sphere (0:E) 1) :
  injective (mfderiv (𝓡 n) 𝓘(ℝ, E) (coe : sphere (0:E) 1 → E) x) :=
sorry
