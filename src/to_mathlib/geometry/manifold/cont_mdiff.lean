import geometry.manifold.cont_mdiff

open_locale topology filter manifold big_operators
open set function filter


section
variables
  {ι : Type*} {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
  {H : Type*} [topological_space H] {I : model_with_corners ℝ E H} {M : Type*}
  [topological_space M] [charted_space H M]
  {s : set M} {F : Type*} [normed_add_comm_group F] [normed_space ℝ F]

lemma cont_mdiff_within_at_of_not_mem {f : M → F} {x : M} (hx : x ∉ tsupport f) (n : ℕ∞)
  (s : set M) :
  cont_mdiff_within_at I 𝓘(ℝ, F) n f s x :=
(cont_mdiff_within_at_const : cont_mdiff_within_at I 𝓘(ℝ, F) n (λ x, (0 : F)) s x)
  .congr_of_eventually_eq
  (eventually_nhds_within_of_eventually_nhds $ not_mem_tsupport_iff_eventually_eq.mp hx)
  (image_eq_zero_of_nmem_tsupport hx)

lemma cont_mdiff_at_of_not_mem {f : M → F} {x : M} (hx : x ∉ tsupport f) (n : ℕ∞) :
  cont_mdiff_at I 𝓘(ℝ, F) n f x :=
cont_mdiff_within_at_of_not_mem hx n univ


end
