import geometry.manifold.algebra.lie_group

open_locale topology filter manifold big_operators
open set function filter


section
variables
  {ι : Type*} {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
  {H : Type*} [topological_space H] {I : model_with_corners ℝ E H} {M : Type*}
  [topological_space M] [charted_space H M]
  {s : set M} {F : Type*} [normed_add_comm_group F] [normed_space ℝ F]


lemma cont_mdiff_within_at.sum {ι : Type*} {f : ι → M → F} {J : finset ι}
  {n : ℕ∞} {s : set M} {x₀ : M}
  (h : ∀ i ∈ J, cont_mdiff_within_at I 𝓘(ℝ, F) n (f i) s x₀) :
  cont_mdiff_within_at I 𝓘(ℝ, F) n (λ x, ∑ i in J, f i x) s x₀ :=
begin
  classical,
  induction J using finset.induction_on with i K iK IH,
  { simp [cont_mdiff_within_at_const] },
  { simp only [iK, finset.sum_insert, not_false_iff],
    exact (h _ (finset.mem_insert_self i K)).add (IH $ λ j hj, h _ $ finset.mem_insert_of_mem hj) }
end

lemma cont_mdiff_at.sum {ι : Type*} {f : ι → M → F} {J : finset ι}
  {n : ℕ∞} {x₀ : M}
  (h : ∀ i ∈ J, cont_mdiff_at I 𝓘(ℝ, F) n (f i)  x₀) :
  cont_mdiff_at I 𝓘(ℝ, F) n (λ x, ∑ i in J, f i x) x₀ :=
begin
  simp only [← cont_mdiff_within_at_univ] at *,
  exact cont_mdiff_within_at.sum h,
end

lemma cont_mdiff.sum {ι : Type*} {f : ι → M → F} {J : finset ι}
  {n : ℕ∞} (h : ∀ i ∈ J, cont_mdiff I 𝓘(ℝ, F) n (f i)) :
  cont_mdiff I 𝓘(ℝ, F) n (λ x, ∑ i in J, f i x) :=
λ x, cont_mdiff_at.sum (λ j hj, h j hj x)

lemma cont_mdiff_within_at_finsum {ι : Type*} {f : ι → M → F} (lf : locally_finite (λ i, support $ f i))
  {n : ℕ∞} {s : set M} {x₀ : M}
  (h : ∀ i, cont_mdiff_within_at I 𝓘(ℝ, F) n (f i) s x₀) :
  cont_mdiff_within_at I 𝓘(ℝ, F) n (λ x, ∑ᶠ i, f i x) s x₀ :=
let ⟨I, hI⟩ := finsum_eventually_eq_sum lf x₀ in
cont_mdiff_within_at.congr_of_eventually_eq (cont_mdiff_within_at.sum $ λ i hi, h i)
    (eventually_nhds_within_of_eventually_nhds hI) hI.self_of_nhds

lemma cont_mdiff_at_finsum {ι : Type*} {f : ι → M → F} (lf : locally_finite (λ i, support $ f i))
  {n : ℕ∞} {x₀ : M}
  (h : ∀ i, cont_mdiff_at I 𝓘(ℝ, F) n (f i) x₀) :
  cont_mdiff_at I 𝓘(ℝ, F) n (λ x, ∑ᶠ i, f i x) x₀ :=
cont_mdiff_within_at_finsum lf h

end
