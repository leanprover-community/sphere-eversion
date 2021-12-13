import analysis.calculus.times_cont_diff

variables {ι k : Type*} [fintype ι]
variables [nondiscrete_normed_field k] {Z : Type*} [normed_group Z] [normed_space k Z]
variables {m : with_top ℕ}

lemma times_cont_diff_apply (i : ι) :
  times_cont_diff k m (λ (f : ι → Z), f i) :=
(continuous_linear_map.proj i : (ι → Z) →L[k] Z).times_cont_diff

lemma times_cont_diff_apply_apply (i j : ι) :
  times_cont_diff k m (λ (f : ι → ι → Z), f j i) :=
(@times_cont_diff_apply _ _ _ _ Z _ _ m i).comp (@times_cont_diff_apply _ _ _ _ (ι → Z) _ _ m j)
