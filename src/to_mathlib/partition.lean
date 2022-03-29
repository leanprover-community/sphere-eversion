import geometry.manifold.partition_of_unity

noncomputable theory

open_locale topological_space filter manifold big_operators
open set function filter

section
-- TODO: put reasonnable assumptions
lemma tsupport_smul {𝕜 : Type*} {X : Type*} {F : Type*} [nondiscrete_normed_field 𝕜]
  [topological_space X] [normed_group F] [normed_space 𝕜 F]
  (f : X → F) (s : X → 𝕜) : tsupport (λ x, s x • f x) ⊆ tsupport s :=
begin
  apply closure_mono,
  erw support_smul,
  exact inter_subset_left _ _
end

-- TODO: put reasonnable assumptions
lemma locally_finite.smul {ι : Type*} {𝕜 : Type*} {X : Type*} {F : Type*} [nondiscrete_normed_field 𝕜]
  [topological_space X] [normed_group F] [normed_space 𝕜 F]
  {s : ι → X → 𝕜} (h : locally_finite $ λ i, support $ s i) (f : ι → X → F) :
  locally_finite (λ i, support $ s i • f i) :=
begin
  apply h.subset (λ i, _),
  rw support_smul,
  exact inter_subset_left _ _
end

end

section
variables {ι X : Type*} [topological_space X]

@[to_additive]
lemma locally_finite_mul_support_iff [has_zero X] {M : Type*} [comm_monoid M] {f : ι → X → M} :
locally_finite (λi, mul_support $ f i) ↔ locally_finite (λ i, mul_tsupport $ f i) :=
⟨locally_finite.closure, λ H, H.subset $ λ i, subset_closure⟩

@[to_additive]
lemma locally_finite.exists_finset_mul_support {M : Type*} [comm_monoid M] {ρ : ι → X → M}
  (hρ : locally_finite (λ i, mul_support $ ρ i)) (x₀ : X) :
  ∃ I : finset ι, ∀ᶠ x in 𝓝 x₀, mul_support (λ i, ρ i x) ⊆ I :=
begin
  rcases hρ x₀ with ⟨U, hxU, hUf⟩,
  refine ⟨hUf.to_finset, mem_of_superset hxU $ λ y hy i hi, _⟩,
  rw [hUf.coe_to_finset],
  exact ⟨y, hi, hy⟩
end

@[to_additive] lemma finprod_eventually_eq_prod {M : Type*} [comm_monoid M]
  {f : ι → X → M} (hf : locally_finite (λ i, mul_support (f i))) (x : X) :
  ∃ s : finset ι, ∀ᶠ y in 𝓝 x, (∏ᶠ i, f i y) = ∏ i in s, f i y :=
let ⟨I, hI⟩ := hf.exists_finset_mul_support x in
  ⟨I, hI.mono (λ y hy, finprod_eq_prod_of_mul_support_subset _ $ λ i hi, hy hi)⟩

lemma partition_of_unity.exists_finset_nhd' {s : set X} (ρ : partition_of_unity ι X s) (x₀ : X) :
  ∃ I : finset ι, (∀ᶠ x in 𝓝[s] x₀, ∑ i in I, ρ i x = 1) ∧ ∀ᶠ x in 𝓝 x₀, support (λ i, ρ i x) ⊆ I  :=
begin
  rcases ρ.locally_finite.exists_finset_support x₀ with ⟨I, hI⟩,
  refine ⟨I, _, hI⟩,
  refine eventually_nhds_within_iff.mpr (hI.mono $ λ x hx x_in, _),
  have : ∑ᶠ (i : ι), ρ i x = ∑ (i : ι) in I, ρ i x := finsum_eq_sum_of_support_subset _ hx,
  rwa [eq_comm, ρ.sum_eq_one x_in] at this
end

lemma partition_of_unity.exists_finset_nhd (ρ : partition_of_unity ι X univ) (x₀ : X) :
  ∃ I : finset ι, ∀ᶠ x in 𝓝 x₀, ∑ i in I, ρ i x = 1 ∧ support (λ i, ρ i x) ⊆ I  :=
begin
  rcases ρ.exists_finset_nhd' x₀ with ⟨I, H⟩,
  use I,
  rwa [nhds_within_univ , ← eventually_and] at H
end

end

section
variables
  {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {E : Type*} [normed_group E] [normed_space 𝕜 E]
  {F : Type*} [normed_group F] [normed_space 𝕜 F]

lemma cont_diff_within_at_finsum {ι : Type*} {f : ι → E → F} (lf : locally_finite (λ i, support $ f i))
  {n : with_top ℕ} {s : set E} {x₀ : E}
  (h : ∀ i, cont_diff_within_at 𝕜 n (f i) s x₀) :
  cont_diff_within_at 𝕜 n (λ x, ∑ᶠ i, f i x) s x₀ :=
let ⟨I, hI⟩ := finsum_eventually_eq_sum lf x₀ in
  cont_diff_within_at.congr_of_eventually_eq (cont_diff_within_at.sum $ λ i hi, h i)
    (eventually_nhds_within_of_eventually_nhds hI) hI.self_of_nhds

lemma cont_diff_at_finsum {ι : Type*} {f : ι → E → F} (lf : locally_finite (λ i, support $ f i))
  {n : with_top ℕ} {x₀ : E}
  (h : ∀ i, cont_diff_at 𝕜 n (f i)  x₀) :
  cont_diff_at 𝕜 n (λ x, ∑ᶠ i, f i x) x₀ :=
cont_diff_within_at_finsum lf h

end

section
variables
  {ι : Type*} {E : Type*} [normed_group E] [normed_space ℝ E] [finite_dimensional ℝ E]
  {H : Type*} [topological_space H] {I : model_with_corners ℝ E H} {M : Type*}
  [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
  {s : set M} {F : Type*} [normed_group F] [normed_space ℝ F]

lemma cont_mdiff_within_at.smul {f : M → F} {r : M → ℝ}
  {n : with_top ℕ} {s : set M} {x₀ : M}
  (hf : cont_mdiff_within_at I 𝓘(ℝ, F) n f s x₀)
  (hs : cont_mdiff_within_at I 𝓘(ℝ, ℝ) n r s x₀) :
  cont_mdiff_within_at I 𝓘(ℝ, F) n (r • f) s x₀ :=
sorry

lemma cont_mdiff_at.smul {f : M → F} {r : M → ℝ}
  {n : with_top ℕ} {x₀ : M}
  (hf : cont_mdiff_at I 𝓘(ℝ, F) n f x₀)
  (hs : cont_mdiff_at I 𝓘(ℝ, ℝ) n r x₀) :
  cont_mdiff_at I 𝓘(ℝ, F) n (r • f) x₀ :=
cont_mdiff_within_at.smul hf hs

lemma cont_mdiff_within_at.add {f g : M → F}
  {n : with_top ℕ} {s : set M} {x₀ : M}
  (hf : cont_mdiff_within_at I 𝓘(ℝ, F) n f s x₀)
  (hg : cont_mdiff_within_at I 𝓘(ℝ, F) n g s x₀) :
  cont_mdiff_within_at I 𝓘(ℝ, F) n (f + g) s x₀ :=
begin
  have : cont_mdiff_within_at I 𝓘(ℝ, F × F) n (λ x, (f x, g x)) s x₀,
  {
    sorry },

  sorry
end

lemma cont_mdiff_within_at.sum {ι : Type*} {f : ι → M → F} {J : finset ι}
  {n : with_top ℕ} {s : set M} {x₀ : M}
  (h : ∀ i ∈ J, cont_mdiff_within_at I 𝓘(ℝ, F) n (f i) s x₀) :
  cont_mdiff_within_at I 𝓘(ℝ, F) n (λ x, ∑ i in J, f i x) s x₀ :=
begin
  classical,
  induction J using finset.induction_on with i K iK IH,
  { simp [cont_mdiff_within_at_const] },
  { simp only [iK, finset.sum_insert, not_false_iff],
    exact (h _ (finset.mem_insert_self i K)).add (IH $ λ j hj, h _ $ finset.mem_insert_of_mem hj) }

end

lemma cont_mdiff_within_at_finsum {ι : Type*} {f : ι → M → F} (lf : locally_finite (λ i, support $ f i))
  {n : with_top ℕ} {s : set M} {x₀ : M}
  (h : ∀ i, cont_mdiff_within_at I 𝓘(ℝ, F) n (f i) s x₀) :
  cont_mdiff_within_at I 𝓘(ℝ, F) n (λ x, ∑ᶠ i, f i x) s x₀ :=
let ⟨I, hI⟩ := finsum_eventually_eq_sum lf x₀ in
cont_mdiff_within_at.congr_of_eventually_eq (cont_mdiff_within_at.sum $ λ i hi, h i)
    (eventually_nhds_within_of_eventually_nhds hI) hI.self_of_nhds

lemma cont_mdiff_at_finsum {ι : Type*} {f : ι → M → F} (lf : locally_finite (λ i, support $ f i))
  {n : with_top ℕ} {x₀ : M}
  (h : ∀ i, cont_mdiff_at I 𝓘(ℝ, F) n (f i) x₀) :
  cont_mdiff_at I 𝓘(ℝ, F) n (λ x, ∑ᶠ i, f i x) x₀ :=
cont_mdiff_within_at_finsum lf h

lemma smooth_partition_of_unity.cont_diff_at_sum (ρ : smooth_partition_of_unity ι I M s)
  {n : with_top ℕ} {x₀ : M} {φ : ι → M → F} (hφ : ∀ i, cont_mdiff_at I 𝓘(ℝ, F) n (φ i) x₀) :
  cont_mdiff_at I 𝓘(ℝ, F) n (λ x, ∑ᶠ i, ρ i x • φ i x) x₀ :=
begin
  refine cont_mdiff_at_finsum (ρ.locally_finite.smul _) _,
  intro i,
  apply (hφ i).smul ((ρ i).smooth.of_le le_top).cont_mdiff_at
end

lemma smooth_partition_of_unity.cont_diff_at_sum' {s : set E} (ρ : smooth_partition_of_unity ι 𝓘(ℝ, E) E s)
  {n : with_top ℕ} {x₀ : E} {φ : ι → E → F} (hφ : ∀ i, cont_diff_at ℝ n (φ i) x₀) :
  cont_diff_at ℝ n (λ x, ∑ᶠ i, ρ i x • φ i x) x₀ :=
begin
  rw ← cont_mdiff_at_iff_cont_diff_at,
  apply ρ.cont_diff_at_sum,
  intro i,
  rw cont_mdiff_at_iff_cont_diff_at,
  exact hφ i
end

end


variables
  {E : Type*} [normed_group E] [normed_space ℝ E] [finite_dimensional ℝ E]
  {F : Type*} [normed_group F] [normed_space ℝ F]

-- Not used here, but should be in mathlib
lemma has_fderiv_at_of_not_mem (𝕜 : Type*) {E : Type*} {F : Type*} [nondiscrete_normed_field 𝕜]
  [normed_group E] [normed_space 𝕜 E] [normed_group F] [normed_space 𝕜 F]
  {f : E → F} {x} (hx : x ∉ tsupport f) : has_fderiv_at f (0 : E →L[𝕜] F) x :=
(has_fderiv_at_const (0 : F)  x).congr_of_eventually_eq
  (not_mem_closure_support_iff_eventually_eq.mp hx)

lemma cont_diff_at_of_not_mem (𝕜 : Type*) {E : Type*} {F : Type*} [nondiscrete_normed_field 𝕜]
  [normed_group E] [normed_space 𝕜 E] [normed_group F] [normed_space 𝕜 F]
  {f : E → F} {x} (hx : x ∉ tsupport f) (n : with_top ℕ) : cont_diff_at 𝕜 n f x :=
(cont_diff_at_const : cont_diff_at 𝕜 n (λ x, (0 : F)) x).congr_of_eventually_eq
   (not_mem_closure_support_iff_eventually_eq.mp hx)



lemma partition_induction_on
  {P : E → F → Prop} (hP : ∀ x, convex ℝ {y | P x y})
  {n : with_top ℕ}
  (hP' : ∀ x : E, ∃ U ∈ 𝓝 x, ∃ f : E → F, cont_diff_on ℝ n f U ∧ ∀ x ∈ U, P x (f x)) :
  ∃ f : E → F, cont_diff ℝ n f ∧ ∀ x, P x (f x) :=
begin
  replace hP' : ∀ x : E, ∃ U ∈ 𝓝 x, is_open U ∧ ∃ f : E → F, cont_diff_on ℝ n f U ∧ ∀ x ∈ U, P x (f x),
  { intros x,
    rcases ((nhds_basis_opens x).exists_iff _).mp (hP' x) with ⟨U, ⟨x_in, U_op⟩, f, hf, hfP⟩,
    exact ⟨U, U_op.mem_nhds x_in, U_op, f, hf, hfP⟩,
    rintros s t hst ⟨f, hf, hf'⟩,
    exact ⟨f, hf.mono hst, λ x hx, hf' x (hst hx)⟩ },
  choose U hU U_op hU' using hP',
  choose φ hφ using hU',
  rcases smooth_bump_covering.exists_is_subordinate 𝓘(ℝ, E) is_closed_univ (λ x h, hU x) with
    ⟨ι, b, hb⟩,
  let ρ := b.to_smooth_partition_of_unity,
  have subf : ∀ i, support (ρ i) ⊆ U (b.c i),
  { intro i,
    exact subset_closure.trans (smooth_bump_covering.is_subordinate.to_smooth_partition_of_unity hb i) },
  refine ⟨λ x : E, (∑ᶠ i, (ρ i x) • φ (b.c i) x), cont_diff_iff_cont_diff_at.mpr _, _⟩,
  all_goals {
    intros x₀,
    rcases ρ.to_partition_of_unity.exists_finset_nhd x₀ with ⟨s, hs⟩,
    have hsum' : ∀ᶠ x in 𝓝 x₀,
      ∑ᶠ i, ρ i x • φ (b.c i) x = ∑ i in s, ρ i x • φ (b.c i) x,
    { apply hs.mono,
      intros x hx,
      apply finsum_eq_sum_of_support_subset,
      apply subset.trans _ hx.2,
      erw function.support_smul,
      exact inter_subset_left _ _ },
    rcases eventually_and.mp hs with ⟨hsum, hsupp⟩,
    clear hs },
  { apply cont_diff_at_finsum (ρ.locally_finite.smul _),
    intro i,
    by_cases hx₀ : x₀ ∈ U (b.c i),
    { exact (((ρ i).smooth.cont_diff.cont_diff_at).of_le le_top).smul
      (((hφ $ b.c i).1 x₀ hx₀).cont_diff_at $ (U_op $ b.c i).mem_nhds hx₀)  },
    { apply cont_diff_at_of_not_mem,
      intros Hx₀,
      have : x₀ ∉ tsupport (ρ i) := λ h, hx₀ (hb.to_smooth_partition_of_unity i h),
      exact this (tsupport_smul (φ (b.c i)) (ρ i) Hx₀) } },
  { have : ∀ (i : ι) , ∀ x ∈ support (ρ i), P x (φ (b.c i) x) :=
      λ i x hx, (hφ $ b.c i).2 _ (subf i hx),
    have Hfin : finite (support (λ i, ρ i x₀)),
    { exact ρ.locally_finite.point_finite x₀ },
    have : ∑ᶠ i, ρ i x₀ • φ (b.c i) x₀ = ∑ i in Hfin.to_finset, ρ i x₀ • φ (b.c i) x₀,
    { apply finsum_eq_sum_of_support_subset,
      rw [finite.coe_to_finset],
      erw function.support_smul,
      exact inter_subset_left _ _ },
    rw this,
    apply (hP x₀).sum_mem (λ i hi, (ρ.nonneg i x₀ : _)),
    { rw [eq_comm, ← ρ.sum_eq_one (mem_univ x₀)],
      apply finsum_eq_sum_of_support_subset,
      rw [finite.coe_to_finset],
      exact subset_rfl },
    { rintros i hi,
      rw [finite.mem_to_finset] at hi,
      exact (hφ $ b.c i).2 _ (subf _ hi) } },
end

/-
-- Extra credit for a version in an open set:

lemma partition_induction_on {s : set E} (hs : is_open s)
  {P : E → F → Prop} (hP : ∀ x ∈ s, convex ℝ {y | P x y})
  {n : with_top ℕ}
  (hP' : ∀ x ∈ s, ∃ U ∈ 𝓝 x, ∃ f : E → F, cont_diff_on ℝ n f U ∧ ∀ x ∈ U, P x (f x)) :
  ∃ f : E → F, cont_diff_on ℝ n f s ∧ ∀ x ∈ s, P x (f x) :=
-/


example {f : E → ℝ} (h : ∀ x : E, ∃ U ∈ 𝓝 x, ∃ ε : ℝ, ∀ x' ∈ U, 0 < ε ∧ ε ≤ f x') :
  ∃ f' : E → ℝ, cont_diff ℝ ⊤ f' ∧ ∀ x, (0 < f' x ∧ f' x ≤ f x) :=
begin
  let P : E → ℝ → Prop := λ x t, 0 < t ∧ t ≤ f x,
  have hP : ∀ x, convex ℝ {y | P x y}, from λ x, convex_Ioc _ _,
  apply partition_induction_on hP,
  intros x,
  rcases h x with ⟨U, U_in, ε, hU⟩,
  exact ⟨U, U_in, λ x, ε, cont_diff_on_const, hU⟩
end
