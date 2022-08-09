import geometry.manifold.partition_of_unity

noncomputable theory

open_locale topological_space filter manifold big_operators
open set function filter

section

lemma tsupport_smul_left
  {α : Type*} [topological_space α] {M : Type*} {R : Type*} [semiring R] [add_comm_monoid M]
  [module R M] [no_zero_smul_divisors R M] (f : α → R) (g : α → M) :
  tsupport (f • g) ⊆ tsupport f :=
begin
  apply closure_mono,
  erw support_smul,
  exact inter_subset_left _ _
end

lemma tsupport_smul_right
   {α : Type*} [topological_space α] {M : Type*} {R : Type*} [semiring R] [add_comm_monoid M]
  [module R M] [no_zero_smul_divisors R M] (f : α → R) (g : α → M) :
    tsupport (f • g) ⊆ tsupport g :=
begin
  apply closure_mono,
  erw support_smul,
  exact inter_subset_right _ _
end

lemma locally_finite.smul_left {ι : Type*} {α : Type*} [topological_space α] {M : Type*}
  {R : Type*} [semiring R] [add_comm_monoid M] [module R M] [no_zero_smul_divisors R M]
  {s : ι → α → R} (h : locally_finite $ λ i, support $ s i) (f : ι → α → M) :
  locally_finite (λ i, support $ s i • f i) :=
begin
  apply h.subset (λ i, _),
  rw support_smul,
  exact inter_subset_left _ _
end

lemma locally_finite.smul_right {ι : Type*} {α : Type*} [topological_space α] {M : Type*}
  {R : Type*} [semiring R] [add_comm_monoid M] [module R M] [no_zero_smul_divisors R M]
   {f : ι → α → M} (h : locally_finite $ λ i, support $ f i) (s : ι → α → R) :
  locally_finite (λ i, support $ s i • f i) :=
begin
  apply h.subset (λ i, _),
  rw support_smul,
  exact inter_subset_right _ _
end


end

section
variables {ι X : Type*} [topological_space X]

@[to_additive]
lemma locally_finite_mul_support_iff {M : Type*} [comm_monoid M] {f : ι → X → M} :
locally_finite (λi, mul_support $ f i) ↔ locally_finite (λ i, mul_tsupport $ f i) :=
⟨locally_finite.closure, λ H, H.subset $ λ i, subset_closure⟩

@[to_additive]
lemma locally_finite.exists_finset_mul_support_eq {M : Type*} [comm_monoid M] {ρ : ι → X → M}
  (hρ : locally_finite (λ i, mul_support $ ρ i)) (x₀ : X) :
  ∃ I : finset ι, mul_support (λ i, ρ i x₀) = I :=
begin
  use (hρ.point_finite x₀).to_finset,
  rw [finite.coe_to_finset],
  refl
end

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

/-- The support of a partition of unity at a point as a `finset`. -/
def partition_of_unity.finsupport {s : set X} (ρ : partition_of_unity ι X s) (x₀ : X) : finset ι :=
(ρ.locally_finite.point_finite x₀).to_finset

@[simp] lemma partition_of_unity.coe_finsupport {s : set X} (ρ : partition_of_unity ι X s) (x₀ : X) :
(ρ.finsupport x₀ : set ι) = support (λ i, ρ i x₀) :=
begin
  dsimp only [partition_of_unity.finsupport],
  rw finite.coe_to_finset,
  refl
end

@[simp] lemma partition_of_unity.mem_finsupport {s : set X} (ρ : partition_of_unity ι X s)
  (x₀ : X) {i} : i ∈ ρ.finsupport x₀ ↔ i ∈ support (λ i, ρ i x₀) :=
by simp only [partition_of_unity.finsupport, mem_support, finite.mem_to_finset, mem_set_of_eq]

/-- Try to prove something is in a set by applying `set.mem_univ`. -/
meta def tactic.mem_univ : tactic unit := `[apply set.mem_univ]

lemma partition_of_unity.sum_finsupport {s : set X} (ρ : partition_of_unity ι X s) {x₀ : X}
  (hx₀ : x₀ ∈ s . tactic.mem_univ) :
  ∑ i in ρ.finsupport x₀, ρ i x₀ = 1 :=
begin
  have := ρ.sum_eq_one hx₀,
  rwa finsum_eq_sum_of_support_subset at this,
  rw [ρ.coe_finsupport],
  exact subset.rfl
end

lemma partition_of_unity.sum_finsupport_smul {s : set X} (ρ : partition_of_unity ι X s) {x₀ : X}
  {M : Type*} [add_comm_group M] [module ℝ M]
  (φ : ι → X → M) :
  ∑ i in ρ.finsupport x₀, ρ i x₀ • φ i x₀ = ∑ᶠ i, ρ i x₀ • φ i x₀ :=
begin
  apply (finsum_eq_sum_of_support_subset _ _).symm,
  erw [ρ.coe_finsupport x₀, support_smul],
  exact inter_subset_left _ _
end

end

section
variables
  {𝕜 : Type*} [nontrivially_normed_field 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
  {F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]

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
  {ι : Type*} {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
  {H : Type*} [topological_space H] {I : model_with_corners ℝ E H} {M : Type*}
  [topological_space M] [charted_space H M]
  {s : set M} {F : Type*} [normed_add_comm_group F] [normed_space ℝ F]


lemma cont_mdiff_within_at_of_not_mem {f : M → F} {x : M} (hx : x ∉ tsupport f) (n : with_top ℕ)
  (s : set M) :
  cont_mdiff_within_at I 𝓘(ℝ, F) n f s x :=
(cont_mdiff_within_at_const : cont_mdiff_within_at I 𝓘(ℝ, F) n (λ x, (0 : F)) s x)
  .congr_of_eventually_eq
  (eventually_nhds_within_of_eventually_nhds $ not_mem_tsupport_iff_eventually_eq.mp hx)
  (image_eq_zero_of_nmem_tsupport hx)


lemma cont_mdiff_at_of_not_mem {f : M → F} {x : M} (hx : x ∉ tsupport f) (n : with_top ℕ) :
  cont_mdiff_at I 𝓘(ℝ, F) n f x :=
cont_mdiff_within_at_of_not_mem hx n univ

@[simp]
lemma local_equiv.refl_prod_refl {α β : Type*} :
  (local_equiv.refl α).prod (local_equiv.refl β) = local_equiv.refl (α × β) :=
by { ext1 ⟨x, y⟩, { refl }, { rintro ⟨x, y⟩, refl }, exact univ_prod_univ }

@[simp]
lemma local_homeomorph.refl_prod_refl {α β : Type*} [topological_space α] [topological_space β] :
  (local_homeomorph.refl α).prod (local_homeomorph.refl β) = local_homeomorph.refl (α × β) :=
by { ext1 ⟨x, y⟩, { refl }, { rintro ⟨x, y⟩, refl }, exact univ_prod_univ }

attribute [ext] model_with_corners charted_space
lemma model_with_corners_self_prod : 𝓘(ℝ, E × F) = 𝓘(ℝ, E).prod 𝓘(ℝ, F) :=
by { ext1, simp }

lemma charted_space_self_prod : prod_charted_space E E F F = charted_space_self (E × F) :=
by { ext1, simp [prod_charted_space, atlas], ext1, simp, }

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

variables [finite_dimensional ℝ E] [smooth_manifold_with_corners I M]

lemma smooth_partition_of_unity.cont_diff_at_sum (ρ : smooth_partition_of_unity ι I M s)
  {n : with_top ℕ} {x₀ : M} {φ : ι → M → F} (hφ : ∀ i, x₀ ∈ tsupport (ρ i) → cont_mdiff_at I 𝓘(ℝ, F) n (φ i) x₀) :
  cont_mdiff_at I 𝓘(ℝ, F) n (λ x, ∑ᶠ i, ρ i x • φ i x) x₀ :=
begin
  refine cont_mdiff_at_finsum (ρ.locally_finite.smul_left _) (λ i, _),
  by_cases hx : x₀ ∈ tsupport (ρ i),
  { exact cont_mdiff_at.smul ((ρ i).smooth.of_le le_top).cont_mdiff_at (hφ i hx) },
  { exact cont_mdiff_at_of_not_mem (compl_subset_compl.mpr (tsupport_smul_left (ρ i) (φ i)) hx) n }
end

lemma smooth_partition_of_unity.cont_diff_at_sum' {s : set E} (ρ : smooth_partition_of_unity ι 𝓘(ℝ, E) E s)
  {n : with_top ℕ} {x₀ : E} {φ : ι → E → F} (hφ : ∀ i, x₀ ∈ tsupport (ρ i) → cont_diff_at ℝ n (φ i) x₀) :
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
  {E : Type*} [normed_add_comm_group E] [normed_space ℝ E] [finite_dimensional ℝ E]
  {F : Type*} [normed_add_comm_group F] [normed_space ℝ F]

-- Not used here, but should be in mathlib
lemma has_fderiv_at_of_not_mem (𝕜 : Type*) {E : Type*} {F : Type*} [nontrivially_normed_field 𝕜]
  [normed_add_comm_group E] [normed_space 𝕜 E] [normed_add_comm_group F] [normed_space 𝕜 F]
  {f : E → F} {x} (hx : x ∉ tsupport f) : has_fderiv_at f (0 : E →L[𝕜] F) x :=
(has_fderiv_at_const (0 : F)  x).congr_of_eventually_eq
  (not_mem_tsupport_iff_eventually_eq.mp hx)

-- Not used here, but should be in mathlib
lemma cont_diff_at_of_not_mem (𝕜 : Type*) {E : Type*} {F : Type*} [nontrivially_normed_field 𝕜]
  [normed_add_comm_group E] [normed_space 𝕜 E] [normed_add_comm_group F] [normed_space 𝕜 F]
  {f : E → F} {x} (hx : x ∉ tsupport f) (n : with_top ℕ) : cont_diff_at 𝕜 n f x :=
(cont_diff_at_const : cont_diff_at 𝕜 n (λ x, (0 : F)) x).congr_of_eventually_eq
   (not_mem_tsupport_iff_eventually_eq.mp hx)

universes uH uM

variables {H : Type uH} [topological_space H] (I : model_with_corners ℝ E H)
  {M : Type uM} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
  [sigma_compact_space M] [t2_space M]

local notation `𝓒` := cont_mdiff I 𝓘(ℝ, F)
local notation `𝓒_on` := cont_mdiff_on I 𝓘(ℝ, F)

lemma exists_cont_mdiff_of_convex
  {P : M → F → Prop} (hP : ∀ x, convex ℝ {y | P x y})
  {n : with_top ℕ}
  (hP' : ∀ x : M, ∃ U ∈ 𝓝 x, ∃ f : M → F, 𝓒_on n f U ∧ ∀ x ∈ U, P x (f x)) :
  ∃ f : M → F, 𝓒 n f ∧ ∀ x, P x (f x) :=
begin
  replace hP' : ∀ x : M, ∃ U ∈ 𝓝 x, is_open U ∧ ∃ f : M → F, 𝓒_on n f U ∧ ∀ x ∈ U, P x (f x),
  { intros x,
    rcases ((nhds_basis_opens x).exists_iff _).mp (hP' x) with ⟨U, ⟨x_in, U_op⟩, f, hf, hfP⟩,
    exact ⟨U, U_op.mem_nhds x_in, U_op, f, hf, hfP⟩,
    rintros s t hst ⟨f, hf, hf'⟩,
    exact ⟨f, hf.mono hst, λ x hx, hf' x (hst hx)⟩ },
  choose U hU U_op hU' using hP',
  choose φ hφ using hU',
  rcases smooth_bump_covering.exists_is_subordinate I is_closed_univ (λ x h, hU x) with
    ⟨ι, b, hb⟩,
  let ρ := b.to_smooth_partition_of_unity,
  have subf : ∀ i, support (ρ i) ⊆ U (b.c i),
  { intro i,
    exact subset_closure.trans (smooth_bump_covering.is_subordinate.to_smooth_partition_of_unity hb i) },
  refine ⟨λ x : M, (∑ᶠ i, (ρ i x) • φ (b.c i) x), _, _⟩,
  { refine λ x₀, ρ.cont_diff_at_sum (λ i hx₀, _),
    have := smooth_bump_covering.is_subordinate.to_smooth_partition_of_unity hb i hx₀,
    exact ((hφ $ b.c i).1 x₀ this).cont_mdiff_at ((U_op $ b.c i).mem_nhds this) },
  { intros x₀,
    erw ← ρ.to_partition_of_unity.sum_finsupport_smul,
    apply (hP x₀).sum_mem (λ i hi, (ρ.nonneg i x₀ : _)) ρ.to_partition_of_unity.sum_finsupport,
    rintros i hi,
    rw [partition_of_unity.mem_finsupport] at hi,
    exact (hφ $ b.c i).2 _ (subf _ hi) },
end


lemma exists_cont_diff_of_convex
  {P : E → F → Prop} (hP : ∀ x, convex ℝ {y | P x y})
  {n : with_top ℕ}
  (hP' : ∀ x : E, ∃ U ∈ 𝓝 x, ∃ f : E → F, cont_diff_on ℝ n f U ∧ ∀ x ∈ U, P x (f x)) :
  ∃ f : E → F, cont_diff ℝ n f ∧ ∀ x, P x (f x) :=
begin
  simp_rw ← cont_mdiff_iff_cont_diff,
  simp_rw ← cont_mdiff_on_iff_cont_diff_on  at ⊢ hP',
  exact exists_cont_mdiff_of_convex 𝓘(ℝ, E) hP hP'
end

open topological_space

example {f : E → ℝ} (h : ∀ x : E, ∃ U ∈ 𝓝 x, ∃ ε : ℝ, ∀ x' ∈ U, 0 < ε ∧ ε ≤ f x') :
  ∃ f' : E → ℝ, cont_diff ℝ ⊤ f' ∧ ∀ x, (0 < f' x ∧ f' x ≤ f x) :=
begin
  let P : E → ℝ → Prop := λ x t, 0 < t ∧ t ≤ f x,
  have hP : ∀ x, convex ℝ {y | P x y}, from λ x, convex_Ioc _ _,
  apply exists_cont_diff_of_convex hP,
  intros x,
  rcases h x with ⟨U, U_in, ε, hU⟩,
  exact ⟨U, U_in, λ x, ε, cont_diff_on_const, hU⟩
end

lemma convex_set_of_imp_eq (P : Prop) (y : F) : convex ℝ {x : F | P → x = y } :=
by by_cases hP : P; simp [hP, convex_singleton, convex_univ]

-- lemma exists_smooth_and_eq_on_aux1 {f : E → F} {ε : E → ℝ} (hf : continuous f)
--   (hε : continuous ε) (h2ε : ∀ x, 0 < ε x) (x₀ : E) :
--   ∃ U ∈ 𝓝 x₀, ∀ x ∈ U, dist (f x₀) (f x) < ε x :=
-- begin
--   have h0 : ∀ x, dist (f x) (f x) < ε x := λ x, by simp_rw [dist_self, h2ε],
--   refine ⟨_, (is_open_lt (continuous_const.dist hf) hε).mem_nhds $ h0 x₀, λ x hx, hx⟩
-- end

-- lemma exists_smooth_and_eq_on_aux2 {n : with_top ℕ} {f : E → F} {ε : E → ℝ} (hf : continuous f)
--   (hε : continuous ε) (h2ε : ∀ x, 0 < ε x)
--   {s : set E} (hs : is_closed s) (hfs : ∃ U ∈ 𝓝ˢ s, cont_diff_on ℝ n f U)
--   (x₀ : E) :
--   ∃ U ∈ 𝓝 x₀, ∀ x ∈ U, dist (f x₀) (f x) < ε x :=
-- begin
--   have h0 : ∀ x, dist (f x) (f x) < ε x := λ x, by simp_rw [dist_self, h2ε],
--   refine ⟨_, (is_open_lt (continuous_const.dist hf) hε).mem_nhds $ h0 x₀, λ x hx, hx⟩
-- end

lemma exists_smooth_and_eq_on {n : with_top ℕ} {f : E → F} {ε : E → ℝ} (hf : continuous f)
  (hε : continuous ε) (h2ε : ∀ x, 0 < ε x)
  {s : set E} (hs : is_closed s) (hfs : ∃ U ∈ 𝓝ˢ s, cont_diff_on ℝ n f U) :
  ∃ f' : E → F, cont_diff ℝ n f' ∧ (∀ x, dist (f' x) (f x) < ε x) ∧ eq_on f' f s :=
begin
  have h0 : ∀ x, dist (f x) (f x) < ε x := λ x, by simp_rw [dist_self, h2ε],
  let P : E → F → Prop := λ x t, dist t (f x) < ε x ∧ (x ∈ s → t = f x),
  have hP : ∀ x, convex ℝ {y | P x y} :=
    λ x, (convex_ball (f x) (ε x)).inter (convex_set_of_imp_eq _ _),
  obtain ⟨f', hf', hPf'⟩ := exists_cont_diff_of_convex hP _,
  { exact ⟨f', hf', λ x, (hPf' x).1, λ x, (hPf' x).2⟩ },
  { intros x,
    obtain ⟨U, hU, hfU⟩ := hfs,
    by_cases hx : x ∈ s,
    { refine ⟨U, mem_nhds_set_iff_forall.mp hU x hx, _⟩,
      refine ⟨f, hfU, λ y _, ⟨h0 y, λ _, rfl⟩⟩ },
    { have : is_open {y : E | dist (f x) (f y) < ε y} := is_open_lt (continuous_const.dist hf) hε,
      exact ⟨_, (this.sdiff hs).mem_nhds ⟨h0 x, hx⟩, λ _, f x, cont_diff_on_const,
        λ y hy, ⟨hy.1, λ h2y, (hy.2 h2y).elim⟩⟩ } },
end
