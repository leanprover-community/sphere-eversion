import geometry.manifold.partition_of_unity
import tactic.find_unused
import to_mathlib.geometry.manifold.algebra.smooth_germ
import to_mathlib.analysis.convex.basic

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

lemma partition_of_unity.sum_finsupport' {s : set X} (ρ : partition_of_unity ι X s) {x₀ : X}
  (hx₀ : x₀ ∈ s . tactic.mem_univ) {I : finset ι} (hI : ρ.finsupport x₀ ⊆ I):
  ∑ i in I, ρ i x₀ = 1 :=
begin
  classical,
  rw [← finset.sum_sdiff hI, ρ.sum_finsupport hx₀],
  suffices : ∑ i in I \ ρ.finsupport x₀, ρ i x₀ = 0, by rw [this, zero_add],
  suffices : ∑ i in I \ ρ.finsupport x₀, (ρ i) x₀ = ∑ i in I \ ρ.finsupport x₀, 0,
  rw [this, finset.sum_const_zero],
  apply finset.sum_congr rfl,
  rintros x hx,
  simp only [finset.mem_sdiff, ρ.mem_finsupport, mem_support, not_not] at hx,
  exact hx.2
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
  {n : ℕ∞} {s : set E} {x₀ : E}
  (h : ∀ i, cont_diff_within_at 𝕜 n (f i) s x₀) :
  cont_diff_within_at 𝕜 n (λ x, ∑ᶠ i, f i x) s x₀ :=
let ⟨I, hI⟩ := finsum_eventually_eq_sum lf x₀ in
  cont_diff_within_at.congr_of_eventually_eq (cont_diff_within_at.sum $ λ i hi, h i)
    (eventually_nhds_within_of_eventually_nhds hI) hI.self_of_nhds

lemma cont_diff_at_finsum {ι : Type*} {f : ι → E → F} (lf : locally_finite (λ i, support $ f i))
  {n : ℕ∞} {x₀ : E}
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

variables [finite_dimensional ℝ E] [smooth_manifold_with_corners I M]

lemma smooth_partition_of_unity.cont_diff_at_sum (ρ : smooth_partition_of_unity ι I M s)
  {n : ℕ∞} {x₀ : M} {φ : ι → M → F} (hφ : ∀ i, x₀ ∈ tsupport (ρ i) → cont_mdiff_at I 𝓘(ℝ, F) n (φ i) x₀) :
  cont_mdiff_at I 𝓘(ℝ, F) n (λ x, ∑ᶠ i, ρ i x • φ i x) x₀ :=
begin
  refine cont_mdiff_at_finsum (ρ.locally_finite.smul_left _) (λ i, _),
  by_cases hx : x₀ ∈ tsupport (ρ i),
  { exact cont_mdiff_at.smul ((ρ i).smooth.of_le le_top).cont_mdiff_at (hφ i hx) },
  { exact cont_mdiff_at_of_not_mem (compl_subset_compl.mpr (tsupport_smul_left (ρ i) (φ i)) hx) n }
end

lemma smooth_partition_of_unity.cont_diff_at_sum' {s : set E} (ρ : smooth_partition_of_unity ι 𝓘(ℝ, E) E s)
  {n : ℕ∞} {x₀ : E} {φ : ι → E → F} (hφ : ∀ i, x₀ ∈ tsupport (ρ i) → cont_diff_at ℝ n (φ i) x₀) :
  cont_diff_at ℝ n (λ x, ∑ᶠ i, ρ i x • φ i x) x₀ :=
begin
  rw ← cont_mdiff_at_iff_cont_diff_at,
  apply ρ.cont_diff_at_sum,
  intro i,
  rw cont_mdiff_at_iff_cont_diff_at,
  exact hφ i
end

end


section
variables {ι : Type*}
variables {E : Type*} [normed_add_comm_group E] [normed_space ℝ E] [finite_dimensional ℝ E]
  {H : Type*} [topological_space H] {I : model_with_corners ℝ E H} {M : Type*}
  [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
  [sigma_compact_space M] [t2_space M]

section
variables {F : Type*} [add_comm_group F] [module ℝ F]

lemma smooth_partition_of_unity.finite_tsupport {s : set M} (ρ : smooth_partition_of_unity ι I M s) (x : M) :
{i | x ∈ tsupport (ρ i)}.finite :=
begin
  rcases ρ.locally_finite x with ⟨t, t_in, ht⟩,
  apply ht.subset,
  rintros i hi,
  simp only [inter_comm],
  exact mem_closure_iff_nhds.mp hi t t_in
end

def smooth_partition_of_unity.fintsupport {s : set M} (ρ : smooth_partition_of_unity ι I M s)
  (x : M) : finset ι :=
(ρ.finite_tsupport x).to_finset

lemma smooth_partition_of_unity.mem_fintsupport_iff {s : set M}
  (ρ : smooth_partition_of_unity ι I M s) (x : M) (i : ι) : i ∈ ρ.fintsupport x ↔ x ∈ tsupport (ρ i) :=
finite.mem_to_finset _

lemma locally_finite.eventually_subset {ι X : Type*} [topological_space X] {s : ι → set X}
(hs : locally_finite s) (hs' : ∀ i, is_closed (s i)) (x : X) :
∀ᶠ y in 𝓝 x, {i | y ∈ s i} ⊆ {i | x ∈ s i} :=
begin
  apply mem_of_superset (hs.Inter_compl_mem_nhds hs' x),
  intros y hy i hi,
  simp only [mem_Inter, mem_compl_iff] at hy,
  exact not_imp_not.mp (hy i) hi
end

lemma smooth_partition_of_unity.eventually_fintsupport_subset {s : set M}
  (ρ : smooth_partition_of_unity ι I M s) (x : M) : ∀ᶠ y in 𝓝 x, ρ.fintsupport y ⊆ ρ.fintsupport x :=
(ρ.locally_finite.closure.eventually_subset (λ _, is_closed_closure) x).mono
  (λ y, finite.to_finset_subset.mpr)

def smooth_partition_of_unity.finsupport {ι : Type*} {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
[finite_dimensional ℝ E] {H : Type*} [topological_space H] {I : model_with_corners ℝ E H}
{M : Type*} [topological_space M] [charted_space H M]
[smooth_manifold_with_corners I M] {s} (ρ : smooth_partition_of_unity ι I M s) (x : M) : finset ι :=
ρ.to_partition_of_unity.finsupport x

/-- Weaker version of `smooth_partition_of_unity.eventually_fintsupport_subset`. -/
lemma smooth_partition_of_unity.finsupport_subset_fintsupport {s : set M}
  (ρ : smooth_partition_of_unity ι I M s) (x : M) : ρ.finsupport x ⊆ ρ.fintsupport x :=
begin
  rintros i hi,
  rw ρ.mem_fintsupport_iff,
  apply subset_closure,
  exact (ρ.to_partition_of_unity.mem_finsupport x).mp hi,
end

lemma smooth_partition_of_unity.eventually_finsupport_subset {s : set M}
  (ρ : smooth_partition_of_unity ι I M s) (x : M) : ∀ᶠ y in 𝓝 x, ρ.finsupport y ⊆ ρ.fintsupport x :=
begin
  apply (ρ.eventually_fintsupport_subset x).mono,
  exact λ y hy, (ρ.finsupport_subset_fintsupport y).trans hy
end

/-- Try to prove something is in the interior of a set by using this set is `univ`. -/
meta def tactic.mem_interior_univ : tactic unit := `[rw interior_univ; apply set.mem_univ]

lemma smooth_partition_of_unity.sum_germ {s : set M} (ρ : smooth_partition_of_unity ι I M s)
  {x : M} (hx : x ∈ interior s . tactic.mem_interior_univ) :
∑ i in ρ.fintsupport x, (ρ i : smooth_germ I x) = 1 :=
begin
  have : ∀ᶠ y in 𝓝 x, y ∈ interior s,
  { exact is_open_interior.eventually_mem hx },
  have : ∀ᶠ y in 𝓝 x, (⇑∑ (i : ι) in ρ.fintsupport x, ρ i) y = 1,
  { apply ((ρ.eventually_finsupport_subset x).and this).mono,
    rintros y ⟨hy, hy'⟩,
    rw [smooth_map.coe_sum, finset.sum_apply],
    apply ρ.to_partition_of_unity.sum_finsupport' (interior_subset hy') hy },
  rw [← smooth_germ.coe_sum],
  exact smooth_germ.coe_eq_coe _ _ 1 this,
end

def smooth_partition_of_unity.combine {s : set M} (ρ : smooth_partition_of_unity ι I M s)
  (φ : ι → M → F) (x : M) : F := ∑ᶠ i, ρ i x • φ i x

include I

attribute [simps] smooth_partition_of_unity.to_partition_of_unity

lemma smooth_partition_of_unity.germ_combine_mem {s : set M} (ρ : smooth_partition_of_unity ι I M s)
  (φ : ι → M → F) {x : M} (hx : x ∈ interior s . tactic.mem_interior_univ) :
  (ρ.combine φ : germ (𝓝 x) F) ∈ really_convex_hull (smooth_germ I x) ((λ i, (φ i : germ (𝓝 x) F)) '' (ρ.fintsupport x)) :=
begin
  change x ∈ interior s at hx,
  have : (ρ.combine φ : germ (𝓝 x) F) =
    ∑ i in ρ.fintsupport x, (ρ i : smooth_germ I x) • (φ i : germ (𝓝 x) F),
  { suffices :
      (ρ.combine φ : germ (𝓝 x) F) = ↑∑ i in ρ.fintsupport x, ((ρ i : M → ℝ) • φ i : M → F),
    { rw [this, germ.coe_sum], refl },
    rw [germ.coe_eq],
    filter_upwards [ρ.eventually_finsupport_subset x] with x' hx',
    simp_rw [smooth_partition_of_unity.combine, finset.sum_apply, pi.smul_apply'],
    rw [finsum_eq_sum_of_support_subset],
    refine subset_trans _ (finset.coe_subset.mpr hx'),
    rw [smooth_partition_of_unity.finsupport, partition_of_unity.finsupport, finite.coe_to_finset],
    apply support_smul_subset_left },
  rw this,
  apply sum_mem_really_convex_hull,
  { intros i hi,
    apply eventually_of_forall,
    apply ρ.nonneg },
  { apply ρ.sum_germ hx },
  { intros i hi,
    exact mem_image_of_mem _ hi },
end

end

section

variables {F : Type*} [add_comm_group F] [module ℝ F]

lemma exists_of_convex {P : (Σ x : M, germ (𝓝 x) F) → Prop}
  (hP : ∀ x, really_convex (smooth_germ I x) {φ | P ⟨x, φ⟩})
  (hP' : ∀ x : M, ∃ f : M → F, ∀ᶠ x' in 𝓝 x, P ⟨x', f⟩) : ∃ f : M → F, ∀ x, P ⟨x, f⟩ :=
begin
  replace hP' : ∀ x : M, ∃ f : M → F, ∃ U ∈ 𝓝 x, ∀ x' ∈ U, P ⟨x', f⟩,
  { intros x,
    rcases hP' x with ⟨f, hf⟩,
    exact ⟨f, {x' | P ⟨x', ↑f⟩}, hf, λ _, id⟩ },
  choose φ U hU hφ using hP',
  rcases smooth_bump_covering.exists_is_subordinate I is_closed_univ (λ x h, hU x) with ⟨ι, b, hb⟩,
  let ρ := b.to_smooth_partition_of_unity,
  refine ⟨λ x : M, (∑ᶠ i, (ρ i x) • φ (b.c i) x), λ x₀, _⟩,
  let g : ι → germ (𝓝 x₀) F := λ i, φ (b.c i),
  have : ((λ x : M, (∑ᶠ i, (ρ i x) • φ (b.c i) x)) : germ (𝓝 x₀) F) ∈
    really_convex_hull (smooth_germ I x₀) (g '' (ρ.fintsupport x₀)),
    from ρ.germ_combine_mem (λ i x, φ (b.c i) x),
  simp_rw [really_convex_iff_hull] at hP,
  apply hP x₀, clear hP,
  have H : g '' ↑(ρ.fintsupport x₀) ⊆ {φ : (𝓝 x₀).germ F | P ⟨x₀, φ⟩},
  { rintros _ ⟨i, hi, rfl⟩,
    exact hφ _ _ (smooth_bump_covering.is_subordinate.to_smooth_partition_of_unity hb i $
      (ρ.mem_fintsupport_iff _ i).mp hi) },
  exact really_convex_hull_mono H this,
end

end

variables {F : Type*} [normed_add_comm_group F] [normed_space ℝ F]
variables {G : Type*} [normed_add_comm_group G] [normed_space ℝ G]
  {HG : Type*} [topological_space HG] (IG : model_with_corners ℝ G HG) {N : Type*}
  [topological_space N] [charted_space HG N] [smooth_manifold_with_corners IG N]

local notation `𝓒` := cont_mdiff I 𝓘(ℝ, F)
local notation `𝓒_on` := cont_mdiff_on I 𝓘(ℝ, F)


namespace filter.germ
/-- The value associated to a germ at a point. This is the common value
shared by all representatives at the given point. -/
def value {X α : Type*} [topological_space X] {x : X} (φ : germ (𝓝 x) α) : α :=
quotient.lift_on' φ (λ f, f x) (λ f g h, by { dsimp only, rw eventually.self_of_nhds h })

lemma value_smul {X α β : Type*} [topological_space X] {x : X} [has_smul α β]
  (φ : germ (𝓝 x) α) (ψ : germ (𝓝 x) β) : (φ • ψ).value = φ.value • ψ.value :=
germ.induction_on φ (λ f, germ.induction_on ψ (λ g, rfl))

@[to_additive]
def value_mul_hom {X E : Type*} [monoid E] [topological_space X] {x : X} :
  germ (𝓝 x) E →* E :=
{ to_fun := filter.germ.value,
  map_one' := rfl,
  map_mul' := λ φ ψ, germ.induction_on φ (λ f, germ.induction_on ψ (λ g, rfl)) }

def valueₗ {X 𝕜 E : Type*} [semiring 𝕜] [add_comm_monoid E] [module 𝕜 E]
  [topological_space X] {x : X} : germ (𝓝 x) E →ₗ[𝕜] E :=
{ map_smul' := λ r φ, germ.induction_on φ (λ f, rfl),
  .. filter.germ.value_add_hom }

def value_ring_hom {X E : Type*} [semiring E] [topological_space X] {x : X} :
  germ (𝓝 x) E →+* E :=
{ ..filter.germ.value_mul_hom,
  ..filter.germ.value_add_hom }

def value_order_ring_hom {X E : Type*} [ordered_semiring E] [topological_space X] {x : X} :
  germ (𝓝 x) E →+*o E :=
{ monotone' := λ φ ψ, germ.induction_on φ (λ f, germ.induction_on ψ (λ g h, h.self_of_nhds)),
  ..filter.germ.value_ring_hom }

def _root_.subring.ordered_subtype {R} [ordered_ring R] (s : subring R) : s →+*o R :=
{ monotone' := λ x y h, h,
  ..s.subtype }

def _root_.smooth_germ.value_order_ring_hom (x : N) : smooth_germ IG x →+*o ℝ :=
filter.germ.value_order_ring_hom.comp $ subring.ordered_subtype _

def _root_.smooth_germ.value_ring_hom (x : N) : smooth_germ IG x →+* ℝ :=
filter.germ.value_ring_hom.comp $ subring.subtype _

lemma _root_.smooth_germ.value_order_ring_hom_to_ring_hom (x : N) :
  (smooth_germ.value_order_ring_hom IG x).to_ring_hom  = smooth_germ.value_ring_hom IG x :=
rfl

def valueₛₗ {F} [add_comm_monoid F] [module ℝ F] (x : N) :
  germ (𝓝 x) F →ₛₗ[smooth_germ.value_ring_hom IG x] F :=
{ to_fun := filter.germ.value,
  map_smul' := λ φ ψ, value_smul (φ : germ (𝓝 x) ℝ) ψ,
  .. filter.germ.value_add_hom }
end filter.germ

variable (I)

/-- The predicate selecting germs of `cont_mdiff_at` functions.
TODO: merge with the next def that generalizes target space -/
def filter.germ.cont_mdiff_at {x : M} (φ : germ (𝓝 x) F) (n : ℕ∞) : Prop :=
quotient.lift_on' φ (λ f, cont_mdiff_at I 𝓘(ℝ, F) n f x) (λ f g h, propext begin
  split,
  all_goals { refine λ H, H.congr_of_eventually_eq _ },
  exacts [h.symm, h]
end)

-- currently unused
def filter.germ.cont_mdiff_at' {x : M} (φ : germ (𝓝 x) N) (n : ℕ∞) : Prop :=
quotient.lift_on' φ (λ f, cont_mdiff_at I IG n f x) (λ f g h, propext begin
  split,
  all_goals { refine λ H, H.congr_of_eventually_eq _ },
  exacts [h.symm, h]
end)

-- currently unused
def filter.germ.mfderiv {x : M} (φ : germ (𝓝 x) N) :
  tangent_space I x →L[ℝ] tangent_space IG φ.value :=
@quotient.hrec_on _ (germ_setoid (𝓝 x) N)
  (λ φ : germ (𝓝 x) N, tangent_space I x →L[ℝ] tangent_space IG φ.value) φ (λ f, mfderiv I IG f x)
(λ f g hfg, heq_of_eq (eventually_eq.mfderiv_eq hfg : _))

variable {I}
lemma smooth_germ.cont_mdiff_at {x : M} (φ : smooth_germ I x) {n : ℕ∞} :
  (φ : germ (𝓝 x) ℝ).cont_mdiff_at I n :=
by { rcases φ with ⟨_, g, rfl⟩, apply g.smooth.of_le le_top }

lemma filter.germ.cont_mdiff_at.add {x : M} {φ ψ : germ (𝓝 x) F} {n : ℕ∞}
(hφ : φ.cont_mdiff_at I n) (hψ : ψ.cont_mdiff_at I n) :
  (φ + ψ).cont_mdiff_at I n :=
germ.induction_on φ (λ f hf, germ.induction_on ψ (λ g hg, hf.add hg)) hφ hψ

lemma filter.germ.cont_mdiff_at.smul {x : M} {φ : germ (𝓝 x) ℝ} {ψ : germ (𝓝 x) F} {n : ℕ∞}
  (hφ : φ.cont_mdiff_at I n) (hψ : ψ.cont_mdiff_at I n) : (φ • ψ).cont_mdiff_at I n :=
germ.induction_on φ (λ f hf, germ.induction_on ψ (λ g hg, hf.smul hg)) hφ hψ

lemma filter.germ.cont_mdiff_at.sum {x : M} {ι} {s : finset ι} {n : ℕ∞} {f : ι → germ (𝓝 x) F}
(h : ∀ i ∈ s, (f i).cont_mdiff_at I n) : (∑ i in s, f i).cont_mdiff_at I n :=
begin
  classical,
  induction s using finset.induction_on with φ s hφs hs,
  { rw [finset.sum_empty], exact cont_mdiff_at_const },
  simp only [finset.mem_insert, forall_eq_or_imp] at h,
  rw finset.sum_insert hφs,
  exact h.1.add (hs h.2)
end

variable (I)

lemma really_convex_cont_mdiff_at (x : M) (n : ℕ∞) :
  really_convex (smooth_germ I x) {φ : germ (𝓝 x) F | φ.cont_mdiff_at I n} :=
begin
  classical,
  rw [nontrivial.really_convex_iff],
  rintros w w_pos w_supp w_sum,
  have : (support w).finite := support_finite_of_finsum_eq_one w_sum,
  let fin_supp := this.to_finset,
  have : support (λ (i : (𝓝 x).germ F), w i • i) ⊆ fin_supp,
  { rw set.finite.coe_to_finset, exact support_smul_subset_left w id },
  rw finsum_eq_sum_of_support_subset _ this, clear this,
  apply filter.germ.cont_mdiff_at.sum,
  intros φ hφ,
  refine (smooth_germ.cont_mdiff_at _).smul (w_supp _),
  simpa [fin_supp] using hφ
end

lemma exists_cont_mdiff_of_convex
  {P : M → F → Prop} (hP : ∀ x, convex ℝ {y | P x y})
  {n : ℕ∞}
  (hP' : ∀ x : M, ∃ U ∈ 𝓝 x, ∃ f : M → F, 𝓒_on n f U ∧ ∀ x ∈ U, P x (f x)) :
  ∃ f : M → F, 𝓒 n f ∧ ∀ x, P x (f x) :=
begin
  let PP : (Σ x : M, germ (𝓝 x) F) → Prop := λ p, p.2.cont_mdiff_at I n ∧ P p.1 p.2.value,
  have hPP : ∀ x, really_convex (smooth_germ I x) {φ | PP ⟨x, φ⟩},
  { intros x,
    apply really_convex.inter,
    apply really_convex_cont_mdiff_at,
    dsimp only,
    let v : germ (𝓝 x) F →ₛₗ[smooth_germ.value_ring_hom I x] F := filter.germ.valueₛₗ I x,
    change really_convex (smooth_germ I x) (v ⁻¹' {y | P x y}),
    dsimp only [← smooth_germ.value_order_ring_hom_to_ring_hom] at v,
    apply really_convex.preimageₛₗ,
    rw [really_convex_iff_convex],
    apply hP },
  have hPP' : ∀ x, ∃ f : M → F, ∀ᶠ x' in 𝓝 x, PP ⟨x', f⟩,
  { intro x,
    rcases hP' x with ⟨U, U_in, f, hf, hf'⟩,
    use f,
    filter_upwards [eventually_mem_nhds.mpr U_in] with y hy,
    exact ⟨hf.cont_mdiff_at hy, hf' y (mem_of_mem_nhds hy)⟩ },
  rcases exists_of_convex hPP hPP' with ⟨f, hf⟩,
  exact ⟨f, λ x, (hf x).1, λ x, (hf x).2⟩
end

lemma exists_cont_diff_of_convex
  {P : E → F → Prop} (hP : ∀ x, convex ℝ {y | P x y})
  {n : ℕ∞}
  (hP' : ∀ x : E, ∃ U ∈ 𝓝 x, ∃ f : E → F, cont_diff_on ℝ n f U ∧ ∀ x ∈ U, P x (f x)) :
  ∃ f : E → F, cont_diff ℝ n f ∧ ∀ x, P x (f x) :=
begin
  simp_rw ← cont_mdiff_iff_cont_diff,
  simp_rw ← cont_mdiff_on_iff_cont_diff_on  at ⊢ hP',
  exact exists_cont_mdiff_of_convex hP hP'
end
end

section

variables {E₁ E₂ E₃ E₄ F : Type*}
variables [normed_add_comm_group E₁] [normed_space ℝ E₁] [finite_dimensional ℝ E₁]
variables [normed_add_comm_group E₂] [normed_space ℝ E₂] [finite_dimensional ℝ E₂]
variables [normed_add_comm_group E₃] [normed_space ℝ E₃] [finite_dimensional ℝ E₃]
variables [normed_add_comm_group E₄] [normed_space ℝ E₄] [finite_dimensional ℝ E₄]
variables [normed_add_comm_group F] [normed_space ℝ F]

variables {H₁ M₁ H₂ M₂ H₃ M₃ H₄ M₄ : Type*}
variables [topological_space H₁] (I₁ : model_with_corners ℝ E₁ H₁)
variables [topological_space M₁] [charted_space H₁ M₁] [smooth_manifold_with_corners I₁ M₁]
variables [sigma_compact_space M₁] [t2_space M₁]
variables [topological_space H₂] (I₂ : model_with_corners ℝ E₂ H₂)
variables [topological_space M₂] [charted_space H₂ M₂] [smooth_manifold_with_corners I₂ M₂]
variables [topological_space H₃] (I₃ : model_with_corners ℝ E₃ H₃)
variables [topological_space M₃] [charted_space H₃ M₃] [smooth_manifold_with_corners I₃ M₃]
variables [topological_space H₄] (I₄ : model_with_corners ℝ E₄ H₄)
variables [topological_space M₄] [charted_space H₄ M₄] [smooth_manifold_with_corners I₄ M₄]

local notation `𝓒` := cont_mdiff (I₁.prod I₂) 𝓘(ℝ, F)
local notation `𝓒_on` := cont_mdiff_on (I₁.prod I₂) 𝓘(ℝ, F)

/- TODO: generalize the next def? -/
def filter.germ.cont_mdiff_at_prod {x : M₁} (φ : germ (𝓝 x) $ M₂ → F) (n : ℕ∞) : Prop :=
quotient.lift_on' φ (λ f, ∀ y : M₂, cont_mdiff_at (I₁.prod I₂) 𝓘(ℝ, F) n (uncurry f) (x, y))
  (λ f g h, propext begin
  change {x' | f x' = g x'} ∈ 𝓝 x at h,
  split,
  all_goals
  { refine λ H y, (H y).congr_of_eventually_eq _,
    clear H,
    replace h : {x' | f x' = g x'} ×ˢ (univ : set M₂) ∈ (𝓝 x) ×ᶠ (𝓝 y) := prod_mem_prod h univ_mem,
    rw ← nhds_prod_eq at h,
    apply mem_of_superset h,
    rintros ⟨x', y'⟩ ⟨(hx' : f x' = g x'), -⟩,
    simp only [mem_set_of_eq, uncurry_apply_pair],
    apply congr_fun, },
  exacts [hx'.symm, hx']
end)

/- potential generalization of the above
def filter.germ.cont_mdiff_at_comp {x : M₁} (φ : germ (𝓝 x) M₂) (n : ℕ∞)
  (g : M₂ → M₃) (h : M₄ → M₁) : Prop :=
quotient.lift_on' φ (λ f, ∀ y ∈ h⁻¹' {x}, cont_mdiff_at I₄ I₃ n (g ∘ f ∘ h) y) (λ f g h, propext begin
  change {x' | f x' = g x'} ∈ 𝓝 x at h,
  split,
  all_goals
  { refine λ H y, (H y).congr_of_eventually_eq _,
    clear H,
    replace h : {x' | f x' = g x'} ×ˢ (univ : set M₂) ∈ (𝓝 x) ×ᶠ (𝓝 y) := prod_mem_prod h univ_mem,
    rw ← nhds_prod_eq at h,
    apply mem_of_superset h,
    rintros ⟨x', y'⟩ ⟨(hx' : f x' = g x'), -⟩,
    simp only [mem_set_of_eq, uncurry_apply_pair],
    apply congr_fun, },
  exacts [hx'.symm, hx']
end)
-/

variables {I₁ I₂}
lemma filter.germ.cont_mdiff_at_prod.add {x : M₁} {φ ψ : germ (𝓝 x) $ M₂ → F} {n : ℕ∞}
  (hφ : φ.cont_mdiff_at_prod I₁ I₂ n) (hψ : ψ.cont_mdiff_at_prod I₁ I₂ n) :
  (φ + ψ).cont_mdiff_at_prod I₁ I₂ n :=
germ.induction_on φ (λ f hf, germ.induction_on ψ (λ g hg y, (hf y).add (hg y))) hφ hψ

lemma filter.germ.cont_mdiff_at_prod.smul {x : M₁} {φ : germ (𝓝 x) $ M₂ → ℝ}
  {ψ : germ (𝓝 x) $ M₂ → F} {n : ℕ∞}
  (hφ : φ.cont_mdiff_at_prod I₁ I₂ n) (hψ : ψ.cont_mdiff_at_prod I₁ I₂ n) :
  (φ • ψ).cont_mdiff_at_prod I₁ I₂ n :=
germ.induction_on φ (λ f hf, germ.induction_on ψ (λ g hg y, (hf y).smul (hg y))) hφ hψ

lemma filter.germ.cont_mdiff_at.smul_prod {x : M₁} {φ : germ (𝓝 x) ℝ}
  {ψ : germ (𝓝 x) $ M₂ → F} {n : ℕ∞}
  (hφ : φ.cont_mdiff_at I₁ n) (hψ : ψ.cont_mdiff_at_prod I₁ I₂ n) :
  (φ • ψ).cont_mdiff_at_prod I₁ I₂ n :=
germ.induction_on φ (λ f hf, germ.induction_on ψ
  (λ g hg y, cont_mdiff_at.smul (cont_mdiff_at.comp _ hf cont_mdiff_at_fst) (hg y))) hφ hψ

lemma filter.germ.cont_mdiff_at_prod.sum {x : M₁} {ι} {s : finset ι} {n : ℕ∞}
  {f : ι → germ (𝓝 x) (M₂ → F)}
  (h : ∀ i ∈ s, (f i).cont_mdiff_at_prod I₁ I₂ n) : (∑ i in s, f i).cont_mdiff_at_prod I₁ I₂ n :=
begin
  classical,
  induction s using finset.induction_on with φ s hφs hs,
  { rw [finset.sum_empty], intro y, exact cont_mdiff_at_const },
  simp only [finset.mem_insert, forall_eq_or_imp] at h,
  rw finset.sum_insert hφs,
  exact h.1.add (hs h.2)
end

lemma really_convex_cont_mdiff_at_prod {x : M₁} (n : ℕ∞) :
  really_convex (smooth_germ I₁ x) {φ : germ (𝓝 x) (M₂ → F) | φ.cont_mdiff_at_prod I₁ I₂ n} :=
begin
  classical,
  rw [nontrivial.really_convex_iff],
  rintros w w_pos w_supp w_sum,
  have : (support w).finite := support_finite_of_finsum_eq_one w_sum,
  let fin_supp := this.to_finset,
  have : support (λ (i : (𝓝 x).germ (M₂ → F)), w i • i) ⊆ fin_supp,
  { rw set.finite.coe_to_finset,
    exact support_smul_subset_left w id },
  rw finsum_eq_sum_of_support_subset _ this, clear this,
  apply filter.germ.cont_mdiff_at_prod.sum,
  intros φ hφ,
  refine (smooth_germ.cont_mdiff_at _).smul_prod (w_supp _),
  simpa [fin_supp] using hφ
end

@[main_declaration]
lemma exists_cont_mdiff_of_convex₂
  {P : M₁ → (M₂ → F) → Prop} (hP : ∀ x, convex ℝ {f | P x f}) {n : ℕ∞}
  (hP' : ∀ x : M₁, ∃ (U ∈ 𝓝 x) (f : M₁ → M₂ → F),
    𝓒_on n (uncurry f) (U ×ˢ (univ : set M₂)) ∧ ∀ y ∈ U, P y (f y)) :
  ∃ f : M₁ → M₂ → F, 𝓒 n (uncurry f) ∧ ∀ x, P x (f x) :=
begin
  let PP : (Σ x : M₁, germ (𝓝 x) (M₂ → F)) → Prop :=
    λ p, p.2.cont_mdiff_at_prod I₁ I₂ n ∧ P p.1 p.2.value,
  have hPP : ∀ x, really_convex (smooth_germ I₁ x) {φ | PP ⟨x, φ⟩},
  { intros x,
    apply really_convex.inter,
    apply really_convex_cont_mdiff_at_prod,
    dsimp only,
    let v : germ (𝓝 x) (M₂ → F) →ₛₗ[smooth_germ.value_ring_hom I₁ x] (M₂ → F) :=
      filter.germ.valueₛₗ I₁ x,
    change really_convex (smooth_germ I₁ x) (v ⁻¹' {y | P x y}),
    dsimp only [← smooth_germ.value_order_ring_hom_to_ring_hom] at v,
    apply really_convex.preimageₛₗ,
    rw [really_convex_iff_convex],
    apply hP },
  have hPP' : ∀ x, ∃ f : M₁ → M₂ → F, ∀ᶠ x' in 𝓝 x, PP ⟨x', f⟩,
  { intro x,
    rcases hP' x with ⟨U, U_in, f, hf, hf'⟩,
    use f,
    filter_upwards [eventually_mem_nhds.mpr U_in] with y hy,
    refine ⟨λz, hf.cont_mdiff_at (prod_mem_nhds hy univ_mem), hf' y (mem_of_mem_nhds hy)⟩ },
  rcases exists_of_convex hPP hPP' with ⟨f, hf⟩,
  exact ⟨f, λ ⟨x, y⟩, (hf x).1 y, λ x, (hf x).2⟩
end

lemma exists_cont_diff_of_convex₂
  {P : E₁ → (E₂ → F) → Prop} (hP : ∀ x, convex ℝ {f | P x f}) {n : ℕ∞}
  (hP' : ∀ x : E₁, ∃ (U ∈ 𝓝 x) (f : E₁ → E₂ → F),
    cont_diff_on ℝ n (uncurry f) (U ×ˢ (univ : set E₂)) ∧ ∀ y ∈ U, P y (f y)) :
  ∃ f : E₁ → E₂ → F, cont_diff ℝ n (uncurry f) ∧ ∀ x, P x (f x) :=
begin
  simp_rw [← cont_mdiff_on_iff_cont_diff_on, model_with_corners_self_prod] at hP',
  simp_rw [← cont_mdiff_iff_cont_diff, model_with_corners_self_prod],
  rw [← charted_space_self_prod] at hP' ⊢, -- Why does `simp_rw` not succeed here?
  exact exists_cont_mdiff_of_convex₂ 𝓘(ℝ, E₁) 𝓘(ℝ, E₂) hP hP',
end
end

section
variables {ι : Type*}
variables {E : Type*} [normed_add_comm_group E] [normed_space ℝ E] [finite_dimensional ℝ E]
  {H : Type*} [topological_space H] {I : model_with_corners ℝ E H} {M : Type*}
  [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
  [sigma_compact_space M] [t2_space M]

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

variables {F : Type*} [normed_add_comm_group F] [normed_space ℝ F]

lemma convex_set_of_imp_eq (P : Prop) (y : F) : convex ℝ {x : F | P → x = y } :=
by by_cases hP : P; simp [hP, convex_singleton, convex_univ]

-- lemma exists_smooth_and_eq_on_aux1 {f : E → F} {ε : E → ℝ} (hf : continuous f)
--   (hε : continuous ε) (h2ε : ∀ x, 0 < ε x) (x₀ : E) :
--   ∃ U ∈ 𝓝 x₀, ∀ x ∈ U, dist (f x₀) (f x) < ε x :=
-- begin
--   have h0 : ∀ x, dist (f x) (f x) < ε x := λ x, by simp_rw [dist_self, h2ε],
--   refine ⟨_, (is_open_lt (continuous_const.dist hf) hε).mem_nhds $ h0 x₀, λ x hx, hx⟩
-- end

-- lemma exists_smooth_and_eq_on_aux2 {n : ℕ∞} {f : E → F} {ε : E → ℝ} (hf : continuous f)
--   (hε : continuous ε) (h2ε : ∀ x, 0 < ε x)
--   {s : set E} (hs : is_closed s) (hfs : ∃ U ∈ 𝓝ˢ s, cont_diff_on ℝ n f U)
--   (x₀ : E) :
--   ∃ U ∈ 𝓝 x₀, ∀ x ∈ U, dist (f x₀) (f x) < ε x :=
-- begin
--   have h0 : ∀ x, dist (f x) (f x) < ε x := λ x, by simp_rw [dist_self, h2ε],
--   refine ⟨_, (is_open_lt (continuous_const.dist hf) hε).mem_nhds $ h0 x₀, λ x hx, hx⟩
-- end

lemma exists_smooth_and_eq_on {n : ℕ∞} {f : E → F} {ε : E → ℝ} (hf : continuous f)
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

end
