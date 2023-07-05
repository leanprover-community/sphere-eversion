import geometry.manifold.partition_of_unity
import tactic.find_unused
import to_mathlib.geometry.manifold.cont_mdiff
import to_mathlib.geometry.manifold.algebra.smooth_germ
import to_mathlib.geometry.manifold.algebra.lie_group
import to_mathlib.analysis.convex.basic
import to_mathlib.topology.support
import to_mathlib.topology.locally_finite
import to_mathlib.topology.partition_of_unity

noncomputable theory

open_locale topological_space filter manifold big_operators
open set function filter


section
variables
  {ι : Type*} {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
  {H : Type*} [topological_space H] {I : model_with_corners ℝ E H} {M : Type*}
  [topological_space M] [charted_space H M]
  {s : set M} {F : Type*} [normed_add_comm_group F] [normed_space ℝ F]

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

end
