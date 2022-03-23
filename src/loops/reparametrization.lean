import notations
import loops.surrounding
import analysis.calculus.specific_functions
import measure_theory.integral.periodic
import geometry.manifold.partition_of_unity
import to_mathlib.order.hom.basic

/-!
# The reparametrization lemma
-/

noncomputable theory

section finprod

open_locale big_operators
open function

variables {α M : Type*} [comm_monoid M]

-- Better version of `finprod_eq_prod_of_mul_support_to_finset_subset`
@[to_additive] lemma finprod_eq_prod_of_mul_support_to_finset_subset'
  (f : α → M) {s : finset α} (h : mul_support f ⊆ (s : set α)) :
  ∏ᶠ i, f i = ∏ i in s, f i :=
begin
  have h' : (s.finite_to_set.subset h).to_finset ⊆ s,
  { erw [← finset.coe_subset, set.coe_to_finset],
    exact h, },
  exact finprod_eq_prod_of_mul_support_to_finset_subset _ _ h',
end

end finprod

namespace partition_of_unity

open_locale big_operators

variables {ι X F : Type*} {U : ι → set X} {s : set X} [topological_space X]
variables (p : partition_of_unity ι X s) (hp : p.is_subordinate U)
variables (f : ι → X → F) (g : X → F)
include hp

lemma finsum_smul_eq [add_comm_group F] [module ℝ F]
  (hfg : ∀ i x, x ∈ s ∩ U i → f i x = g x) {x : X} (hx : x ∈ s) :
  ∑ᶠ i, p i x • f i x = g x :=
begin
  suffices : ∀ i, p i x • f i x = p i x • g x,
  { simp_rw [this, ← finsum_smul, p.sum_eq_one hx, one_smul], },
  intros i,
  by_cases hxi : x ∈ U i,
  { rw hfg i x (set.mem_inter hx hxi), },
  { suffices : x ∉ function.support (p i),
    { simp only [function.mem_support, not_not] at this,
      simp [this], },
    exact λ contra, hxi (hp i (subset_tsupport _ contra)), },
end

end partition_of_unity

namespace smooth_partition_of_unity

open_locale big_operators

variables {ι E H M F : Type*} {U : ι → set M} {s : set M}
variables [normed_group E] [normed_space ℝ E] [finite_dimensional ℝ E]
variables [topological_space H] {J : model_with_corners ℝ E H}
variables [topological_space M] [charted_space H M] [smooth_manifold_with_corners J M]
variables (p : smooth_partition_of_unity ι J M s) (hp : p.is_subordinate U)
variables (f : ι → M → F) (g : M → F)

lemma finsum_smul_eq [add_comm_group F] [module ℝ F]
  (hfg : ∀ i x, x ∈ s ∩ U i → f i x = g x) {x : M} (hx : x ∈ s) :
  ∑ᶠ i, p i x • f i x = g x :=
p.to_partition_of_unity.finsum_smul_eq hp f g hfg hx

end smooth_partition_of_unity

namespace interval_integral

open_locale big_operators
open function

variables {α E : Type*} {a b : α}
variables [linear_order α] [measurable_space α] [measurable_space E] [normed_group E]
variables [topological_space.second_countable_topology E] [complete_space E] [normed_space ℝ E]
variables [borel_space E] {μ : measure_theory.measure α}

variables [topological_space α] [compact_Icc_space α] [measure_theory.is_locally_finite_measure μ]

lemma _root_.interval_integrable.sum {ι : Type*} (s : finset ι) {f : ι → α → E}
  (hf : ∀ i ∈ s, interval_integrable (f i) μ a b) :
  interval_integrable (∑ i in s, f i) μ a b :=
begin
  classical,
  revert hf,
  refine s.induction _ (λ i t hi ih, _),
  { simp [pi.zero_def],
    exact @interval_integrable_const α E _ _ _ _ _ _ μ _ a b 0, },
  { intros hf,
    simp only [finset.sum_insert hi],
    refine interval_integrable.add (hf i _) (ih (λ j hj, hf j _)),
    exacts [finset.mem_insert.mpr (or.inl rfl), finset.mem_insert.mpr (or.inr hj)], },
end

lemma integral_sum {ι : Type*} (s : finset ι) {f : ι → α → E}
  (hf : ∀ i ∈ s, interval_integrable (f i) μ a b) :
  ∫ x in a..b, (∑ i in s, f i x) ∂μ = ∑ i in s, ∫ x in a..b, f i x ∂μ :=
begin
  classical,
  revert hf,
  refine s.induction _ (λ i t hi ih, _),
  { simp, },
  { intros hf,
    simp only [finset.sum_insert hi],
    have : interval_integrable (λ x, ∑ j in t, f j x) μ a b,
    { simp_rw ← finset.sum_apply,
      exact interval_integrable.sum t (λ i hi, hf i (finset.mem_insert.mpr (or.inr hi))), },
    rw [integral_add (hf i _) this, ih (λ j hj, hf j _)],
    exacts [finset.mem_insert.mpr (or.inr hj), finset.mem_insert.mpr (or.inl rfl)], },
end

lemma integral_finsum {ι : Type*} {f : ι → α → E}
  (hf : ∀ i, interval_integrable (f i) μ a b)
  (hf' : (support f).finite) :
  ∫ x in a..b, (∑ᶠ i, f i x) ∂μ = ∑ᶠ i, ∫ x in a..b, f i x ∂μ :=
begin
  haveI : fintype (support f) := hf'.fintype,
  let s := (support f).to_finset,
  have h₁ : ∀ x, ∑ᶠ i, f i x = ∑ i in s, f i x,
  { intros x,
    suffices : support (λ i, f i x) ⊆ s,
    { exact finsum_eq_sum_of_support_to_finset_subset' _ this, },
    intros i hi,
    simp only [set.coe_to_finset, mem_support] at hi ⊢,
    exact λ contra, by simpa [congr_fun contra x] using hi, },
  suffices : support (λ i, ∫ x in a..b, f i x ∂μ) ⊆ s,
  { simp_rw [h₁, integral_sum s (λ i _, hf i), finsum_eq_sum_of_support_to_finset_subset' _ this] },
  intros i hi,
  simp only [set.coe_to_finset, mem_support] at hi ⊢,
  intros contra,
  erw [contra, interval_integral.integral_zero] at hi,
  contradiction,
end

end interval_integral

open set function measure_theory interval_integral
open_locale topological_space unit_interval manifold big_operators

variables {E F : Type*}
variables [normed_group E] [normed_space ℝ E] [finite_dimensional ℝ E]
variables [normed_group F] [normed_space ℝ F] [finite_dimensional ℝ F]
variables [measurable_space F] [borel_space F]

structure smooth_surrounding_family (g : E → F) :=
(to_fun : E → loop F)
(smooth : 𝒞 ∞ ↿to_fun)
(surrounds : ∀ x, (to_fun x).surrounds $ g x)

namespace smooth_surrounding_family

variables {g : E → F} (γ : smooth_surrounding_family g) (x y : E)

instance : has_coe_to_fun (smooth_surrounding_family g) (λ _, E → loop F) := ⟨to_fun⟩

protected lemma continuous : continuous (γ x) :=
begin
  apply continuous_uncurry_left x,
  exact γ.smooth.continuous,
end

include γ x
/- This is an auxiliary definition to help construct `centering_density` below.

It represents a smooth probability distribution on the circle with the property that:
`∫ s in 0..1, γ.local_centering_density x y s • γ y s = g y`
for all `y` in a neighbourhood of `x` (see `local_centering_density_average` below).

This property is obtained by combining smoothness of barycentric coordinates with the fact that
`g x` lies in the _interior_ of a convex hull.

The intuition is that given `x : E`, since `γ x` surrounds `g x`, there are real numbers
`t₁`, ..., `tₙ` such that `g x` is in the interior of the convex hull of `γ x tᵢ`, which are an
affine basis. One defines `local_centering_density x y`, for `y` in a neighbourhood of `x`, so that
`local_centering_density x y t` has almost all of its mass concentrated at the values `t = tᵢ` with
each value getting a share of the total mass proportional to the barycentric coordinate of `g y`. -/
def local_centering_density : E → ℝ → ℝ :=
sorry

def local_centering_density_nhd : set E :=
sorry
omit x

lemma local_centering_density_nhd_is_open :
  is_open $ γ.local_centering_density_nhd x :=
sorry

lemma local_centering_density_nhd_self_mem :
  x ∈ γ.local_centering_density_nhd x :=
sorry

lemma local_centering_density_nhd_covers :
  univ ⊆ ⋃ x, γ.local_centering_density_nhd x :=
λ x hx, mem_Union.mpr ⟨x, γ.local_centering_density_nhd_self_mem x⟩

@[simp] lemma local_centering_density_pos (t : ℝ) (hy : y ∈ γ.local_centering_density_nhd x) :
  0 < γ.local_centering_density x y t :=
sorry

lemma local_centering_density_periodic (hy : y ∈ γ.local_centering_density_nhd x) :
  periodic (γ.local_centering_density x y) 1 :=
sorry

lemma local_centering_density_smooth :
  cont_diff_on ℝ ∞ ↿(γ.local_centering_density x) $
    (γ.local_centering_density_nhd x) ×ˢ (univ : set ℝ) :=
sorry

lemma local_centering_density_continuous (hy : y ∈ γ.local_centering_density_nhd x) :
  continuous (λ t, γ.local_centering_density x y t) :=
begin
  refine continuous_iff_continuous_at.mpr (λ t, _),
  have hyt : γ.local_centering_density_nhd x ×ˢ univ ∈ 𝓝 (y, t) :=
    mem_nhds_prod_iff'.mpr ⟨γ.local_centering_density_nhd x, univ,
      γ.local_centering_density_nhd_is_open x, hy, is_open_univ, mem_univ t, rfl.subset⟩,
  exact ((γ.local_centering_density_smooth x).continuous_on.continuous_at hyt).comp
    (continuous.prod.mk y).continuous_at,
end

@[simp] lemma local_centering_density_integral_eq_one (hy : y ∈ γ.local_centering_density_nhd x) :
  ∫ s in 0..1, γ.local_centering_density x y s = 1 :=
sorry

@[simp] lemma local_centering_density_average (hy : y ∈ γ.local_centering_density_nhd x) :
  ∫ s in 0..1, γ.local_centering_density x y s • γ y s = g y :=
sorry

/-- This the key construction. It represents a smooth probability distribution on the circle with
the property that:
`∫ s in 0..1, γ.centering_density x s • γ x s = g x`
(see `centering_density_average` below).

It is constructed from `local_centering_density` using a partition of unity
(see `centering_density_eq_exists_pou` below). -/
def centering_density : E → ℝ → ℝ :=
begin
  choose p hp using
    @smooth_partition_of_unity.exists_is_subordinate _ _ _ _ _ _ _ 𝓘(ℝ, E) _ _ _ _ _ _ _
    is_closed_univ (γ.local_centering_density_nhd) (γ.local_centering_density_nhd_is_open)
    γ.local_centering_density_nhd_covers,
  exact λ x t, ∑ᶠ (y : E), (p y x) * γ.local_centering_density y x t,
end
omit γ

lemma centering_density_eq_exists_pou :
  ∃ (p : smooth_partition_of_unity E 𝓘(ℝ, E) E)
    (hp : p.is_subordinate γ.local_centering_density_nhd),
    ∀ x t, γ.centering_density x t = ∑ᶠ y, (p y x) * γ.local_centering_density y x t :=
let h := @smooth_partition_of_unity.exists_is_subordinate _ _ _ _ _ _ _ 𝓘(ℝ, E) _ _ _ _ _ _ _
  is_closed_univ (γ.local_centering_density_nhd) (γ.local_centering_density_nhd_is_open)
  γ.local_centering_density_nhd_covers in
⟨classical.some h, classical.some_spec h, λ x y, rfl⟩

@[simp] lemma centering_density_pos (t : ℝ) :
  0 < γ.centering_density x t :=
sorry

lemma centering_density_periodic :
  periodic (γ.centering_density x) 1 :=
sorry

lemma centering_density_smooth :
  𝒞 ∞ ↿γ.centering_density :=
sorry

@[simp] lemma centering_density_integral_eq_one :
  ∫ s in 0..1, γ.centering_density x s = 1 :=
sorry

@[simp] lemma centering_density_average :
  ∫ s in 0..1, γ.centering_density x s • γ x s = g x :=
begin
  obtain ⟨p, hp, hp'⟩ := γ.centering_density_eq_exists_pou,
  have h_int : ∀ y, interval_integrable
    (λ t, p y x • γ.local_centering_density y x t • γ x t) volume 0 1,
  { intros y,
    by_cases hy : x ∈ γ.local_centering_density_nhd y,
    { refine continuous.interval_integrable (continuous.const_smul _ (p y x)) _ _,
      refine continuous.smul _ (γ.smooth.continuous.comp (continuous.prod.mk x)),
      exact γ.local_centering_density_continuous _ _ hy, },
    { suffices : p y x = 0, { simp [this], },
      rw ← nmem_support,
      exact λ contra, hy (hp _ (subset_tsupport _ contra)), }, },
  have h_supp : (support (λ y t, p y x • γ.local_centering_density y x t • γ x t)).finite,
  { refine set.finite.subset (p.locally_finite.point_finite x) (λ y hy, _),
    simp only [ne.def, mem_set_of_eq, mem_support],
    intros contra,
    simpa only [mem_support, contra, zero_smul, ne.def, pi.zero_def] using hy, },
  simp_rw [hp', finsum_smul, mul_smul, integral_finsum h_int h_supp,
    interval_integral.integral_smul],
  suffices : ∀ (y x : E), x ∈ univ ∩ γ.local_centering_density_nhd y →
    ∫ s in 0..1, γ.local_centering_density y x s • γ x s = g x,
  { exact p.finsum_smul_eq hp _ _ this (mem_univ x), },
  intros y x' hx',
  simp only [univ_inter] at hx',
  exact γ.local_centering_density_average _ _ hx',
end

lemma centering_density_continuous :
  continuous (γ.centering_density x) :=
begin
  apply continuous_uncurry_left x,
  exact γ.centering_density_smooth.continuous,
end

lemma centering_density_interval_integrable (t₁ t₂ : ℝ) :
  interval_integrable (γ.centering_density x) volume t₁ t₂ :=
(γ.centering_density_continuous x).interval_integrable t₁ t₂

@[simp] lemma integral_add_one_centering_density (t : ℝ) :
  ∫ s in 0..t+1, γ.centering_density x s = (∫ s in 0..t, γ.centering_density x s) + 1 :=
begin
  have h₁ := γ.centering_density_interval_integrable x 0 t,
  have h₂ := γ.centering_density_interval_integrable x t (t + 1),
  simp [← integral_add_adjacent_intervals h₁ h₂,
    (γ.centering_density_periodic x).interval_integral_add_eq t 0],
end

lemma strict_mono_integral_centering_density :
  strict_mono $ λ t, ∫ s in 0..t, γ.centering_density x s :=
begin
  intros t₁ t₂ ht₁₂,
  have h := γ.centering_density_interval_integrable x,
  rw [← sub_pos, integral_interval_sub_left (h 0 t₂) (h 0 t₁)],
  have hK : is_compact (Icc t₁ t₂) := is_compact_Icc,
  have hK' : (Icc t₁ t₂).nonempty := nonempty_Icc.mpr ht₁₂.le,
  obtain ⟨u, hu₁, hu₂⟩ := hK.exists_forall_le hK' (γ.centering_density_continuous x).continuous_on,
  refine lt_of_lt_of_le _ (integral_mono_on ht₁₂.le interval_integrable_const (h t₁ t₂) hu₂),
  simp [ht₁₂],
end

lemma surjective_integral_centering_density :
  surjective $ λ t, ∫ s in 0..t, γ.centering_density x s :=
begin
  have : continuous (λ t, ∫ s in 0..t, γ.centering_density x s),
  { exact continuous_primitive (γ.centering_density_interval_integrable x) 0, },
  apply this.surjective,
  { exact (γ.centering_density_periodic x).tendsto_at_top_interval_integral_of_pos'
      (γ.centering_density_interval_integrable x) (γ.centering_density_pos x) one_pos, },
  { exact (γ.centering_density_periodic x).tendsto_at_bot_interval_integral_of_pos'
      (γ.centering_density_interval_integrable x) (γ.centering_density_pos x) one_pos, },
end

def reparametrize : E → equivariant_equiv := λ x,
({ to_fun := λ t, ∫ s in 0..t, γ.centering_density x s,
  inv_fun := (strict_mono.order_iso_of_surjective _
    (γ.strict_mono_integral_centering_density x)
    (γ.surjective_integral_centering_density x)).symm,
  left_inv := strict_mono.order_iso_of_surjective_symm_apply_self _ _ _,
  right_inv := λ t, strict_mono.order_iso_of_surjective_self_symm_apply _ _ _ t,
  map_zero' := integral_same,
  eqv' := γ.integral_add_one_centering_density x, } : equivariant_equiv).symm

lemma coe_reparametrize_symm :
  ((γ.reparametrize x).symm : ℝ → ℝ) = λ t, ∫ s in 0..t, γ.centering_density x s :=
rfl

lemma reparametrize_symm_apply (t : ℝ) :
  (γ.reparametrize x).symm t = ∫ s in 0..t, γ.centering_density x s :=
rfl

@[simp] lemma integral_reparametrize (t : ℝ) :
  ∫ s in 0..(γ.reparametrize x t), γ.centering_density x s = t :=
by simp [← reparametrize_symm_apply]

lemma has_deriv_at_reparametrize_symm (s : ℝ) :
  has_deriv_at (γ.reparametrize x).symm (γ.centering_density x s) s :=
integral_has_deriv_at_right
  (γ.centering_density_interval_integrable x 0 s)
  ((γ.centering_density_continuous x).measurable_at_filter _ _)
  (γ.centering_density_continuous x).continuous_at

lemma reparametrize_smooth :
  -- 𝒞 ∞ ↿γ.reparametrize :=
  𝒞 ∞ $ uncurry (λ x t, γ.reparametrize x t) :=
sorry

@[simp] lemma reparametrize_average :
  ((γ x).reparam $ (γ.reparametrize x).equivariant_map).average = g x :=
begin
  change ∫ (s : ℝ) in 0..1, γ x (γ.reparametrize x s) = g x,
  have h₁ : ∀ s,
    s ∈ interval 0 (1 : ℝ) → has_deriv_at (γ.reparametrize x).symm (γ.centering_density x s) s :=
    λ s hs, γ.has_deriv_at_reparametrize_symm x s,
  have h₂ : continuous_on (λ s, γ.centering_density x s) (interval 0 1) :=
    (γ.centering_density_continuous x).continuous_on,
  have h₃ : continuous (λ s, γ x (γ.reparametrize x s)) :=
    (γ.continuous x).comp (continuous_uncurry_left x γ.reparametrize_smooth.continuous),
  rw [← (γ.reparametrize x).symm.map_zero, ← (γ.reparametrize x).symm.map_one,
    ← integral_comp_smul_deriv h₁ h₂ h₃],
  simp,
end

end smooth_surrounding_family
