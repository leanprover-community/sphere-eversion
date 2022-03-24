import notations
import loops.surrounding
import analysis.calculus.specific_functions
import measure_theory.integral.periodic
import geometry.manifold.partition_of_unity
import to_mathlib.order.hom.basic
import to_mathlib.geometry.manifold.partition_of_unity

/-!
# The reparametrization lemma
-/

section to_mathlib

open_locale topological_space

variables {𝕜 E F : Type*} [nondiscrete_normed_field 𝕜]
variables [normed_group E] [normed_space 𝕜 E] [normed_group F] [normed_space 𝕜 F]

lemma cont_diff_on_iff_of_eq_on
  {n : with_top ℕ} {s : set E} (hs : is_open s) (f g : E → F) (h : ∀ x ∈ s, f x = g x) :
  cont_diff_on 𝕜 n f s ↔ cont_diff_on 𝕜 n g s :=
sorry

end to_mathlib

noncomputable theory

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

Given `x : E`, it represents a smooth probability distribution on the circle with the property that:
`∫ s in 0..1, γ.local_centering_density x y s • γ y s = g y`
for all `y` in a neighbourhood of `x` (see `local_centering_density_average` below).

This property is obtained by combining smoothness of barycentric coordinates with the fact that
`g x` lies in the _interior_ of a convex hull.

The intuition is that given `y : E` in a neighbourhood of `x`, since `γ y` surrounds `g y`, there
are real numbers `t₁`, ..., `tₙ` (depending on `y`) such that `g y` is in the interior of the convex
hull of `γ y tᵢ`, which are an affine basis. One defines `local_centering_density x y`, for `y` in a
neighbourhood of `x`, so that `local_centering_density x y t` has almost all of its mass
concentrated at the values `t = tᵢ` with each value getting a share of the total mass proportional
to the barycentric coordinate of `g y`. -/
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

lemma local_centering_density_smooth_on :
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
  exact ((γ.local_centering_density_smooth_on x).continuous_on.continuous_at hyt).comp
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
for all `x : E` (see `centering_density_average` below).

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

lemma centering_density_eq_exists_pou_nhd_finset_sum :
  ∃ (p : smooth_partition_of_unity E 𝓘(ℝ, E) E)
    (hp : p.is_subordinate γ.local_centering_density_nhd),
    ∀ (x : E), ∃ (ys : finset E) {n : set E} (hn₀ : is_open n) (hn₁ : n ∈ 𝓝 x)
      (hn₂ : n ⊆ ⋂ y ∈ ys, γ.local_centering_density_nhd y),
      ∀ (z ∈ n) t, γ.centering_density z t = ∑ y in ys, p y z * γ.local_centering_density y z t :=
begin
  sorry,
end

@[simp] lemma centering_density_pos (t : ℝ) :
  0 < γ.centering_density x t :=
sorry

lemma centering_density_periodic :
  periodic (γ.centering_density x) 1 :=
sorry

lemma centering_density_smooth :
  -- 𝒞 ∞ ↿γ.centering_density :=
  𝒞 ∞ $ uncurry (λ x t, γ.centering_density x t) :=
begin
  obtain ⟨p, hp, hp'⟩ := γ.centering_density_eq_exists_pou,
  rw cont_diff_iff_cont_diff_at,
  rintros ⟨x, t⟩,
  obtain ⟨p, hp, hp'⟩ := γ.centering_density_eq_exists_pou_nhd_finset_sum,
  obtain ⟨ys, n, hn₀, hn₁, hn₂, hn₃⟩ := hp' x,
  have hn₄ : n ×ˢ (univ : set ℝ) ∈ 𝓝 (x, t) :=
    mem_nhds_prod_iff.mpr ⟨n, hn₁, univ, filter.univ_mem, rfl.subset⟩,
  refine cont_diff_within_at.cont_diff_at
    (cont_diff_on.cont_diff_within_at _ (mem_of_mem_nhds hn₄)) hn₄,
  let f : E × ℝ → ℝ := λ zt, ∑ y in ys, p y zt.1 * γ.local_centering_density y zt.1 zt.2,
  have hf : ∀ zs ∈ n ×ˢ (univ : set ℝ), (uncurry γ.centering_density) zs = f zs,
  { rintros ⟨z, s⟩ hz,
    simp only [prod_mk_mem_set_prod_eq, mem_univ, and_true] at hz,
    simp [hn₃ z hz s], },
  replace hn₀ : is_open (n ×ˢ (univ : set ℝ)) := hn₀.prod is_open_univ,
  rw cont_diff_on_iff_of_eq_on hn₀ _ f hf,
  refine cont_diff_on.sum (λ y hy, cont_diff_on.mul (cont_diff.cont_diff_on _) _),
  { refine cont_diff.comp _ cont_diff_fst,
    rw ← cont_mdiff_iff_cont_diff,
    exact (p y).cont_mdiff, },
  { suffices : n ×ˢ (univ : set ℝ) ⊆ (γ.local_centering_density_nhd y) ×ˢ (univ : set ℝ),
    { exact (γ.local_centering_density_smooth_on y).mono this, },
    simp only [subset_Inter₂_iff] at hn₂,
    exact prod_mono (hn₂ y hy) rfl.subset, },
end

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
    { suffices : x ∉ support (p y), { simp [nmem_support.mp this], },
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
