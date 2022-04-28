import analysis.calculus.specific_functions
import measure_theory.integral.periodic
import geometry.manifold.partition_of_unity

import notations
import loops.surrounding
import loops.delta_mollifier

import to_mathlib.geometry.manifold.partition_of_unity
import to_mathlib.analysis.cont_diff
import to_mathlib.analysis.normed_group

/-!
# The reparametrization lemma
-/

noncomputable theory

open set function measure_theory interval_integral filter
open_locale topological_space unit_interval manifold big_operators

variables {E F : Type*}
variables [normed_group E] [normed_space ℝ E] [finite_dimensional ℝ E]
variables [normed_group F] [normed_space ℝ F] [finite_dimensional ℝ F]
variables [measurable_space F] [borel_space F]

local notation `ι` := fin (finite_dimensional.finrank ℝ F + 1)

/-- An auxiliary lemma for bootstrapping to `tendsto_mollify_apply`. -/
lemma loop.tendsto_mollify_apply_aux (γ : E → loop F) (h : continuous ↿γ) (x : E) (t : ℝ)
  (hx : γ x = 0) :
  tendsto (λ (z : E × ℕ), (γ z.1).mollify z.2 t) ((𝓝 x).prod at_top) (𝓝 0) :=
begin
  suffices : tendsto (λ (z : E × ℕ), ∥(γ z.1).mollify z.2 t∥) ((𝓝 x).prod at_top) (𝓝 0),
  { exact this.of_norm_le (λ z, le_refl _), },
  suffices : tendsto (λ (z : E × ℕ), ⨆ (s : I), ∥γ z.1 s∥) ((𝓝 x).prod at_top) (𝓝 0),
  { refine this.of_norm_le _,
    rintros ⟨y, n⟩,
    simp only [norm_norm, loop.mollify],
    refine norm_integral_le_integral_norm_Ioc.trans _,
    simp only [interval_integral.integral_of_le zero_le_one, interval_oc_of_le (@zero_le_one ℝ _),
      norm_smul, real.norm_of_nonneg (delta_mollifier_pos _).le],
    rw ← interval_integral.integral_of_le (@zero_le_one ℝ _),
    let f₁ : ℝ → ℝ := λ s, delta_mollifier n t s * ∥γ y s∥,
    let f₂ : ℝ → ℝ := λ s, delta_mollifier n t s * ⨆ (u : I), ∥γ y u∥,
    have hle : f₁ ≤ f₂ := λ s, mul_le_mul_of_nonneg_left ((γ y).norm_at_le_supr_norm_Icc
      (loop.continuous_of_family h y) s) (delta_mollifier_pos s).le,
    have hf₁ : interval_integrable f₁ volume 0 1,
    { apply continuous.interval_integrable,
      refine continuous.mul delta_mollifier_smooth.continuous (continuous_norm.comp _),
      exact loop.continuous_of_family h y, },
    have hf₂ : interval_integrable f₂ volume 0 1,
    { apply continuous.interval_integrable,
      exact delta_mollifier_smooth.continuous.mul continuous_const, },
    refine (interval_integral.integral_mono (@zero_le_one ℝ _) hf₁ hf₂ hle).trans _,
    rw [integral_mul_const, delta_mollifier_integral_eq_one, one_mul], },
  suffices : tendsto (λ y, ⨆ (s : I), ∥γ y s∥) (𝓝 x) (𝓝 0), { exact this.comp tendsto_fst, },
  let γ' := loop.as_continuous_family h,
  have hx' : γ' x = 0, { ext s, simp [hx], },
  have hγx : tendsto γ' (𝓝 x) (𝓝 (γ' _)) := γ'.continuous.continuous_at,
  rw metric.tendsto_nhds_nhds at hγx ⊢,
  simp only [hx', dist_zero_right, continuous_map.norm_eq_supr_norm, γ',
    continuous_map.curry_apply, continuous_map.coe_mk, gt_iff_lt, exists_prop] at hγx,
  intros ε hε,
  obtain ⟨δ, hδ, hδ'⟩ := hγx ε hε,
  refine ⟨δ, hδ, λ y hy, _⟩,
  specialize hδ' hy,
  simp only [dist_zero_right],
  rw real.norm_of_nonneg,
  { exact hδ', },
  { refine real.Sup_nonneg _ (λ n hn, _),
    obtain ⟨s, rfl⟩ := hn,
    simp, },
end

lemma loop.tendsto_mollify_apply (γ : E → loop F) (h : continuous ↿γ) (x : E) (t : ℝ) :
  tendsto (λ (z : E × ℕ), (γ z.1).mollify z.2 t) ((𝓝 x).prod at_top) (𝓝 (γ x t)) :=
begin
  suffices : tendsto (λ (z : E × ℕ), (γ x).mollify z.2 t - (γ z.1).mollify z.2 t)
    ((𝓝 x).prod at_top) (𝓝 0),
  { have hx : tendsto (λ (z : E × ℕ), (γ x).mollify z.2 t) ((𝓝 x).prod at_top) (𝓝 (γ x t)) :=
      ((γ x).tendsto_mollify (loop.continuous_of_family h x) t).comp tendsto_snd,
    simpa using hx.sub this, },
  simp_rw loop.mollify_sub (γ x) _ (loop.continuous_of_family h x) (loop.continuous_of_family h _),
  refine loop.tendsto_mollify_apply_aux (λ y, γ x - γ y) _ x t (sub_self _),
  suffices : continuous (λ (yt : E × ℝ), γ x yt.2 - γ yt.1 yt.2),
  { refine this.congr (λ z, _),
    simp [has_uncurry.uncurry], },
  exact ((loop.continuous_of_family h x).comp continuous_snd).sub h,
end

structure smooth_surrounding_family (g : E → F) :=
(smooth_surrounded : 𝒞 ∞ g)
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

def surrounding_parameters_at : ι → ℝ := classical.some (γ.surrounds x)

def surrounding_points_at : ι → F := γ x ∘ γ.surrounding_parameters_at x

def surrounding_weights_at : ι → ℝ := classical.some (classical.some_spec (γ.surrounds x))

lemma surround_pts_points_weights_at :
  surrounding_pts (g x) (γ.surrounding_points_at x) (γ.surrounding_weights_at x) :=
classical.some_spec _

/-- Note that we are mollifying the loop `γ y` at the surrounding parameters for `γ x`. -/
def approx_surrounding_points_at (n : ℕ) (i : ι) : F :=
(γ y).mollify n (γ.surrounding_parameters_at x i)

lemma approx_surrounding_points_at_smooth (n : ℕ) :
  𝒞 ∞ (λ y, γ.approx_surrounding_points_at x y n) :=
begin
  refine cont_diff_pi.mpr (λ i, _),
  suffices : 𝒞 ∞ (λy, ∫ s in 0..1, delta_mollifier n (γ.surrounding_parameters_at x i) s • γ y s),
  { simpa [approx_surrounding_points_at, loop.mollify], },
  refine cont_diff_parametric_integral_of_cont_diff (cont_diff.smul _ γ.smooth) 0 1,
  exact delta_mollifier_smooth.snd',
end

/-- The key property from which it should be easy to construct `local_centering_density`,
`local_centering_density_nhd` etc below. -/
lemma eventually_exists_surrounding_pts_approx_surrounding_points_at :
  ∀ᶠ (z : E × ℕ) in (𝓝 x).prod at_top,
  ∃ w, surrounding_pts (g z.1) (γ.approx_surrounding_points_at x z.1 z.2) w :=
begin
  let a : ι → E × ℕ → F := λ i z, γ.approx_surrounding_points_at x z.1 z.2 i,
  suffices : ∀ i, tendsto (a i) ((𝓝 x).prod at_top) (𝓝 (γ.surrounding_points_at x i)),
  { have hg : tendsto (λ (z : E × ℕ), g z.fst) ((𝓝 x).prod at_top) (𝓝 (g x)) :=
      tendsto.comp γ.smooth_surrounded.continuous.continuous_at tendsto_fst,
    exact eventually_surrounding_pts_of_tendsto_of_tendsto'
      ⟨_, γ.surround_pts_points_weights_at x⟩ this hg, },
  intros i,
  let t := γ.surrounding_parameters_at x i,
  change tendsto (λ (z : E × ℕ), (γ z.1).mollify z.2 t) ((𝓝 x).prod at_top) (𝓝 (γ x t)),
  exact loop.tendsto_mollify_apply γ γ.smooth.continuous x t,
end

/- This is an auxiliary definition to help construct `centering_density` below.

Given `x : E`, it represents a smooth probability distribution on the circle with the property that:
`∫ s in 0..1, γ.local_centering_density x y s • γ y s = g y`
for all `y` in a neighbourhood of `x` (see `local_centering_density_average` below). -/
def local_centering_density [decidable_pred (∈ affine_bases ι ℝ F)] : E → ℝ → ℝ := λ y,
begin
  choose n hn₁ hn₂ using filter.eventually_iff_exists_mem.mp
    (γ.eventually_exists_surrounding_pts_approx_surrounding_points_at x),
  choose u hu v hv huv using mem_prod_iff.mp hn₁,
  choose m hmv using mem_at_top_sets.mp hv,
  exact ∑ i, (eval_barycentric_coords ι ℝ F (g y) (γ.approx_surrounding_points_at x y m) i) •
    (delta_mollifier m (γ.surrounding_parameters_at x i)),
end

def local_centering_density_mp : ℕ :=
begin
  choose n hn₁ hn₂ using filter.eventually_iff_exists_mem.mp
    (γ.eventually_exists_surrounding_pts_approx_surrounding_points_at x),
  choose u hu v hv huv using mem_prod_iff.mp hn₁,
  choose m hmv using mem_at_top_sets.mp hv,
  exact m,
end

lemma local_centering_density_spec [decidable_pred (∈ affine_bases ι ℝ F)] :
  γ.local_centering_density x y =
  ∑ i, (eval_barycentric_coords ι ℝ F (g y)
    (γ.approx_surrounding_points_at x y (γ.local_centering_density_mp x)) i) •
    (delta_mollifier (γ.local_centering_density_mp x) (γ.surrounding_parameters_at x i)) :=
rfl

def local_centering_density_nhd : set E :=
begin
  choose n hn₁ hn₂ using filter.eventually_iff_exists_mem.mp
    (γ.eventually_exists_surrounding_pts_approx_surrounding_points_at x),
  choose u hu v hv huv using mem_prod_iff.mp hn₁,
  exact (interior u),
end

omit x

lemma local_centering_density_nhd_is_open :
  is_open $ γ.local_centering_density_nhd x :=
is_open_interior

lemma local_centering_density_nhd_self_mem :
  x ∈ γ.local_centering_density_nhd x :=
begin
  let h := filter.eventually_iff_exists_mem.mp
    (γ.eventually_exists_surrounding_pts_approx_surrounding_points_at x),
  exact mem_interior_iff_mem_nhds.mpr (classical.some (classical.some_spec (mem_prod_iff.mp
    (classical.some (classical.some_spec h))))),
end

lemma local_centering_density_nhd_covers :
  univ ⊆ ⋃ x, γ.local_centering_density_nhd x :=
λ x hx, mem_Union.mpr ⟨x, γ.local_centering_density_nhd_self_mem x⟩

lemma approx_surrounding_points_at_of_local_centering_density_nhd
  (hy : y ∈ γ.local_centering_density_nhd x) : ∃ w,
  surrounding_pts (g y) (γ.approx_surrounding_points_at x y (γ.local_centering_density_mp x)) w :=
begin
  let h := filter.eventually_iff_exists_mem.mp
    (γ.eventually_exists_surrounding_pts_approx_surrounding_points_at x),
  let nn := classical.some h,
  let hnn := mem_prod_iff.mp (classical.some (classical.some_spec h)),
  let n := classical.some hnn,
  let hn := classical.some_spec hnn,
  change y ∈ interior n at hy,
  let v := classical.some (classical.some_spec hn),
  let hv : v ∈ at_top := classical.some (classical.some_spec (classical.some_spec hn)),
  let m := classical.some (mem_at_top_sets.mp hv),
  let hm := classical.some_spec (mem_at_top_sets.mp hv),
  change ∃ w, surrounding_pts (g y) (γ.approx_surrounding_points_at x y m) w,
  suffices : (y, m) ∈ nn,
  { exact classical.some_spec (classical.some_spec h) _ this, },
  apply classical.some_spec (classical.some_spec (classical.some_spec hn)),
  change y ∈ n ∧ m ∈ v,
  exact ⟨interior_subset hy, hm _ (le_refl _)⟩,
end

lemma approx_surrounding_points_at_mem_affine_bases (hy : y ∈ γ.local_centering_density_nhd x) :
  γ.approx_surrounding_points_at x y (γ.local_centering_density_mp x) ∈ affine_bases ι ℝ F :=
(classical.some_spec
  (γ.approx_surrounding_points_at_of_local_centering_density_nhd x y hy)).mem_affine_bases

variables [decidable_pred (∈ affine_bases ι ℝ F)]

@[simp] lemma local_centering_density_pos (t : ℝ) (hy : y ∈ γ.local_centering_density_nhd x) :
  0 < γ.local_centering_density x y t :=
begin
  simp only [γ.local_centering_density_spec x, fintype.sum_apply, pi.smul_apply,
    algebra.id.smul_eq_mul],
  refine finset.sum_pos (λ i hi, _) finset.univ_nonempty,
  refine mul_pos _ (delta_mollifier_pos _),
  obtain ⟨w, hw⟩ := γ.approx_surrounding_points_at_of_local_centering_density_nhd x y hy,
  convert hw.w_pos i,
  rw ← hw.coord_eq_w,
  simp [eval_barycentric_coords, γ.approx_surrounding_points_at_mem_affine_bases x y hy],
end

lemma local_centering_density_periodic (hy : y ∈ γ.local_centering_density_nhd x) :
  periodic (γ.local_centering_density x y) 1 :=
finset.univ.periodic_sum $ λ i hi, periodic.smul delta_mollifier_periodic _

lemma local_centering_density_smooth_on :
  smooth_on ↿(γ.local_centering_density x) $
    (γ.local_centering_density_nhd x) ×ˢ (univ : set ℝ) :=
begin
  let h₀ := (λ (yt : E × ℝ) (hyt : yt ∈ (γ.local_centering_density_nhd x) ×ˢ (univ : set ℝ)),
    congr_fun (γ.local_centering_density_spec x yt.fst) yt.snd),
  refine cont_diff_on.congr _ h₀,
  simp only [fintype.sum_apply, pi.smul_apply, algebra.id.smul_eq_mul],
  refine cont_diff_on.sum (λ i hi, cont_diff_on.mul _ (cont_diff.cont_diff_on _)),
  { let w : F × (ι → F) → ℝ := λ z, eval_barycentric_coords ι ℝ F z.1 z.2 i,
    let z : E → F × (ι → F) :=
      (prod.map g (λ y, γ.approx_surrounding_points_at x y (γ.local_centering_density_mp x))) ∘
      (λ x, (x, x)),
    change smooth_on ((w ∘ z) ∘ prod.fst) (γ.local_centering_density_nhd x ×ˢ univ),
    rw prod_univ,
    refine cont_diff_on.comp _ cont_diff_fst.cont_diff_on subset.rfl,
    have h₁ := smooth_barycentric ι ℝ F (fintype.card_fin _),
    have h₂ : 𝒞 ∞ (eval i : (ι → ℝ) → ℝ) := cont_diff_apply _ _ i,
    refine (h₂.comp_cont_diff_on h₁).comp _ _,
    { have h₃ := (diag_preimage_prod_self (γ.local_centering_density_nhd x)).symm.subset,
      refine cont_diff_on.comp _ (cont_diff_id.prod cont_diff_id).cont_diff_on h₃,
      refine (γ.smooth_surrounded).cont_diff_on.prod_map (cont_diff.cont_diff_on _),
      exact γ.approx_surrounding_points_at_smooth x _, },
    { intros y hy,
      simp [z, γ.approx_surrounding_points_at_mem_affine_bases x y hy], }, },
  { exact delta_mollifier_smooth.comp cont_diff_snd, },
end

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
begin
  let n := γ.local_centering_density_mp x,
  simp only [γ.local_centering_density_spec x, prod.forall, exists_prop, gt_iff_lt,
    fintype.sum_apply, pi.smul_apply, algebra.id.smul_eq_mul, finset.sum_smul],
  rw interval_integral.integral_sum,
  { have h : γ.approx_surrounding_points_at x y n ∈ affine_bases ι ℝ F :=
      γ.approx_surrounding_points_at_mem_affine_bases x y hy,
    simp_rw [← smul_eq_mul, interval_integral.integral_smul, delta_mollifier_integral_eq_one,
      algebra.id.smul_eq_mul, mul_one, eval_barycentric_coords_apply_of_mem_bases ι ℝ F (g y) h,
      affine_basis.coords_apply, affine_basis.sum_coord_apply_eq_one], },
  { simp_rw ← smul_eq_mul,
    refine λ i hi, (continuous.const_smul _ _).interval_integrable 0 1,
    exact delta_mollifier_smooth.continuous, },
end

@[simp] lemma local_centering_density_average (hy : y ∈ γ.local_centering_density_nhd x) :
  ∫ s in 0..1, γ.local_centering_density x y s • γ y s = g y :=
begin
  let n := γ.local_centering_density_mp x,
  simp only [γ.local_centering_density_spec x, prod.forall, exists_prop, gt_iff_lt,
    fintype.sum_apply, pi.smul_apply, algebra.id.smul_eq_mul, finset.sum_smul],
  rw interval_integral.integral_sum,
  { simp_rw [mul_smul, interval_integral.integral_smul],
    change ∑ i, _ • (γ.approx_surrounding_points_at x y n i) = _,
    have h : γ.approx_surrounding_points_at x y n ∈ affine_bases ι ℝ F :=
      γ.approx_surrounding_points_at_mem_affine_bases x y hy,
    erw [eval_barycentric_coords_apply_of_mem_bases ι ℝ F (g y) h],
    simpa using affine_basis.affine_combination_coord_eq_self (affine_basis.mk _ h.1 h.2) (g y), },
  { simp_rw mul_smul,
    refine λ i hi, ((continuous.smul _ (γ.continuous y)).const_smul _).interval_integrable 0 1,
    exact delta_mollifier_smooth.continuous, },
end

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

lemma centering_density_def :
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
    ∀ (x : E), ∃ (ys : finset E) {n : set E} (hn₁ : n ∈ 𝓝 x)
      (hn₂ : n ⊆ ⋂ y ∈ ys, γ.local_centering_density_nhd y),
      ∀ (z ∈ n) t, ∑ y in ys, p y z = 1 ∧
      γ.centering_density z t = ∑ y in ys, p y z * γ.local_centering_density y z t :=
begin
  obtain ⟨p, hp, hp'⟩ := γ.centering_density_def,
  refine ⟨p, hp, λ x, _⟩,
  obtain ⟨ys, n, hn₁, hn₂, hn₃⟩ := partition_of_unity.exists_finset_nhd_support_subset
    (smooth_partition_of_unity.is_subordinate_to_partition_of_unity.mpr hp)
    (γ.local_centering_density_nhd_is_open) x,
  refine ⟨ys, n, hn₁, hn₂, λ z hz t, ⟨_, _⟩⟩,
  { erw [← finsum_eq_sum_of_support_to_finset_subset' _ (hn₃ z hz), p.sum_eq_one (mem_univ z)], },
  { rw hp',
    suffices : support (λ y, p y z * γ.local_centering_density y z t) ⊆ ys,
    { exact finsum_eq_sum_of_support_to_finset_subset' _ this, },
    refine subset.trans (λ y hy, _) (hn₃ z hz),
    rintros (contra : p y z = 0),
    simpa [contra] using hy, },
end

@[simp] lemma centering_density_pos (t : ℝ) :
  0 < γ.centering_density x t :=
begin
  obtain ⟨p, hp, hp'⟩ := γ.centering_density_eq_exists_pou_nhd_finset_sum,
  obtain ⟨ys, n, hn₁, hn₂, hn₃⟩ := hp' x,
  obtain ⟨hx₁, hx₂⟩ := hn₃ x (mem_of_mem_nhds hn₁) t,
  rw hx₂,
  have hx₀ : ∀ y ∈ ys, 0 ≤ p y x  := λ y hy, p.nonneg y x,
  refine (convex_Ioi (0 : ℝ)).sum_mem hx₀ hx₁ (λ y hy, _),
  simp only [subset_Inter₂_iff] at hn₂,
  exact γ.local_centering_density_pos y x t (hn₂ y hy (mem_of_mem_nhds hn₁)),
end

lemma centering_density_periodic :
  periodic (γ.centering_density x) 1 :=
begin
  obtain ⟨p, hp, hp'⟩ := γ.centering_density_def,
  have : ∀ y t,
    p y x * γ.local_centering_density y x (t + 1) = p y x * γ.local_centering_density y x t,
  { intros,
    by_cases h : x ∈ γ.local_centering_density_nhd y,
    { rw γ.local_centering_density_periodic y x h, },
    { suffices : x ∉ support (p y), { simp [nmem_support.mp this], },
      exact set.not_mem_subset (subset_tsupport _) (set.not_mem_subset (hp y) h), }, },
  intros t,
  simp_rw [hp', this],
end

lemma centering_density_smooth :
  -- 𝒞 ∞ ↿γ.centering_density :=
  𝒞 ∞ $ uncurry (λ x t, γ.centering_density x t) :=
begin
  rw cont_diff_iff_cont_diff_at,
  rintros ⟨x, t⟩,
  obtain ⟨p, hp, hp'⟩ := γ.centering_density_eq_exists_pou_nhd_finset_sum,
  obtain ⟨ys, n, hn₁, hn₂, hn₃⟩ := hp' x,
  have hn₄ : n ×ˢ (univ : set ℝ) ∈ 𝓝 (x, t) :=
    mem_nhds_prod_iff.mpr ⟨n, hn₁, univ, filter.univ_mem, rfl.subset⟩,
  refine cont_diff_within_at.cont_diff_at
    (cont_diff_on.cont_diff_within_at _ (mem_of_mem_nhds hn₄)) hn₄,
  let f : E × ℝ → ℝ := λ zt, ∑ y in ys, p y zt.1 * γ.local_centering_density y zt.1 zt.2,
  have hf : ∀ zs ∈ n ×ˢ (univ : set ℝ), (uncurry γ.centering_density) zs = f zs,
  { rintros ⟨z, s⟩ hz,
    simp only [prod_mk_mem_set_prod_eq, mem_univ, and_true] at hz,
    simp [hn₃ z hz s], },
  apply cont_diff_on.congr _ hf,
  refine cont_diff_on.sum (λ y hy, cont_diff_on.mul (cont_diff.cont_diff_on _) _),
  { refine cont_diff.comp _ cont_diff_fst,
    rw ← cont_mdiff_iff_cont_diff,
    exact (p y).cont_mdiff },
  { suffices : n ×ˢ (univ : set ℝ) ⊆ (γ.local_centering_density_nhd y) ×ˢ (univ : set ℝ),
    { exact (γ.local_centering_density_smooth_on y).mono this, },
    simp only [subset_Inter₂_iff] at hn₂,
    exact prod_mono (hn₂ y hy) rfl.subset, },
end

@[simp] lemma centering_density_integral_eq_one :
  ∫ s in 0..1, γ.centering_density x s = 1 :=
begin
  obtain ⟨p, hp, hp'⟩ := γ.centering_density_def,
  have h_int : ∀ y, interval_integrable
    (λ t, p y x • γ.local_centering_density y x t) volume 0 1,
  { intros y,
    by_cases hy : x ∈ γ.local_centering_density_nhd y,
    { refine continuous.interval_integrable (continuous.const_smul _ (p y x)) _ _,
      exact γ.local_centering_density_continuous _ _ hy, },
    { suffices : x ∉ support (p y), { simp [nmem_support.mp this], },
      exact λ contra, hy (hp _ (subset_tsupport _ contra)), }, },
  have h_supp : (support (λ y t, p y x • γ.local_centering_density y x t)).finite,
  { refine set.finite.subset (p.locally_finite.point_finite x) (λ y hy, _),
    simp only [ne.def, mem_set_of_eq, mem_support],
    intros contra,
    simpa only [mem_support, contra, zero_smul, ne.def, pi.zero_def] using hy, },
  simp_rw [hp', ← smul_eq_mul, integral_finsum h_int h_supp, interval_integral.integral_smul],
  suffices : ∀ y z, z ∈ univ ∩ γ.local_centering_density_nhd y →
    ∫ t in 0..1, γ.local_centering_density y z t = 1,
  { let f := λ y z, ∫ t in 0..1, γ.local_centering_density y z t,
    exact p.finsum_smul_eq hp f 1 this (mem_univ x), },
  intros y z hyz,
  simp only [univ_inter] at hyz,
  exact γ.local_centering_density_integral_eq_one y z hyz,
end

@[simp] lemma centering_density_average :
  ∫ s in 0..1, γ.centering_density x s • γ x s = g x :=
begin
  obtain ⟨p, hp, hp'⟩ := γ.centering_density_def,
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

lemma deriv_integral_centering_density_pos (t : ℝ) :
  0 < deriv (λ t, ∫ s in 0..t, γ.centering_density x s) t :=
begin
  rw interval_integral.deriv_integral_right (γ.centering_density_interval_integrable _ _ _)
    ((γ.centering_density_continuous x).strongly_measurable_at_filter volume (𝓝 t))
    (centering_density_continuous γ x).continuous_at,
  exact centering_density_pos γ x t
end

lemma strict_mono_integral_centering_density :
  strict_mono $ λ t, ∫ s in 0..t, γ.centering_density x s :=
strict_mono_of_deriv_pos (γ.deriv_integral_centering_density_pos x)

lemma surjective_integral_centering_density :
  surjective $ λ t, ∫ s in 0..t, γ.centering_density x s :=
begin
  have : continuous (λ t, ∫ s in 0..t, γ.centering_density x s),
  { exact continuous_primitive (γ.centering_density_interval_integrable x) 0, },
  exact equivariant_map.surjective
    ⟨λ t, ∫ s in 0..t, γ.centering_density x s, γ.integral_add_one_centering_density x⟩ this
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
  ((γ.centering_density_continuous x).strongly_measurable_at_filter _ _)
  (γ.centering_density_continuous x).continuous_at

lemma reparametrize_smooth :
  -- 𝒞 ∞ ↿γ.reparametrize :=
  𝒞 ∞ $ uncurry (λ x t, γ.reparametrize x t) :=
begin
  let f : E → ℝ → ℝ := λ x t, ∫ s in 0..t, γ.centering_density x s,
  change 𝒞 ⊤ (λ p : E × ℝ, (strict_mono.order_iso_of_surjective (f p.1) _ _).symm p.2),
  apply cont_diff_parametric_symm_of_deriv_pos,
  { exact cont_diff_parametric_primitive_of_cont_diff'' γ.centering_density_smooth 0 },
  { exact λ x, deriv_integral_centering_density_pos γ x }
end

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
