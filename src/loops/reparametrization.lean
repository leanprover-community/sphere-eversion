import notations
import loops.surrounding
import analysis.calculus.specific_functions
import measure_theory.integral.periodic
import to_mathlib.order.hom.basic

/-!
# The reparametrization lemma
-/

noncomputable theory

open set function measure_theory interval_integral
open_locale topological_space unit_interval

variables {E F : Type*}
variables [normed_group E] [normed_space ℝ E]
variables [normed_group F] [normed_space ℝ F]
variables [measurable_space F] [borel_space F] [finite_dimensional ℝ F]

structure smooth_surrounding_family (g : E → F) :=
(to_fun : E → loop F)
(smooth : 𝒞 ∞ ↿to_fun)
(surrounds : ∀ x, (to_fun x).surrounds $ g x)

namespace smooth_surrounding_family

variables {g : E → F} (γ : smooth_surrounding_family g) (x : E)

instance : has_coe_to_fun (smooth_surrounding_family g) (λ _, E → loop F) := ⟨to_fun⟩

protected lemma continuous : continuous (γ x) :=
begin
  apply continuous_uncurry_left x,
  exact γ.smooth.continuous,
end

include γ
/-- This the key construction. It represents a smooth probability distribution on the circle with
the property that:
`∫ s in 0..1, (γ.centering_density x s) • (γ x s) = g x`
(see `centering_density_average` below).

The above property, which is global in `x`, is obtained from the corresponding local property via
a standard partition of unity argument. The local property is obtained by combining smoothness
of barycentric coordinates with the fact that `g x` lies in the _interior_ of a convex hull.

The _pointwise_ statement is at least intuitive: for a given `x : E`, since `γ.to_fun x` surrounds
`g x`, there are real numbers `t₁,` ..., `tₙ` such that `g x` is in the interior of the convex hull
of `γ.to_fun x tᵢ`, which are an affine basis. One defines `centering_density` so that
`centering_density x t` has almost all of its mass concentrated at the values `t = tᵢ` with each
value getting a share of the total mass proportional to the barycentric coordinate of `g x`. -/
def centering_density : E → ℝ → ℝ :=
sorry
omit γ

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
  ∫ s in 0..1, (γ.centering_density x s) • (γ x s) = g x :=
sorry

lemma centering_density_continuous :
  continuous (γ.centering_density x) :=
begin
  apply continuous_uncurry_left x,
  exact γ.centering_density_smooth.continuous,
end

lemma centering_density_interval_integrable (t₁ t₂ : ℝ) :
  interval_integrable (γ.centering_density x) measure_space.volume t₁ t₂ :=
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
