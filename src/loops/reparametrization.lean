import notations
import loops.surrounding
import analysis.calculus.specific_functions
import to_mathlib.order.hom.basic

/-!
# The reparametrization lemma
-/

noncomputable theory

open set function
open_locale topological_space unit_interval

set_option old_structure_cmd true

/-- Equivariant maps from `ℝ` to itself are functions `f : ℝ → ℝ` with `f (t + 1) = f t + 1`. -/
structure equivariant_equiv extends ℝ ≃ ℝ :=
(map_zero' : to_fun 0 = 0)
(eqv' : ∀ t, to_fun (t + 1) = to_fun t + 1)

namespace equivariant_equiv

variable (φ : equivariant_equiv)

instance : has_coe_to_fun equivariant_equiv (λ _, ℝ → ℝ) := ⟨equivariant_equiv.to_fun⟩

instance has_coe_to_equiv : has_coe equivariant_equiv (ℝ ≃ ℝ) := ⟨to_equiv⟩

lemma eqv : ∀ t, φ (t + 1) = φ t + 1 := φ.eqv'

@[simp] lemma map_zero : φ 0 = 0 := φ.map_zero'

@[simp] lemma map_one : φ 1 = 1 :=
by conv_lhs { rw [← zero_add (1 : ℝ), eqv, map_zero, zero_add], }

instance {α : Type*} : has_uncurry (α → equivariant_equiv) (α × ℝ) ℝ := ⟨λ φ p, φ p.1 p.2⟩

@[simp] lemma coe_mk (f : ℝ → ℝ) (g : ℝ → ℝ) (h₀ h₁ h₂ h₃) :
  ⇑(⟨f, g, h₀, h₁, h₂, h₃⟩ : equivariant_equiv) = f :=
rfl

@[simp] lemma coe_to_equiv (e : equivariant_equiv) : (⇑(e : ℝ ≃ ℝ) : ℝ → ℝ) = e := rfl

def symm (e : equivariant_equiv) : equivariant_equiv :=
{ map_zero' := by rw [← (e : ℝ ≃ ℝ).apply_eq_iff_eq, equiv.to_fun_as_coe, equiv.apply_symm_apply,
    coe_to_equiv, map_zero],
  eqv' := λ t,
  begin
    let f := (e : ℝ ≃ ℝ),
    let g := (e : ℝ ≃ ℝ).symm,
    change g (t + 1) = g t + 1,
    calc g (t + 1) = g (f (g t) + 1) : by rw (e : ℝ ≃ ℝ).apply_symm_apply
               ... = g (f (g t + 1)) : by { erw e.eqv, refl, }
               ... = g t + 1 : (e : ℝ ≃ ℝ).symm_apply_apply _,
  end,
  .. (e : ℝ ≃ ℝ).symm }

@[ext] lemma ext {e₁ e₂ : equivariant_equiv} (h : ∀ x, e₁ x = e₂ x) : e₁ = e₂ :=
sorry

@[simp] lemma symm_symm (e : equivariant_equiv) : e.symm.symm = e :=
begin
  ext x,
  change (e : ℝ ≃ ℝ).symm.symm x = e x,
  simp only [equiv.symm_symm, coe_to_equiv],
end

@[simp] lemma apply_symm_apply (e : equivariant_equiv) : ∀ x, e (e.symm x) = x :=
(e : ℝ ≃ ℝ).apply_symm_apply

@[simp] lemma symm_apply_apply (e : equivariant_equiv) : ∀ x, e.symm (e x) = x :=
(e : ℝ ≃ ℝ).symm_apply_apply

end equivariant_equiv

variables {E F : Type*}
variables [normed_group E] [normed_space ℝ E]
variables [normed_group F] [normed_space ℝ F]
variables [measurable_space F] [borel_space F] [finite_dimensional ℝ F]
variables {g b : E → F}

/-- Reparametrizing loop `γ` using an equivariant map `φ`. -/
@[simps {simp_rhs := tt}]
def loop.reparam (γ : loop F) (φ : equivariant_equiv) : loop F :=
{ to_fun := γ ∘ φ,
  per' := λ t, by rw [comp_apply, φ.eqv, γ.per] }

section smooth_surrounding_family

variables (g)

structure smooth_surrounding_family :=
(to_fun : E → loop F)
(smooth : ∀ x s, smooth_at ↿to_fun (x, s))
(surrounds : ∀ x, (to_fun x).surrounds $ g x)

variables {g}

namespace smooth_surrounding_family

instance : has_coe_to_fun (smooth_surrounding_family g) (λ _, E → loop F) := ⟨to_fun⟩

variables (γ : smooth_surrounding_family g) (x : E)
include γ

protected lemma continuous : continuous (γ x) :=
sorry

def centering_density : E → ℝ → ℝ :=
sorry

lemma centering_density_pos (t : ℝ) :
  0 < γ.centering_density x t :=
sorry

@[simp] lemma integral_centering_density_eq_one (t : ℝ) :
  ∫ s in t..(t+1), γ.centering_density x s = 1 :=
sorry

lemma centering_density_smooth (t : ℝ) :
  smooth_at ↿γ.centering_density ⟨x, t⟩ :=
sorry

lemma centering_density_continuous (t : ℝ) :
  continuous_at (γ.centering_density x) t :=
sorry

lemma centering_density_interval_integrable (t₁ t₂ : ℝ) :
  interval_integrable (γ.centering_density x) measure_theory.measure_space.volume t₁ t₂ :=
sorry

@[simp] lemma average_centering_density :
  ∫ s in 0..1, (γ.centering_density x s) • (γ x s) = g x :=
sorry

-- Prove for any measure `μ` with `[is_finite_measure_on_compacts μ] [is_open_pos_measure μ]`?
lemma strict_mono_integral_centering_density :
  strict_mono $ λ t, ∫ s in 0..t, γ.centering_density x s :=
sorry

lemma surjective_integral_centering_density :
  surjective $ λ t, ∫ s in 0..t, γ.centering_density x s :=
sorry

def reparametrize : E → equivariant_equiv := λ x,
({ to_fun := λ t, ∫ s in 0..t, γ.centering_density x s,
  inv_fun := (strict_mono.order_iso_of_surjective _
    (γ.strict_mono_integral_centering_density x)
    (γ.surjective_integral_centering_density x)).symm,
  left_inv := strict_mono.order_iso_of_surjective_symm_apply_self _ _ _,
  right_inv := λ t, strict_mono.order_iso_of_surjective_self_symm_apply _ _ _ t,
  map_zero' := interval_integral.integral_same,
  eqv' := λ t,
  begin
    have h₁ := γ.centering_density_interval_integrable x 0 t,
    have h₂ := γ.centering_density_interval_integrable x t (t + 1),
    simp [← interval_integral.integral_add_adjacent_intervals h₁ h₂],
  end, } : equivariant_equiv).symm

lemma coe_reparametrize_symm :
  ((γ.reparametrize x).symm : ℝ → ℝ) = λ t, ∫ s in 0..t, γ.centering_density x s :=
rfl

lemma coe_reparametrize_symm_apply (t : ℝ) :
  (γ.reparametrize x).symm t = ∫ s in 0..t, γ.centering_density x s :=
rfl

@[simp] lemma reparametrize_map_zero :
  γ.reparametrize x 0 = 0 :=
equivariant_equiv.map_zero _

@[simp] lemma reparametrize_map_one :
  γ.reparametrize x 1 = 1 :=
equivariant_equiv.map_one _

lemma has_deriv_at_reparametrize_symm (s : ℝ) :
  has_deriv_at (γ.reparametrize x).symm (γ.centering_density x s) s :=
begin
  simp only [coe_reparametrize_symm],
  convert interval_integral.integral_has_deriv_at_right
    (γ.centering_density_interval_integrable x 0 s) _ (γ.centering_density_continuous x s),
  sorry,
end

lemma reparametrize_smooth_at (s : ℝ) :
  smooth_at ↿γ.reparametrize (x, s) :=
sorry

lemma reparametrize_continuous :
  continuous (γ.reparametrize x : ℝ → ℝ) :=
sorry

@[simp] lemma reparametrize_average :
  ((γ x).reparam $ γ.reparametrize x).average = g x :=
begin
  change ∫ (s : ℝ) in 0..1, γ x (γ.reparametrize x s) = g x,
  have h₁ : ∀ s,
    s ∈ interval 0 (1 : ℝ) → has_deriv_at (γ.reparametrize x).symm (γ.centering_density x s) s :=
    λ s hs, γ.has_deriv_at_reparametrize_symm x s,
  have h₂ : continuous_on (λ s, γ.centering_density x s) (interval 0 1) :=
    λ s hs, (γ.centering_density_continuous x s).continuous_within_at,
  have h₃ : continuous (λ s, γ x (γ.reparametrize x s)) :=
    (γ.continuous x).comp (γ.reparametrize_continuous x),
  rw [← (γ.reparametrize x).symm.map_zero, ← (γ.reparametrize x).symm.map_one,
    ← interval_integral.integral_comp_smul_deriv h₁ h₂ h₃],
  simp,
end

end smooth_surrounding_family

end smooth_surrounding_family
