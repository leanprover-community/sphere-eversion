import Mathlib.Topology.Algebra.Order.Floor
import SphereEversion.ToMathlib.Topology.Misc

noncomputable section

open Set Function FiniteDimensional Prod Int

open scoped Topology unitInterval

/-- Equivariant maps from `ℝ` to itself are functions `f : ℝ → ℝ` with `f (t + 1) = f t + 1`. -/
structure EquivariantMap where
  toFun : ℝ → ℝ
  eqv' : ∀ t, toFun (t + 1) = toFun t + 1

namespace EquivariantMap

variable (φ : EquivariantMap)

instance : CoeFun EquivariantMap fun _ => ℝ → ℝ :=
  ⟨EquivariantMap.toFun⟩

theorem eqv : ∀ t, φ (t + 1) = φ t + 1 :=
  φ.eqv'

theorem sub_one (t : ℝ) : φ (t - 1) = φ t - 1 := by rw [eq_sub_iff_add_eq, ← eqv, sub_add_cancel]

theorem add_coe (t : ℝ) (n : ℤ) : φ (t + n) = φ t + n := by
  refine Int.inductionOn' n 0 ?_ ?_ ?_
  · simp_rw [cast_zero, add_zero]
  · intro k _ h; simp_rw [cast_add, cast_one, ← add_assoc, eqv, h]
  · intro k _ h; simp_rw [cast_sub, cast_one, ← add_sub_assoc, sub_one, h]

theorem coe_int (n : ℤ) : φ n = φ 0 + n := by convert add_coe φ 0 n; rw [zero_add]

protected theorem one : φ 1 = φ 0 + 1 := by rw [← cast_one, φ.coe_int]

protected theorem not_bounded_above (y : ℝ) : ∃ x : ℝ, y ≤ φ x :=
  ⟨⌈y - φ 0⌉, by simp_rw [φ.coe_int, ← sub_le_iff_le_add', le_ceil]⟩

protected theorem not_bounded_below (y : ℝ) : ∃ x : ℝ, φ x ≤ y :=
  ⟨⌊y - φ 0⌋, by simp_rw [φ.coe_int, ← le_sub_iff_add_le', floor_le]⟩

@[simp]
theorem coe_mk (f : ℝ → ℝ) {eqv} : ((⟨f, eqv⟩ : EquivariantMap) : ℝ → ℝ) = f :=
  rfl

protected theorem surjective (h : Continuous φ) : Surjective φ := by
  rw [← range_eq_univ, eq_univ_iff_forall]
  exact fun y =>
    mem_range_of_exists_le_of_exists_ge h (φ.not_bounded_below y) (φ.not_bounded_above y)

protected theorem fract_add_floor (t : ℝ) : φ (fract t) + ⌊t⌋ = φ t := by
  rw [← φ.add_coe, fract_add_floor]

protected theorem monotone (h : MonotoneOn φ I) : Monotone φ := fun x y hxy ↦ by
  rw [← φ.fract_add_floor x, ← φ.fract_add_floor y]
  cases' (floor_mono hxy).eq_or_lt with h2 h2
  · rw [h2]
    refine add_le_add_right (h (unitInterval.fract_mem _) (unitInterval.fract_mem _) ?_) _
    simp_rw [fract, h2]
    exact sub_le_sub_right hxy _
  · refine (add_le_add_right (h (unitInterval.fract_mem _) unitInterval.one_mem
      (fract_lt_one _).le) _).trans
      (le_trans ?_ <|
        add_le_add_right (h unitInterval.zero_mem (unitInterval.fract_mem _) (fract_nonneg _)) _)
    rw [φ.one, add_assoc, add_comm (1 : ℝ)]
    refine add_le_add_left ?_ _
    norm_cast

protected theorem fract_fract (t : ℝ) : fract (φ (fract t)) = fract (φ t) := by
  rw [← φ.fract_add_floor t, fract_add_intCast]

end EquivariantMap

/-- continuous equivariant reparametrization that is locally constant around `0`.
  It is piecewise linear, connecting `(0, 0)`, `(1/4, 0)` and `(3/4, 1)` and `(1, 1)`,
  and extended to an equivariant function. -/
def linearReparam : EquivariantMap :=
  ⟨fun t => t + 4⁻¹ - abs (fract (t - 4⁻¹) - 2⁻¹), fun t => by
    simp only [← sub_add_eq_add_sub t, fract_add_one]; ring⟩

theorem linearReparam_eq_zero {t : ℝ} (h1 : -4⁻¹ ≤ t) (h2 : t ≤ 4⁻¹) : linearReparam t = 0 := by
  rcases h2.eq_or_lt with (rfl | h2)
  · rw [linearReparam]; norm_num; simp_rw [abs_of_pos (half_pos (zero_lt_one' ℝ)), sub_self]
  have : ⌊t - 4⁻¹⌋ = -1 :=
    floor_eq_iff.mpr ⟨le_sub_iff_add_le.mpr <| le_trans (by norm_num) h1,
      sub_lt_iff_lt_add.mpr <| h2.trans_le (by norm_num)⟩
  have : (⌊t - 4⁻¹⌋ : ℝ) = -1 := by exact_mod_cast this
  simp_rw [linearReparam, fract, this, sub_eq_zero]
  refine (abs_eq_self.mpr <| ?_).symm.trans (by ring_nf)
  rwa [← sub_le_iff_le_add, zero_sub]

theorem linearReparam_eq_zero' {t : ℝ} (h1 : 0 ≤ t) (h2 : t ≤ 4⁻¹) : linearReparam t = 0 :=
  linearReparam_eq_zero (le_trans (by norm_num) h1) h2

@[simp]
theorem linearReparam_zero : linearReparam 0 = 0 :=
  linearReparam_eq_zero' le_rfl <| by norm_num1

theorem linearReparam_eq_one {t : ℝ} (h1 : 3 / 4 ≤ t) (h2 : t ≤ 5 / 4) : linearReparam t = 1 := by
  rw [← eq_sub_iff_add_eq.mp (linearReparam.sub_one t), ← eq_sub_iff_add_eq, sub_self]
  apply linearReparam_eq_zero
  · rw [le_sub_iff_add_le]; exact le_trans (by norm_num1) h1
  · rw [sub_le_iff_le_add]; exact h2.trans (by norm_num1)

theorem linearReparam_eq_one' {t : ℝ} (h1 : 3 / 4 ≤ t) (h2 : t ≤ 1) : linearReparam t = 1 :=
  linearReparam_eq_one h1 (h2.trans <| by norm_num)

@[simp]
theorem linearReparam_one : linearReparam 1 = 1 :=
  linearReparam_eq_one' (by norm_num1) le_rfl

theorem linearReparam_monotone : Monotone linearReparam := by
  have : ∀ x ∈ Icc (4 : ℝ)⁻¹ (3 / 4), linearReparam x = 2 * x - 2⁻¹ := fun x hx ↦ by
    have : ⌊x - 4⁻¹⌋ = 0 :=
      floor_eq_iff.mpr ⟨le_sub_iff_add_le.mpr <| le_trans (by norm_num) hx.1,
        sub_lt_iff_lt_add.mpr <| hx.2.trans_lt (by norm_num)⟩
    have : (⌊x - 4⁻¹⌋ : ℝ) = 0 := by exact_mod_cast this
    simp_rw [linearReparam, fract, this, sub_zero, sub_sub,
      show (4 : ℝ)⁻¹ + 2⁻¹ = 3 / 4 by norm_num, abs_eq_neg_self.mpr (sub_nonpos.mpr hx.2)]
    norm_num; linarith
  have : MonotoneOn linearReparam (Icc 4⁻¹ (3 / 4)) := fun x hx y hy hxy ↦ by
    rw [this x hx, this y hy]
    exact sub_le_sub_right (mul_le_mul_of_nonneg_left hxy zero_le_two) _
  have : MonotoneOn linearReparam (Icc 4⁻¹ 1) := fun x hx y hy hxy ↦ by
    cases' le_total y (3 / 4) with h1y h1y
    · exact this ⟨hx.1, hxy.trans h1y⟩ ⟨hy.1, h1y⟩ hxy
    rw [linearReparam_eq_one' h1y hy.2]
    cases' le_total x (3 / 4) with h1x h1x
    · rw [← linearReparam_eq_one le_rfl (by norm_num)]
      exact this ⟨hx.1, h1x⟩ ⟨by norm_num, le_rfl⟩ h1x
    rw [linearReparam_eq_one' h1x hx.2]
  have : MonotoneOn linearReparam I := by
    intro x hx y hy hxy
    cases' le_total x 4⁻¹ with h1x h1x
    · rw [linearReparam_eq_zero' hx.1 h1x]
      cases' le_total y 4⁻¹ with h1y h1y
      · rw [linearReparam_eq_zero' hy.1 h1y]
      rw [← linearReparam_eq_zero (by norm_num) le_rfl]
      exact this ⟨le_rfl, by norm_num⟩ ⟨h1y, hy.2⟩ h1y
    exact this ⟨h1x, hx.2⟩ ⟨h1x.trans hxy, hy.2⟩ hxy
  exact linearReparam.monotone this

theorem linearReparam_nonpos {t : ℝ} (ht : t ≤ 4⁻¹) : linearReparam t ≤ 0 :=
  (linearReparam_monotone ht).trans_eq (linearReparam_eq_zero (by norm_num1) le_rfl)

theorem linearReparam_nonneg {t : ℝ} (ht : -4⁻¹ ≤ t) : 0 ≤ linearReparam t :=
  (linearReparam_eq_zero le_rfl (by norm_num1)).symm.trans_le (linearReparam_monotone ht)

theorem linearReparam_le_one {t : ℝ} (ht : t ≤ 5 / 4) : linearReparam t ≤ 1 :=
  (linearReparam_monotone ht).trans_eq (linearReparam_eq_one (by norm_num1) le_rfl)

theorem one_le_linearReparam {t : ℝ} (ht : 3 / 4 ≤ t) : 1 ≤ linearReparam t :=
  (linearReparam_eq_one le_rfl (by norm_num1)).symm.trans_le (linearReparam_monotone ht)

set_option linter.style.multiGoal false in
@[simp]
theorem linearReparam_projI {t : ℝ} : linearReparam (projI t) = projI (linearReparam t) := by
  rw [eq_comm]
  rcases le_total 0 t with (h1t | h1t)
  rcases le_total t 1 with (h2t | h2t)
  · rw [projI_eq_self.mpr ⟨h1t, h2t⟩, projI_eq_self]
    exact ⟨linearReparam_nonneg (le_trans (by norm_num1) h1t),
      linearReparam_le_one (h2t.trans (by norm_num1))⟩
  · rw [projI_eq_one.mpr h2t, linearReparam_one, projI_eq_one]
    exact one_le_linearReparam (le_trans (by norm_num1) h2t)
  · rw [projI_eq_zero.mpr h1t, linearReparam_zero, projI_eq_zero]
    exact linearReparam_nonpos (h1t.trans (by norm_num1))

@[simp]
theorem fract_linearReparam_eq_zero {t : ℝ} (h : fract t ≤ 4⁻¹ ∨ 3 / 4 ≤ fract t) :
    fract (linearReparam t) = 0 := by
  rw [← linearReparam.fract_fract]; rcases h with (h | h)
  · rw [linearReparam_eq_zero' (fract_nonneg _) h, fract_zero]
  · rw [linearReparam_eq_one' h (fract_lt_one _).le, fract_one]

theorem continuous_linearReparam : Continuous linearReparam := by
  have h1 : Continuous (uncurry fun t x ↦ t + 4⁻¹ - abs (x - 2⁻¹) : ℝ × ℝ → ℝ) := by fun_prop
  exact h1.continuousOn.comp_fract (by fun_prop) fun s ↦ by norm_num

/-- A bijection from `ℝ` to itself that fixes `0` and is equivariant with respect to the `ℤ`
action by translations.

Morally, these are bijections of the circle `ℝ / ℤ` to itself. -/
structure EquivariantEquiv extends ℝ ≃ ℝ where
  map_zero' : toFun 0 = 0
  eqv' : ∀ t, toFun (t + 1) = toFun t + 1

namespace EquivariantEquiv

variable (φ : EquivariantEquiv)

instance : CoeFun EquivariantEquiv fun _ => ℝ → ℝ :=
  ⟨fun f => f.toFun⟩

instance hasCoeToEquiv : Coe EquivariantEquiv (ℝ ≃ ℝ) :=
  ⟨toEquiv⟩

/-- Forgetting its bijective properties, an `equivariant_equiv` can be regarded as an
`equivariant_map`. -/
@[simps]
protected def equivariantMap : EquivariantMap :=
  { φ with toFun := φ }

theorem eqv : ∀ t, φ (t + 1) = φ t + 1 :=
  φ.eqv'

@[simp]
theorem map_zero : φ 0 = 0 :=
  φ.map_zero'

@[simp]
theorem map_zero'' : (⇑(φ : ℝ ≃ ℝ) : ℝ → ℝ) 0 = 0 :=
  φ.map_zero'

@[simp]
theorem map_one : φ 1 = 1 := by conv_lhs => rw [← zero_add (1 : ℝ), eqv, map_zero, zero_add]

instance {α : Type*} : HasUncurry (α → EquivariantEquiv) (α × ℝ) ℝ :=
  ⟨fun φ p => φ p.1 p.2⟩

@[simp]
theorem coe_mk (f : ℝ ≃ ℝ) (h₀ h₁) : ⇑(⟨f, h₀, h₁⟩ : EquivariantEquiv) = f := rfl

-- Warning: making this a simp lemma creates a loop with `Equiv.toFun_as_coe` or
-- `Equiv.toFun_as_coe_apply`
theorem coe_toEquiv (e : EquivariantEquiv) : (⇑(e : ℝ ≃ ℝ) : ℝ → ℝ) = e :=
  rfl

/-- The inverse of an `equivariant_equiv` is an `equivariant_equiv`. -/
def symm (e : EquivariantEquiv) : EquivariantEquiv :=
  { (e : ℝ ≃ ℝ).symm with
    map_zero' := by
      rw [← (e : ℝ ≃ ℝ).apply_eq_iff_eq, Equiv.toFun_as_coe, Equiv.apply_symm_apply, coe_toEquiv,
        map_zero]
    eqv' := fun t => by
      let f := (e : ℝ ≃ ℝ)
      let g := (e : ℝ ≃ ℝ).symm
      change g (t + 1) = g t + 1
      calc
        g (t + 1) = g (f (g t) + 1) := by rw [(e : ℝ ≃ ℝ).apply_symm_apply]
        _ = g (f (g t + 1)) := by congr; exact (e.eqv (g t)).symm
        _ = g t + 1 := (e : ℝ ≃ ℝ).symm_apply_apply _ }

instance : EquivLike EquivariantEquiv ℝ ℝ where
  coe e := e.toFun
  inv e := e.invFun
  left_inv e := e.left_inv
  right_inv e := e.right_inv
  coe_injective' e₁ e₂ h₁ h₂ := by
    rcases e₁ with ⟨f₁, hf₁⟩
    rcases e₂ with ⟨f₂, hf₂⟩
    suffices f₁ = f₂ by simpa
    ext
    change (f₁ : ℝ → ℝ)  = f₂ at h₁
    rw [h₁]

@[ext]
theorem ext {e₁ e₂ : EquivariantEquiv} (h : ∀ x, e₁ x = e₂ x) : e₁ = e₂ :=
  DFunLike.ext e₁ e₂ h

@[simp]
theorem symm_symm (e : EquivariantEquiv) : e.symm.symm = e := by
  ext x
  change (e : ℝ ≃ ℝ).symm.symm x = e x
  simp only [Equiv.symm_symm, coe_toEquiv]
  rfl

@[simp]
theorem apply_symm_apply (e : EquivariantEquiv) : ∀ x, e (e.symm x) = x :=
  (e : ℝ ≃ ℝ).apply_symm_apply

@[simp]
theorem symm_apply_apply (e : EquivariantEquiv) : ∀ x, e.symm (e x) = x :=
  (e : ℝ ≃ ℝ).symm_apply_apply

end EquivariantEquiv
