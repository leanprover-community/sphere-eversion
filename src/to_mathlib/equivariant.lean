import notations
import topology.algebra.order.floor
import to_mathlib.topology.misc

noncomputable theory

open set function finite_dimensional prod int
open_locale topology unit_interval

/-- Equivariant maps from `ℝ` to itself are functions `f : ℝ → ℝ` with `f (t + 1) = f t + 1`. -/
structure equivariant_map :=
(to_fun : ℝ → ℝ)
(eqv' : ∀ t, to_fun (t + 1) = to_fun t + 1)

namespace equivariant_map

variable (φ : equivariant_map)

instance : has_coe_to_fun equivariant_map (λ _, ℝ → ℝ) := ⟨equivariant_map.to_fun⟩

lemma eqv : ∀ t, φ (t + 1) = φ t + 1 := φ.eqv'

lemma sub_one (t : ℝ) : φ (t - 1) = φ t - 1 :=
by rw [eq_sub_iff_add_eq, ← eqv, sub_add_cancel]

lemma add_coe (t : ℝ) (n : ℤ) : φ (t + n) = φ t + n :=
begin
  refine int.induction_on' n 0 _ _ _,
  { simp_rw [cast_zero, add_zero] },
  { intros k hk h, simp_rw [cast_add, cast_one, ← add_assoc, eqv, h] },
  { intros k hk h, simp_rw [cast_sub, cast_one, ← add_sub_assoc, sub_one, h] }
end

lemma coe_int (n : ℤ) : φ n = φ 0 + n :=
by { convert add_coe φ 0 n, rw [zero_add] }

protected lemma one : φ 1 = φ 0 + 1 :=
by rw [← cast_one, φ.coe_int]

protected lemma not_bounded_above (y : ℝ) : ∃ (x : ℝ), y ≤ φ x  :=
by { use int.ceil (y - φ 0), simp_rw [φ.coe_int, ← sub_le_iff_le_add', le_ceil] }

protected lemma not_bounded_below (y : ℝ) : ∃ (x : ℝ), φ x ≤ y  :=
by { use int.floor (y - φ 0), simp_rw [φ.coe_int, ← le_sub_iff_add_le', floor_le] }

@[simp] lemma coe_mk (f : ℝ → ℝ) {eqv} : ((⟨f, eqv⟩ : equivariant_map) : ℝ → ℝ) = f := rfl

protected lemma surjective (h : continuous φ) : surjective φ :=
begin
  rw [← range_iff_surjective, eq_univ_iff_forall],
  exact λ y, mem_range_of_exists_le_of_exists_ge h (φ.not_bounded_below y) (φ.not_bounded_above y)
end

protected lemma fract_add_floor (t : ℝ) : φ (fract t) + ⌊t⌋ = φ t :=
by rw [← φ.add_coe, fract_add_floor]

protected lemma monotone (h : monotone_on φ I) : monotone φ :=
begin
  intros x y hxy,
  rw [← φ.fract_add_floor x, ← φ.fract_add_floor y],
  cases (floor_mono hxy).eq_or_lt with h2 h2,
  { rw [h2],
    refine add_le_add_right (h (unit_interval.fract_mem _) (unit_interval.fract_mem _) _) _,
    simp_rw [fract, h2],
    exact sub_le_sub_right hxy _ },
  { refine (add_le_add_right (h (unit_interval.fract_mem _) unit_interval.one_mem
      (fract_lt_one _).le) _).trans (le_trans _ $ add_le_add_right (h unit_interval.zero_mem
        (unit_interval.fract_mem _) (fract_nonneg _)) _),
    rw [φ.one, add_assoc, add_comm (1 : ℝ)],
    refine add_le_add_left _ _,
    norm_cast,
    exact add_one_le_of_lt h2 },
end

protected lemma fract_fract (t : ℝ) : fract (φ (fract t)) = fract (φ t) :=
by rw [← φ.fract_add_floor t, fract_add_int]


end equivariant_map

@[simp] lemma fract_add_one {α} [linear_ordered_ring α] [floor_ring α] (a : α) :
  fract (a + 1) = fract a :=
by exact_mod_cast fract_add_int a 1

/-- continuous equivariant reparametrization that is locally constant around `0`.
  It is piecewise linear, connecting `(0, 0)`, `(1/4, 0)` and `(3/4, 1)` and `(1, 1)`,
  and extended to an equivariant function. -/
def linear_reparam : equivariant_map :=
⟨λ t, t + 4⁻¹ - abs (fract (t - 4⁻¹) - 2⁻¹), λ t,
  by { rw [← sub_add_eq_add_sub t, fract_add_one], ring }⟩

lemma linear_reparam_eq_zero {t : ℝ} (h1 : -4⁻¹ ≤ t) (h2 : t ≤ 4⁻¹) : linear_reparam t = 0 :=
begin
  rcases h2.eq_or_lt with rfl|h2,
  { rw [linear_reparam], norm_num, simp_rw [abs_of_pos (half_pos (zero_lt_one' ℝ)), sub_self] },
  have : ⌊ t - 4⁻¹ ⌋ = -1,
  { refine floor_eq_iff.mpr ⟨le_sub_iff_add_le.mpr $ le_trans (by norm_num) h1,
      sub_lt_iff_lt_add.mpr $ h2.trans_le (by norm_num)⟩ },
  have : (⌊ t - 4⁻¹ ⌋ : ℝ) = -1,
  { exact_mod_cast this },
  simp_rw [linear_reparam, equivariant_map.coe_mk, fract, this, sub_eq_zero],
  refine (abs_eq_self.mpr $ _).symm.trans (by ring_nf),
  rwa [← sub_le_iff_le_add, zero_sub]
end

lemma linear_reparam_eq_zero' {t : ℝ} (h1 : 0 ≤ t) (h2 : t ≤ 4⁻¹) : linear_reparam t = 0 :=
linear_reparam_eq_zero (le_trans (by norm_num) h1) h2

@[simp] lemma linear_reparam_zero : linear_reparam 0 = 0 :=
linear_reparam_eq_zero' le_rfl $ by norm_num1

lemma linear_reparam_eq_one {t : ℝ} (h1 : 3 / 4 ≤ t) (h2 : t ≤ 5 / 4) : linear_reparam t = 1 :=
begin
  rw [← eq_sub_iff_add_eq.mp (linear_reparam.sub_one t), ← eq_sub_iff_add_eq, sub_self],
  apply linear_reparam_eq_zero,
  { rw [le_sub_iff_add_le], exact le_trans (by norm_num1) h1 },
  { rw [sub_le_iff_le_add], exact h2.trans (by norm_num1) },
end

lemma linear_reparam_eq_one' {t : ℝ} (h1 : 3 / 4 ≤ t) (h2 : t ≤ 1) : linear_reparam t = 1 :=
linear_reparam_eq_one h1 (h2.trans $ by norm_num)

@[simp] lemma linear_reparam_one : linear_reparam 1 = 1 :=
linear_reparam_eq_one' (by norm_num1) le_rfl

lemma linear_reparam_monotone : monotone linear_reparam :=
begin
  have : ∀ x ∈ Icc (4 : ℝ)⁻¹ (3 / 4), linear_reparam x = 2 * x - 2⁻¹,
  { intros x hx,
    have : ⌊ x - 4⁻¹ ⌋ = 0,
    { refine floor_eq_iff.mpr ⟨le_sub_iff_add_le.mpr $ le_trans (by norm_num) hx.1,
        sub_lt_iff_lt_add.mpr $ hx.2.trans_lt (by norm_num)⟩ },
    have : (⌊ x - 4⁻¹ ⌋ : ℝ) = 0,
    { exact_mod_cast this },
    simp_rw [linear_reparam, equivariant_map.coe_mk, fract, this, sub_zero, sub_sub,
      show (4 : ℝ)⁻¹ + 2⁻¹ = 3 / 4, by norm_num, abs_eq_neg_self.mpr (sub_nonpos.mpr hx.2)],
    norm_num, linarith },
  have : monotone_on linear_reparam (Icc 4⁻¹ (3 / 4)),
  { intros x hx y hy hxy,
    rw [this x hx, this y hy],
    exact sub_le_sub_right (mul_le_mul_of_nonneg_left hxy zero_le_two) _ },
  have : monotone_on linear_reparam (Icc 4⁻¹ 1),
  { intros x hx y hy hxy,
    cases le_total y (3 / 4) with h1y h1y,
    { exact this ⟨hx.1, hxy.trans h1y⟩ ⟨hy.1, h1y⟩ hxy },
    rw [linear_reparam_eq_one' h1y hy.2],
    cases le_total x (3 / 4) with h1x h1x,
    { rw [← linear_reparam_eq_one le_rfl (by norm_num)],
      exact this ⟨hx.1, h1x⟩ ⟨by norm_num, le_rfl⟩ h1x },
    rw [linear_reparam_eq_one' h1x hx.2] },
  have : monotone_on linear_reparam I,
  { intros x hx y hy hxy,
    cases le_total x 4⁻¹ with h1x h1x,
    { rw [linear_reparam_eq_zero' hx.1 h1x],
      cases le_total y 4⁻¹ with h1y h1y,
      { rw [linear_reparam_eq_zero' hy.1 h1y] },
      rw [← linear_reparam_eq_zero (by norm_num) le_rfl],
      exact this ⟨le_rfl, by norm_num⟩ ⟨h1y, hy.2⟩ h1y },
    exact this ⟨h1x, hx.2⟩ ⟨h1x.trans hxy, hy.2⟩ hxy },
  exact linear_reparam.monotone this
end

lemma linear_reparam_nonpos {t : ℝ} (ht : t ≤ 4⁻¹) : linear_reparam t ≤ 0 :=
(linear_reparam_monotone ht).trans_eq (linear_reparam_eq_zero (by norm_num1) le_rfl)

lemma linear_reparam_nonneg {t : ℝ} (ht : -4⁻¹ ≤ t) : 0 ≤ linear_reparam t :=
(linear_reparam_eq_zero le_rfl (by norm_num1)).symm.trans_le (linear_reparam_monotone ht)

lemma linear_reparam_le_one {t : ℝ} (ht : t ≤ 5 / 4) : linear_reparam t ≤ 1 :=
(linear_reparam_monotone ht).trans_eq (linear_reparam_eq_one (by norm_num1) le_rfl)

lemma one_le_linear_reparam {t : ℝ} (ht : 3 / 4 ≤ t) : 1 ≤ linear_reparam t :=
(linear_reparam_eq_one le_rfl (by norm_num1)).symm.trans_le (linear_reparam_monotone ht)

@[simp] lemma linear_reparam_proj_I {t : ℝ} :
  linear_reparam (proj_I t) = proj_I (linear_reparam t) :=
begin
  rw [eq_comm],
  rcases le_total 0 t with h1t|h1t,
  rcases le_total t 1 with h2t|h2t,
  { rw [proj_I_eq_self.mpr ⟨h1t, h2t⟩, proj_I_eq_self],
    refine ⟨linear_reparam_nonneg (le_trans (by norm_num1) h1t),
      linear_reparam_le_one (h2t.trans (by norm_num1))⟩ },
  { rw [proj_I_eq_one.mpr h2t, linear_reparam_one, proj_I_eq_one],
    exact one_le_linear_reparam (le_trans (by norm_num1) h2t) },
  { rw [proj_I_eq_zero.mpr h1t, linear_reparam_zero, proj_I_eq_zero],
    exact linear_reparam_nonpos (h1t.trans (by norm_num1)) },
end

@[simp] lemma fract_linear_reparam_eq_zero {t : ℝ} (h : fract t ≤ 4⁻¹ ∨ 3 / 4 ≤ fract t) :
  fract (linear_reparam t) = 0 :=
begin
  rw [← linear_reparam.fract_fract], rcases h with h|h,
  { rw [linear_reparam_eq_zero' (fract_nonneg _) h, fract_zero] },
  { rw [linear_reparam_eq_one' h (fract_lt_one _).le, fract_one] },
end

lemma continuous_linear_reparam : continuous linear_reparam :=
begin
  have h1 : continuous (uncurry (λ t x : ℝ, t + 4⁻¹ - abs (x - 2⁻¹))) :=
    (continuous_fst.add continuous_const).sub (continuous_snd.sub continuous_const).abs,
  refine h1.continuous_on.comp_fract (continuous_id.sub continuous_const) (λ s, by norm_num)
end

set_option old_structure_cmd true

/-- A bijection from `ℝ` to itself that fixes `0` and is equivariant with respect to the `ℤ`
action by translations.

Morally, these are bijections of the circle `ℝ / ℤ` to itself. -/
structure equivariant_equiv extends ℝ ≃ ℝ :=
(map_zero' : to_fun 0 = 0)
(eqv' : ∀ t, to_fun (t + 1) = to_fun t + 1)

attribute [nolint doc_blame] equivariant_equiv.to_equiv

namespace equivariant_equiv

variable (φ : equivariant_equiv)

instance : has_coe_to_fun equivariant_equiv (λ _, ℝ → ℝ) := ⟨λ f, f.to_fun⟩

instance has_coe_to_equiv : has_coe equivariant_equiv (ℝ ≃ ℝ) := ⟨to_equiv⟩

/-- Forgetting its bijective properties, an `equivariant_equiv` can be regarded as an
`equivariant_map`. -/
@[simps]
protected def equivariant_map : equivariant_map := { to_fun := φ, ..φ }

lemma eqv : ∀ t, φ (t + 1) = φ t + 1 := φ.eqv'

@[simp] lemma map_zero : φ 0 = 0 := φ.map_zero'

@[simp] lemma map_one : φ 1 = 1 :=
by conv_lhs { rw [← zero_add (1 : ℝ), eqv, map_zero, zero_add], }

instance {α : Type*} : has_uncurry (α → equivariant_equiv) (α × ℝ) ℝ := ⟨λ φ p, φ p.1 p.2⟩

@[simp] lemma coe_mk (f : ℝ → ℝ) (g : ℝ → ℝ) (h₀ h₁ h₂ h₃) :
  ⇑(⟨f, g, h₀, h₁, h₂, h₃⟩ : equivariant_equiv) = f :=
rfl

@[simp] lemma coe_to_equiv (e : equivariant_equiv) : (⇑(e : ℝ ≃ ℝ) : ℝ → ℝ) = e := rfl

/-- The inverse of an `equivariant_equiv` is an `equivariant_equiv`. -/
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

instance : equiv_like equivariant_equiv ℝ ℝ :=
{ coe := to_fun, inv := inv_fun, left_inv := left_inv, right_inv := right_inv,
  coe_injective' := λ e₁ e₂ h₁ h₂, by { cases e₁, cases e₂, congr', } }

@[ext] lemma ext {e₁ e₂ : equivariant_equiv} (h : ∀ x, e₁ x = e₂ x) : e₁ = e₂ :=
fun_like.ext e₁ e₂ h

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
