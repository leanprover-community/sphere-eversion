import analysis.normed_space.add_torsor_bases
import analysis.convex.caratheodory
import analysis.calculus.cont_diff
import measure_theory.integral.interval_integral
import measure_theory.measure.lebesgue
import topology.algebra.order.floor
import topology.path_connected
import linear_algebra.affine_space.independent

import to_mathlib.smooth_barycentric
import to_mathlib.topology.path
import to_mathlib.measure_theory.parametric_interval_integral
import to_mathlib.equivariant

/-!
# Basic definitions and properties of loops
-/

open set function finite_dimensional int topological_space
open_locale big_operators topological_space topological_space unit_interval
noncomputable theory

variables {K X X' Y Z : Type*}
-- variables [topological_space X'] [topological_space Y] [topological_space Z]
variables {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
          {F : Type*} [normed_add_comm_group F] [normed_space ℝ F]
          {F' : Type*} [normed_add_comm_group F'] [normed_space ℝ F']

set_option old_structure_cmd true

/-! ## Definition and periodicity lemmas -/

variables (X)

/-- A loop is a function with domain `ℝ` and is periodic with period 1. -/
structure loop :=
(to_fun : ℝ → X)
(per' : ∀ t, to_fun (t + 1) = to_fun t)

instance : has_coe_to_fun (loop X) (λ _, ℝ → X) := ⟨λ γ, γ.to_fun⟩

initialize_simps_projections loop (to_fun → apply)

/-- Any function `φ : α → loop X` can be seen as a function `α × ℝ → X`. -/
instance has_uncurry_loop {α : Type*} : has_uncurry (α → loop X) (α × ℝ) X := ⟨λ φ p, φ p.1 p.2⟩

variables {X}

namespace loop

@[simp]
protected lemma coe_mk {γ : ℝ → X} (h : ∀ t, γ (t + 1) = γ t) : ⇑(⟨γ, h⟩ : loop X) = γ :=
rfl

@[ext] protected lemma ext : ∀ {γ₁ γ₂ : loop X}, (γ₁ : ℝ → X) = γ₂ → γ₁ = γ₂
| ⟨x, h1⟩ ⟨.(x), h2⟩ rfl := rfl

protected lemma ext_iff {γ₁ γ₂ : loop X} : γ₁ = γ₂ ↔ (γ₁ : ℝ → X) = γ₂ :=
⟨λ h, by rw h, loop.ext⟩

/-- The constant loop. -/
@[simps]
def const (f : X) : loop X :=
⟨λ t, f, λ t, rfl⟩

instance [has_zero X] : has_zero (loop X) :=
⟨const 0⟩

@[simp] lemma zero_fun [has_zero X] : ((0 : loop X) : ℝ → X) = (0 : ℝ → X) :=
rfl

-- unused
@[simp] lemma const_zero [has_zero X] : const (0 : X) = (0 : loop X) :=
rfl

instance [inhabited X] : inhabited (loop X) :=
⟨loop.const default⟩

/-- Periodicity of loops restated in terms of the function coercion. -/
lemma per (γ : loop X) : ∀ t, γ (t + 1) = γ t :=
loop.per' γ

lemma periodic (γ : loop X) : function.periodic γ 1 :=
loop.per' γ

protected lemma one (γ : loop X) : γ 1 = γ 0 :=
by { convert γ.per 0, rw [zero_add] }

-- unused
lemma add_nat_eq (γ : loop X) (t : ℝ) : ∀ (n : ℕ), γ (t + n) = γ t
| 0 := by rw [nat.cast_zero, add_zero]
| (nat.succ n) := by rw [← add_nat_eq n, nat.cast_succ, ← add_assoc, γ.per]

lemma add_int_eq (γ : loop X) (t : ℝ) (n : ℤ) : γ (t + n) = γ t :=
begin
  induction n using int.induction_on with n hn n hn,
  { norm_cast, rw add_zero },
  { rw [← hn, int.cast_add, ← add_assoc, int.cast_one, γ.per] },
  { rw [← hn, int.cast_sub, add_sub, int.cast_one, ← γ.per, sub_add_cancel] }
end

lemma fract_eq (γ : loop X) : ∀ t, γ (fract t) = γ t :=
begin
  intro t,
  unfold fract,
  rw [sub_eq_add_neg, ← int.cast_neg],
  exact γ.add_int_eq _ _
end

lemma range_eq_image (γ : loop X) : range γ = γ '' I :=
begin
  apply eq_of_subset_of_subset,
  { rw range_subset_iff,
    exact λ y, ⟨fract y, unit_interval.fract_mem y, γ.fract_eq _⟩ },
  { rintros y ⟨x, hx, hxy⟩,
    exact ⟨x, hxy⟩ },
end

/-- Transforming a loop by applying function `f`. -/
@[simps]
def transform (γ : loop X) (f : X → X') : loop X' :=
⟨λ t, f (γ t), λ t, by rw γ.per⟩

/-- Adding two loops pointwise. -/
@[simps]
instance [has_add X] : has_add (loop X) :=
⟨λ γ₁ γ₂, ⟨λ t, γ₁ t + γ₂ t, λ t, by simp_rw [loop.per]⟩⟩

@[simps]
instance [has_neg X] : has_neg (loop X) :=
⟨λ γ, ⟨λ t, - γ t, λ t, by simp_rw [loop.per]⟩⟩

instance [add_comm_group X] : add_comm_group (loop X) :=
{ add_assoc := λ γ₁ γ₂ γ₃, by { ext t, apply add_assoc },
  add_comm := λ γ₁ γ₂, by { ext t, apply add_comm },
  add_comm := λ γ₁ γ₂, by { ext t, apply add_comm },
  zero_add := λ γ, by { ext t, apply zero_add },
  add_zero := λ γ, by { ext t, apply add_zero },
  add_left_neg := λ γ, by { ext t, apply add_left_neg },
  ..loop.has_add,
  ..loop.has_zero,
  ..loop.has_neg }

/-- Shifting a loop, or equivalently, adding a constant value to a loop. -/
instance [has_add X] : has_vadd X (loop X) :=
⟨λ x γ, γ.transform (λ y, x + y)⟩

@[simp] lemma vadd_apply [has_add X] {x : X} {γ : loop X} {t : ℝ} : (x +ᵥ γ) t = x + γ t :=
rfl

/-- Multiplying a loop by a scalar value. -/
instance [has_smul K X] : has_smul K (loop X) :=
⟨λ k γ, γ.transform (λ y, k • y)⟩

instance [semiring K] [add_comm_group X] [module K X] : module K (loop X) :=
{ one_smul := λ γ, by { ext t, apply one_smul },
  mul_smul := λ k₁ k₂ γ, by { ext t, apply mul_smul },
  smul_zero := λ k, by { ext t, apply smul_zero },
  smul_add := λ k γ₁ γ₂, by { ext t, apply smul_add },
  add_smul := λ k₁ k₂ γ, by { ext t, apply add_smul },
  zero_smul := λ γ, by { ext t, apply zero_smul } }

@[simp] lemma smul_apply [has_smul K X] {k : K} {γ : loop X} {t : ℝ} : (k • γ) t = k • γ t :=
rfl

-- unused
lemma norm_at_le_supr_norm_Icc (γ : loop F) (hγ : continuous γ) (t : ℝ) :
  ‖γ t‖ ≤ ⨆ (s : I), ‖γ s‖ :=
begin
  obtain ⟨u, hu, ht⟩ := γ.periodic.exists_mem_Ico₀ zero_lt_one t,
  replace hu := mem_Icc_of_Ico hu,
  rw ht,
  have h₁ : set.nonempty (range (λ (s : I), ‖γ s‖)) := ⟨‖γ 0‖, 0, rfl⟩,
  have h₂ : bdd_above (range (λ (s : I), ‖γ s‖)),
  { convert is_compact_Icc.bdd_above_image (continuous_norm.comp hγ).continuous_on, ext, simp, },
  exact (real.is_lub_Sup _ h₁ h₂).1 ⟨⟨u, hu⟩, rfl⟩,
end

/-- Reparametrizing loop `γ` using an equivariant map `φ`. -/
@[simps {simp_rhs := tt}]
def reparam {F : Type*} (γ : loop F) (φ : equivariant_map) : loop F :=
{ to_fun := γ ∘ φ,
  per' := λ t, by rw [comp_apply, φ.eqv, γ.per] }

/-! ## Support of a loop family -/

/-- A loop is constant if it takes the same value at every time.
See also `loop.is_const_iff_forall_avg` and `loop.is_const_iff_const_avg` for characterizations in
terms of average values. -/
def is_const (γ : loop X) := ∀ t s, γ t = γ s

lemma is_const_of_eq {γ : loop X} {f : X} (H : ∀ t, γ t = f) : γ.is_const :=
λ t t', by rw [H, H]

variables [topological_space X] [topological_space X']
variables [topological_space Y] [topological_space Z]

/-- The support of a loop family is the closure of the set of parameters where
the loop is not constant. -/
def support (γ : X → loop X') : set X :=
closure {x | ¬ (γ x).is_const}

lemma not_mem_support {γ : X → loop X'} {x : X} (h : ∀ᶠ y in 𝓝 x, (γ y).is_const) :
  x ∉ loop.support γ :=
begin
  intro hx,
  rw [support, mem_closure_iff_nhds] at hx,
  rcases hx _ h with ⟨z, hz, hz'⟩,
  exact hz' hz
end

/-! ## From paths to loops -/

/-- Turn a path into a loop. -/
@[simps]
noncomputable def of_path {x : X} (γ : path x x) : loop X :=
{ to_fun := λ t, γ.extend (fract t),
  per' :=
  begin
    intros t,
    congr' 1,
    exact_mod_cast fract_add_int t 1
  end }

@[simp]
lemma range_of_path {x : X} (γ : path x x) : range (of_path γ) = range γ :=
begin
  rw loop.range_eq_image,
  unfold_coes,
  simp only [of_path, image_eq_range],
  congr,
  ext t,
  by_cases ht1 : t.val = 1,
  { have : t = ⟨1, right_mem_Icc.mpr zero_le_one⟩ := subtype.ext_val ht1,
    rw this,
    norm_cast,
    simp only [fract, floor_one, path.extend_zero, int.cast_one, sub_self, subtype.coe_mk],
    exact γ.target.symm },
  { change (t : ℝ) ≠ 1 at ht1,
    have : fract ↑t = t.val,
    { rw fract_eq_iff,
      refine ⟨t.2.1, t.2.2.lt_of_ne ht1, ⟨0, _⟩⟩,
      rw [int.cast_zero, subtype.val_eq_coe, sub_self] },
    simp only [this, γ.extend_extends t.2],
    congr',
    rw subtype.ext_iff_val }
end

/-- `loop.of_path` is continuous, general version. -/
lemma _root_.continuous.of_path (x : X → Y) (t : X → ℝ)
  (γ : ∀ i, path (x i) (x i)) (hγ : continuous ↿γ) (ht : continuous t) :
  continuous (λ i, of_path (γ i) (t i)) :=
begin
  change continuous (λ i, (λ s, (γ s).extend) i (fract (t i))),
  refine continuous_on.comp_fract _ ht _,
  { exact (hγ.comp (continuous_id.prod_map continuous_proj_Icc)).continuous_on },
  { simp only [Icc.mk_zero, zero_le_one, path.target, path.extend_extends,
      implies_true_iff, eq_self_iff_true, path.source, right_mem_Icc, left_mem_Icc,
      Icc.mk_one] }
end

/-- `loop.of_path` is continuous, where the endpoints of `γ` are fixed. TODO: remove -/
lemma of_path_continuous_family {x : Y} (γ : X → path x x)
  (h : continuous ↿γ) : continuous ↿(λ s, of_path $ γ s) :=
continuous.of_path _ _ (λ i : X × ℝ, γ i.1) (h.comp $ continuous_fst.prod_map continuous_id)
  continuous_snd

/-! ## Round trips -/

/-- The round-trip defined by `γ` is `γ` followed by `γ⁻¹`. -/
def round_trip {x y : X} (γ : path x y) : loop X :=
of_path (γ.trans γ.symm)

lemma round_trip_range {x y : X} {γ : path x y} : range (round_trip γ) = range γ :=
by simp [round_trip, range_of_path, path.trans_range, path.symm_range]

lemma round_trip_based_at {x y : X} {γ : path x y} : round_trip γ 0 = x :=
begin
  unfold_coes,
  rw [round_trip, of_path],
  simp [fract_zero]
end

lemma round_trip_eq {x y x' y' : X} {γ : path x y} {γ' : path x' y'} (h : ∀ s, γ s = γ' s) :
  round_trip γ = round_trip γ' :=
begin
  obtain rfl : x = x' := γ.source.symm.trans ((h 0).trans γ'.source),
  obtain rfl : y = y' := γ.target.symm.trans ((h 1).trans γ'.target),
  obtain rfl : γ = γ', { ext, apply h },
  refl,
end


/-- The round trip loop family associated to a path `γ`. For each parameter `t`,
the loop `round_trip_family γ t` backtracks at `γ t`. -/
noncomputable
def round_trip_family {x y : X} (γ : path x y) : ℝ → loop X :=
have key : ∀ {t}, x = γ.extend (min 0 t) := λ t, (γ.extend_of_le_zero $ min_le_left _ _).symm,
λ t, round_trip ((γ.truncate 0 t).cast key rfl)

lemma round_trip_family_continuous {x y : X} {γ : path x y} : continuous ↿(round_trip_family γ) :=
of_path_continuous_family _
  (path.trans_continuous_family _ (γ.truncate_const_continuous_family 0) _ $
    path.symm_continuous_family _ $ γ.truncate_const_continuous_family 0)

lemma round_trip_family_based_at {x y : X} {γ : path x y} : ∀ t, (round_trip_family γ) t 0 = x :=
λ t, round_trip_based_at

lemma round_trip_family_zero {x y : X} {γ : path x y} :
  (round_trip_family γ) 0 = of_path (path.refl x) :=
begin
  simp only [round_trip_family, round_trip, path.truncate_zero_zero, of_path],
  ext z,
  congr,
  ext t,
  simp [path.refl_symm]
end

lemma round_trip_family_one {x y : X} {γ : path x y} : (round_trip_family γ) 1 = round_trip γ :=
begin
  simp only [round_trip_family, round_trip, path.truncate_zero_one, of_path],
  refl
end


section average

/-! ## Average value of a loop -/

variables [measurable_space F] [borel_space F] [second_countable_topology F] [complete_space F]

/-- The average value of a loop. -/
noncomputable def average (γ : loop F) : F :=
∫ x in 0..1, (γ x)

-- unused
@[simp]
lemma zero_average : average (0 : loop F) = 0 :=
interval_integral.integral_zero

lemma is_const_iff_forall_avg {γ : loop F} : γ.is_const ↔ ∀ t, γ t = γ.average :=
begin
  split ; intro h,
  { intro t,
    have : γ = loop.const (γ t),
    { ext s,
      rw h s t,
      refl },
    rw this,
    simp only [average, const_apply, interval_integral.integral_const, one_smul, sub_zero], },
  { exact is_const_of_eq h }
end

@[simp] lemma average_const {f : F} : (const f).average = f :=
by simp [loop.average]

open measure_theory
@[simp] lemma average_add {γ₁ γ₂ : loop F} (hγ₁ : interval_integrable γ₁ volume 0 1)
  (hγ₂ : interval_integrable γ₂ volume 0 1) : (γ₁ + γ₂).average = γ₁.average + γ₂.average :=
by simp [loop.average, interval_integral.integral_add hγ₁ hγ₂]

@[simp] lemma average_smul {γ : loop F} {c : ℝ} : (c • γ).average = c • γ.average :=
by simp [loop.average, interval_integral.integral_smul]

lemma is_const_iff_const_avg {γ : loop F} : γ.is_const ↔ γ = const γ.average :=
by { rw [loop.is_const_iff_forall_avg, loop.ext_iff, funext_iff], refl }

lemma is_const_of_not_mem_support {γ : X → loop F} {x : X}
  (hx : x ∉ support γ) : (γ x).is_const :=
begin
  classical,
  exact decidable.by_contradiction (λ H, hx (subset_closure H)),
end

lemma continuous_average {E : Type*} [topological_space E] [first_countable_topology E]
  [locally_compact_space E] {γ : E → loop F}
  (hγ_cont : continuous ↿γ) : continuous (λ x, (γ x).average) :=
continuous_parametric_interval_integral_of_continuous' hγ_cont _ _

/-- The normalization of a loop `γ` is the loop `γ - γ.average`. -/
def normalize (γ : loop F) : loop F :=
{ to_fun := λ t, γ t - γ.average,
  per' := λ t, by simp [γ.per] }

@[simp]
lemma normalize_apply (γ : loop F) (t : ℝ) : loop.normalize γ t = γ t - γ.average :=
rfl

@[simp]
lemma normalize_of_is_const {γ : loop F} (h : γ.is_const) : γ.normalize = 0 :=
begin
  ext t,
  simp [is_const_iff_forall_avg.mp h]
end

end average

end loop

section c1

/-! ## Differentiation of loop families -/


local notation `∂₁` := partial_fderiv_fst ℝ

variables (π : E → ℝ) (N : ℝ) (γ : E → loop F)
          (hγ : is_compact (loop.support γ))

/-- Differential of a loop family with respect to the parameter. -/
def loop.diff (γ : E → loop F) (e : E) : loop (E →L[ℝ] F) :=
{ to_fun := λ t, ∂₁ (λ e t, γ e t) e t,
  per' := λ t, by simp only [partial_fderiv_fst, loop.per] }

@[simp]
lemma loop.diff_apply (γ : E → loop F) (e : E) (t : ℝ) : loop.diff γ e t = ∂₁ (λ e t, γ e t) e t :=
rfl

lemma loop.continuous_diff {γ : E → loop F} (h : 𝒞 1 ↿γ) : continuous (↿(loop.diff γ)) :=
cont_diff.continuous_partial_fst (h : _)

lemma cont_diff.partial_loop {γ : E → loop F} {n : ℕ∞} (hγ_diff : 𝒞 n ↿γ) :
  ∀ t, 𝒞 n (λ e, γ e t) :=
λ t, hγ_diff.comp ((cont_diff_prod_mk_left t).of_le le_top)

variables [measurable_space F] [borel_space F] [finite_dimensional ℝ F]

lemma loop.support_diff {γ : E → loop F} :
  loop.support (loop.diff γ) ⊆ loop.support γ :=
begin
  unfold loop.support,
  erw [closure_compl, closure_compl],
  rw compl_subset_compl,
  intros x hx,
  rw mem_interior_iff_mem_nhds at *,
  rcases mem_nhds_iff.mp hx with ⟨U, hU, U_op, hxU⟩,
  have U_nhds : U ∈ 𝓝 x, from is_open.mem_nhds U_op hxU,
  apply filter.mem_of_superset U_nhds,
  intros y hy,
  have Hy : ∀ t, (λ z, γ z t) =ᶠ[𝓝 y] (λ z, (γ z).average),
  { intro t,
    apply filter.mem_of_superset (U_op.mem_nhds hy),
    intros z hz,
    exact loop.is_const_iff_forall_avg.mp (hU hz) t },
  have : ∀ (t : ℝ), loop.diff γ y t = D (λ (z : E), (γ z).average) y := λ t, (Hy t).fderiv_eq,
  intros t s,
  simp [this]
end

variables [finite_dimensional ℝ E]

lemma loop.average_diff {γ : E → loop F} (hγ_diff : 𝒞 1 ↿γ) (e : E) :
(loop.diff γ e).average = D (λ e, (γ e).average) e :=
begin
  change 𝒞 1 ↿(λ (e : E) (t : ℝ), γ e t) at hγ_diff,
  simpa only [loop.average, hγ_diff.fderiv_parametric_integral]
end

lemma cont_diff.loop_average {γ : E → loop F} {n : ℕ∞} (hγ_diff : 𝒞 n ↿γ) :
  𝒞 n (λ e, (γ e).average) :=
cont_diff_parametric_integral_of_cont_diff hγ_diff _ _

lemma loop.diff_normalize {γ : E → loop F} (hγ_diff : 𝒞 1 ↿γ) (e : E) :
  (loop.diff γ e).normalize = loop.diff (λ e, (γ e).normalize) e :=
begin
  ext t x,
  simp only [loop.diff_apply, loop.normalize_apply, partial_fderiv_fst],

  rw [fderiv_sub ((hγ_diff.partial_loop t).differentiable le_rfl).differentiable_at,
      loop.average_diff hγ_diff],
  exact (hγ_diff.loop_average.differentiable le_rfl).differentiable_at
end

variable {γ}

lemma cont_diff_average {n : ℕ∞} (hγ_diff : 𝒞 n ↿γ) : 𝒞 n (λ x, (γ x).average) :=
cont_diff_parametric_primitive_of_cont_diff hγ_diff cont_diff_const 0

lemma cont_diff_sub_average {n : ℕ∞} (hγ_diff : 𝒞 n ↿γ) :
  𝒞 n ↿(λ (x : E) (t : ℝ), (γ x) t - (γ x).average) :=
hγ_diff.sub (cont_diff_average hγ_diff).fst'

end c1
