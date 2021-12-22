import analysis.normed_space.add_torsor_bases
import analysis.convex.caratheodory
import analysis.calculus.times_cont_diff
import measure_theory.integral.interval_integral
import measure_theory.measure.lebesgue
import topology.algebra.floor_ring
import topology.path_connected
import linear_algebra.affine_space.independent

import to_mathlib.homotheties
import to_mathlib.smooth_barycentric
import to_mathlib.topology.path
import to_mathlib.linear_algebra.affine_space.basis
import to_mathlib.measure_theory.parametric_interval_integral

/-!
# Basic definitions and properties of loops
-/

open set function finite_dimensional int topological_space
open_locale big_operators topological_space topological_space unit_interval
noncomputable theory

variables {X X' Y Z : Type*} [topological_space X]
variables [topological_space X'] [topological_space Y] [topological_space Z]
variables {E : Type*} [normed_group E] [normed_space ℝ E]
          {F : Type*} [normed_group F] [normed_space ℝ F] 
          {F' : Type*} [normed_group F'] [normed_space ℝ F'] 

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
@[uncurry_simps]
instance has_uncurry_loop {α : Type*} : has_uncurry (α → loop X) (α × ℝ) X := ⟨λ φ p, φ p.1 p.2⟩

variables {X}

namespace loop

@[ext] protected lemma ext : ∀ {γ₁ γ₂ : loop X}, (γ₁ : ℝ → X) = γ₂ → γ₁ = γ₂
| ⟨x, h1⟩ ⟨.(x), h2⟩ rfl := rfl

instance [has_zero X] : has_zero (loop X) :=
⟨{ to_fun := λ t, 0, per' := λ t, rfl }⟩

/-- The constant loop. -/
@[simps]
def const (f : X) : loop X :=
⟨λ t, f, by simp⟩

@[simp] lemma const_zero [has_zero X] : const (0 : X) = (0 : loop X) :=
begin
  ext t,
  refl
end

instance [inhabited X] : inhabited (loop X) :=
⟨loop.const (default X)⟩

/-- Periodicity of loops restated in terms of the function coercion. -/
lemma per (γ : loop X) : ∀ t, γ (t + 1) = γ t :=
loop.per' γ

protected lemma one (γ : loop X) : γ 1 = γ 0 :=
by { convert γ.per 0, rw [zero_add] }

lemma add_nat_eq (γ : loop X) (t : ℝ) : ∀ (n : ℕ), γ (t+n) = γ t
| 0 := (add_zero t).symm ▸ rfl
| (nat.succ n) := by rw [← add_nat_eq n, nat.cast_succ, ← add_assoc, γ.per]

lemma add_int_eq (γ : loop X) (t : ℝ) (n : ℤ) : γ (t+n) = γ t :=
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

lemma comp_fract_eq (γ : loop X) : γ ∘ fract = γ :=
funext γ.fract_eq

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

/-- Shifting a loop, or equivalently, adding a constant value to a loop -/
@[simps]
def shift {F : Type*} [add_group F] [topological_space F] (γ : loop F) (x : F) : loop F :=
γ.transform (+ x)

/-! ## Support of a loop family -/

/-- A loop is constant if it takes the same value at every time. 
See also `loop.is_const_iff_forall_avg` and `loop.is_const_iff_const_avg` for characterizations in
terms of average values. -/
def is_const (γ : loop X) := ∀ t s, γ t = γ s

/-- The support of a loop family is the closure of the set of parameters where
the loop is not constant. -/
def support (γ : X → loop X') : set X :=
closure {x | ¬ (γ x).is_const}

lemma is_closed_support (γ : X → loop X') : is_closed (loop.support γ) :=
is_closed_closure

lemma continuous_of_family {γ : X → loop X'} (h : continuous ↿γ) (x : X) : continuous (γ x) :=
h.comp $ continuous_const.prod_mk continuous_id

lemma continuous_of_family_step {γ : X → Y → loop Z} (h : continuous ↿γ) (x : X) :
  continuous ↿(γ x) :=
h.comp $ continuous_const.prod_mk continuous_id

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
      exact ⟨t.2.1, lt_of_le_of_ne t.2.2 ht1, ⟨0, sub_self _⟩⟩ },
    simp only [this, γ.extend_extends t.2],
    congr',
    rw subtype.ext_iff_val }
end

lemma of_path_continuous {x : X} (γ : path x x) : continuous (of_path γ) :=
begin
  simp only [has_coe_to_fun.coe, coe_fn, of_path],
  apply γ.continuous_extend.continuous_on.comp_fract,
  rw [γ.extend_zero, γ.extend_one]
end

/-- `loop.of_path` is continuous, general version. -/
lemma _root_.continuous.of_path (x : X → Y) (t : X → ℝ)
  (γ : ∀ i, path (x i) (x i)) (hγ : continuous ↿γ) (ht : continuous t) :
  continuous (λ i, of_path (γ i) (t i)) :=
begin
  change continuous (λ i, (λ s, (γ s).extend) i (fract (t i))),
  refine continuous_on.comp_fract'' _ ht _,
  { exact (hγ.comp (continuous_id.prod_map continuous_proj_Icc)).continuous_on },
  { simp only [unit_interval.mk_zero, zero_le_one, path.target, path.extend_extends,
      implies_true_iff, eq_self_iff_true, path.source, right_mem_Icc, left_mem_Icc,
      unit_interval.mk_one] }
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

lemma round_trip_continuous {x y : X} (γ : path x y) : continuous (round_trip γ) :=
of_path_continuous _

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
  { intros t s,
    rw [h, h] }
end

@[simp] lemma average_const {f : F} : (loop.const f).average = f :=
by simp [loop.average]

lemma is_const_iff_const_avg {γ : loop F} : γ.is_const ↔ γ = loop.const γ.average :=
begin
  rw loop.is_const_iff_forall_avg,  
  split,
  { intro h,
    ext s,
    apply h },
  { intros h t,
    rw h,
    simp }
end

lemma const_of_not_mem_support {γ : X → loop F} {x : X}
  (hx : x ∉ support γ) : γ x = loop.const (γ x).average :=
begin
  classical,
  by_contradiction H,
  apply hx,
  apply subset_closure,
  simp_rw loop.is_const_iff_const_avg,
  exact H
end

lemma continuous_average {E : Type*} [topological_space E] [first_countable_topology E] [locally_compact_space E] {γ : E → loop F}
  (hγ_cont : continuous ↿γ) : continuous (λ x, (γ x).average) :=
continuous_parametric_interval_integral_of_continuous' hγ_cont _ _

/-- The normalization of a loop `γ` is the loop `γ - γ.average`. -/
def normalize (γ : loop F) : loop F :=
{ to_fun := λ t, γ t - γ.average,
  per' := λ t, by simp [γ.per] }

@[simp]
lemma normalize_apply (γ : loop F) (t : ℝ) : loop.normalize γ t = γ t - γ.average :=
rfl

end average

end loop

section c1

/-! ## Differentiation of loop families -/

local notation `D` := fderiv ℝ
local notation `∂₁` := partial_fderiv_fst ℝ
local notation `𝒞` := times_cont_diff ℝ

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
times_cont_diff.continuous_partial_fst (h : _)

lemma times_cont_diff.partial_loop {γ : E → loop F} (hγ_diff : 𝒞 1 ↿γ) :
  ∀ t, 𝒞 1 (λ e, γ e t) :=
λ t, hγ_diff.comp ((times_cont_diff_prod_left t).of_le le_top)

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

lemma loop.compact_support_diff {γ : E → loop F}  (h' : is_compact (loop.support γ)):
  is_compact (loop.support $ loop.diff γ) :=
compact_of_is_closed_subset h' is_closed_closure loop.support_diff

variables [finite_dimensional ℝ E]
          
lemma loop.average_diff {γ : E → loop F} (hγ_diff : 𝒞 1 ↿γ) (e : E) :
(loop.diff γ e).average = D (λ e, (γ e).average) e :=
begin
  change 𝒞 1 ↿(λ (e : E) (t : ℝ), γ e t) at hγ_diff,
  simpa only [loop.average, hγ_diff.fderiv_parametric_integral]
end

lemma times_cont_diff.loop_average {γ : E → loop F} {n : with_top ℕ} (hγ_diff : 𝒞 n ↿γ) :
  𝒞 n (λ e, (γ e).average) :=
times_cont_diff_parametric_integral_of_times_cont_diff hγ_diff _ _

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

lemma times_cont_diff_average {n : with_top ℕ} (hγ_diff : 𝒞 n ↿γ) : 𝒞 n (λ x, (γ x).average) :=
times_cont_diff_parametric_primitive_of_times_cont_diff hγ_diff times_cont_diff_const 0

lemma times_cont_diff_sub_average {n : with_top ℕ} (hγ_diff : 𝒞 n ↿γ) :
  𝒞 n ↿(λ (x : E) (t : ℝ), (γ x) t - (γ x).average) :=
hγ_diff.sub ((times_cont_diff_average hγ_diff).comp times_cont_diff_fst)

end c1
