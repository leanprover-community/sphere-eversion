import SphereEversion.ToMathlib.Equivariant
import SphereEversion.ToMathlib.MeasureTheory.ParametricIntervalIntegral

import SphereEversion.FunPropConfig

/-!
# Basic definitions and properties of loops
-/


open Set Function FiniteDimensional Int TopologicalSpace

open scoped BigOperators Topology unitInterval

noncomputable section

variable {K X X' Y Z : Type _}

-- variable [TopologicalSpace X'] [TopologicalSpace Y] [TopologicalSpace Z]
variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : Type _} [NormedAddCommGroup F]
  [NormedSpace ℝ F] {F' : Type _} [NormedAddCommGroup F'] [NormedSpace ℝ F']

/-! ## Definition and periodicity lemmas -/


variable (X)

/-- A loop is a function with domain `ℝ` and is periodic with period 1. -/
structure Loop where
  toFun : ℝ → X
  per' : ∀ t, toFun (t + 1) = toFun t

instance : FunLike (Loop X) ℝ X where
  coe := fun γ ↦ γ.toFun
  coe_injective' := sorry


initialize_simps_projections Loop (toFun → apply)

/-- Any function `φ : α → loop X` can be seen as a function `α × ℝ → X`. -/
instance hasUncurryLoop {α : Type _} : HasUncurry (α → Loop X) (α × ℝ) X :=
  ⟨fun φ p ↦ φ p.1 p.2⟩

variable {X}

namespace Loop

@[simp]
protected theorem coe_mk {γ : ℝ → X} (h : ∀ t, γ (t + 1) = γ t) : ⇑(⟨γ, h⟩ : Loop X) = γ :=
  rfl

@[ext]
protected theorem ext : ∀ {γ₁ γ₂ : Loop X}, (γ₁ : ℝ → X) = γ₂ → γ₁ = γ₂
  | ⟨_x, _h1⟩, ⟨.(_x), _h2⟩, rfl => rfl

protected theorem ext_iff {γ₁ γ₂ : Loop X} : γ₁ = γ₂ ↔ (γ₁ : ℝ → X) = γ₂ :=
  ⟨fun h ↦ by rw [h], Loop.ext⟩

/-- The constant loop. -/
@[simps]
def const (f : X) : Loop X :=
  ⟨fun _ ↦ f, fun _ ↦ rfl⟩

instance Loop.Zero [Zero X] : Zero (Loop X) :=
  ⟨const 0⟩

@[simp]
theorem zero_fun [Zero X] : ((0 : Loop X) : ℝ → X) = (0 : ℝ → X) :=
  rfl

-- unused
@[simp]
theorem const_zero [Zero X] : const (0 : X) = (0 : Loop X) :=
  rfl

instance [Inhabited X] : Inhabited (Loop X) :=
  ⟨Loop.const default⟩

/-- Periodicity of loops restated in terms of the function coercion. -/
theorem per (γ : Loop X) : ∀ t, γ (t + 1) = γ t :=
  Loop.per' γ

theorem periodic (γ : Loop X) : Function.Periodic γ 1 :=
  Loop.per' γ

protected theorem one (γ : Loop X) : γ 1 = γ 0 := by convert γ.per 0; rw [zero_add]

-- unused
theorem add_nat_eq (γ : Loop X) (t : ℝ) : ∀ n : ℕ, γ (t + n) = γ t
  | 0 => by rw [Nat.cast_zero, add_zero]
  | Nat.succ n => by rw [← γ.add_nat_eq t n, Nat.cast_succ, ← add_assoc, γ.per]

theorem add_int_eq (γ : Loop X) (t : ℝ) (n : ℤ) : γ (t + n) = γ t := by
  induction' n using Int.induction_on with n hn n hn
  · norm_cast; rw [add_zero]
  · rw [← hn, Int.cast_add, ← add_assoc, Int.cast_one, γ.per]
  · rw [← hn, Int.cast_sub, add_sub, Int.cast_one, ← γ.per, sub_add_cancel]

theorem fract_eq (γ : Loop X) : ∀ t, γ (fract t) = γ t := by
  intro t
  unfold fract
  rw [sub_eq_add_neg, ← Int.cast_neg]
  exact γ.add_int_eq _ _

theorem range_eq_image (γ : Loop X) : range γ = γ '' I := by
  apply eq_of_subset_of_subset
  · rw [range_subset_iff]
    exact fun y ↦ ⟨fract y, unitInterval.fract_mem y, γ.fract_eq _⟩
  · rintro y ⟨x, -, hxy⟩
    exact ⟨x, hxy⟩

/-- Transforming a loop by applying function `f`. -/
@[simps]
def transform (γ : Loop X) (f : X → X') : Loop X' :=
  ⟨fun t ↦ f (γ t), fun t ↦ by dsimp only; rw [γ.per]⟩

/-- Adding two loops pointwise. -/
@[simps]
instance Loop.Add [Add X] : Add (Loop X) :=
  ⟨fun γ₁ γ₂ ↦ ⟨fun t ↦ γ₁ t + γ₂ t, fun t ↦ by simp_rw [Loop.per]⟩⟩

@[simps]
instance Loop.Neg [Neg X] : Neg (Loop X) :=
  ⟨fun γ ↦ ⟨fun t ↦ -γ t, fun t ↦ by simp_rw [Loop.per]⟩⟩

instance [AddCommGroup X] : AddCommGroup (Loop X) :=
  { Loop.Add, Loop.Zero,
    Loop.Neg with
    add_assoc := fun γ₁ γ₂ γ₃ ↦ by ext t; apply add_assoc
    add_comm := fun γ₁ γ₂ ↦ by ext t; apply add_comm
    zero_add := fun γ ↦ by ext t; apply zero_add
    add_zero := fun γ ↦ by ext t; apply add_zero
    add_left_neg := fun γ ↦ by ext t; apply add_left_neg }

/-- Shifting a loop, or equivalently, adding a constant value to a loop. -/
instance [Add X] : VAdd X (Loop X) :=
  ⟨fun x γ ↦ γ.transform fun y ↦ x + y⟩

@[simp]
theorem vadd_apply [Add X] {x : X} {γ : Loop X} {t : ℝ} : (x +ᵥ γ) t = x + γ t :=
  rfl

/-- Multiplying a loop by a scalar value. -/
instance [SMul K X] : SMul K (Loop X) :=
  ⟨fun k γ ↦ γ.transform fun y ↦ k • y⟩

instance [Semiring K] [AddCommGroup X] [Module K X] : Module K (Loop X)
    where
  one_smul γ := by ext t; apply one_smul
  mul_smul k₁ k₂ γ := by ext t; apply mul_smul
  smul_zero k := by ext ; apply smul_zero
  smul_add k γ₁ γ₂ := by ext t; apply smul_add
  add_smul k₁ k₂ γ := by ext t; apply add_smul
  zero_smul γ := by ext t; apply zero_smul

@[simp]
theorem smul_apply [SMul K X] {k : K} {γ : Loop X} {t : ℝ} : (k • γ) t = k • γ t :=
  rfl

/-- Reparametrizing loop `γ` using an equivariant map `φ`. -/
@[simps (config := { simpRhs := true })]
def reparam {F : Type _} (γ : Loop F) (φ : EquivariantMap) : Loop F
    where
  toFun := γ ∘ φ
  per' t := by rw [comp_apply, φ.eqv, γ.per] ; rfl

/-! ## Support of a loop family -/


/-- A loop is constant if it takes the same value at every time.
See also `Loop.isConst_iff_forall_avg` and `Loop.isConst_iff_const_avg` for characterizations in
terms of average values. -/
def IsConst (γ : Loop X) :=
  ∀ t s, γ t = γ s

theorem isConst_of_eq {γ : Loop X} {f : X} (H : ∀ t, γ t = f) : γ.IsConst := fun t t' ↦ by
  rw [H, H]

variable [TopologicalSpace X] [TopologicalSpace X']

variable [TopologicalSpace Y] [TopologicalSpace Z]

/-- The support of a loop family is the closure of the set of parameters where
the loop is not constant. -/
def support (γ : X → Loop X') : Set X :=
  closure {x | ¬(γ x).IsConst}

theorem not_mem_support {γ : X → Loop X'} {x : X} (h : ∀ᶠ y in 𝓝 x, (γ y).IsConst) :
    x ∉ Loop.support γ := by
  intro hx
  rw [support, mem_closure_iff_nhds] at hx
  rcases hx _ h with ⟨z, hz, hz'⟩
  exact hz' hz

/-! ## From paths to loops -/


/-- Turn a path into a loop. -/
@[simps]
noncomputable def ofPath {x : X} (γ : Path x x) : Loop X where
  toFun t := γ.extend (fract t)
  per' := by
    intro t
    dsimp
    congr 1
    exact_mod_cast fract_add_int t 1

@[simp]
theorem range_ofPath {x : X} (γ : Path x x) : range (ofPath γ) = range γ := by
  rw [Loop.range_eq_image]
  simp only [ofPath, image_eq_range]
  apply congrArg
  ext t
  by_cases ht1 : t.val = 1
  · have : t = ⟨1, right_mem_Icc.mpr zero_le_one⟩ := Subtype.ext_val ht1
    rw [this]
    norm_cast
    simp only [Loop.coe_mk, fract_one, mem_Icc, le_refl, zero_le_one, and_self, Path.extend_extends,
      Icc.mk_zero, Path.source, Icc.mk_one, Path.target]
  · change (t : ℝ) ≠ 1 at ht1
    have : fract ↑t = t.val := by
      rw [fract_eq_iff]
      refine' ⟨t.2.1, t.2.2.lt_of_ne ht1, ⟨0, _⟩⟩
      rw [Int.cast_zero, sub_self]
    simp only [Loop.coe_mk, this, Path.extend_extends']

/-- `Loop.ofPath` is continuous, general version. -/
theorem _root_.Continuous.ofPath (x : X → Y) (t : X → ℝ) (γ : ∀ i, Path (x i) (x i)) (hγ : Continuous ↿γ)
    (ht : Continuous t) : Continuous fun i ↦ ofPath (γ i) (t i) := by
  change Continuous fun i ↦ (fun s ↦ (γ s).extend) i (fract (t i))
  refine' ContinuousOn.comp_fract _ ht _
  · have : Continuous (fun x : X × ℝ ↦ (x.1, projIcc 0 1 zero_le_one x.2)) := by
      fun_prop
    exact (hγ.comp this).continuousOn -- TODO: cannot use fun_prop, uncurrying?
  · simp only [Icc.mk_zero, zero_le_one, Path.target, Path.extend_extends, imp_true_iff,
      eq_self_iff_true, Path.source, right_mem_Icc, left_mem_Icc, Icc.mk_one]

/-- `Loop.ofPath` is continuous, where the endpoints of `γ` are fixed. TODO: remove -/
theorem ofPath_continuous_family {x : Y} (γ : X → Path x x) (h : Continuous ↿γ) :
    Continuous ↿fun s ↦ ofPath <| γ s :=
  -- use by fun_prop
  Continuous.ofPath _ _ (fun i : X × ℝ ↦ γ i.1) (h.comp <| continuous_fst.prod_map continuous_id)
    continuous_snd

/-! ## Round trips -/


/-- The round-trip defined by `γ` is `γ` followed by `γ⁻¹`. -/
def roundTrip {x y : X} (γ : Path x y) : Loop X :=
  ofPath (γ.trans γ.symm)

theorem roundTrip_range {x y : X} {γ : Path x y} : range (roundTrip γ) = range γ := by
  simp [roundTrip, range_ofPath, Path.trans_range, Path.symm_range]

theorem roundTrip_based_at {x y : X} {γ : Path x y} : roundTrip γ 0 = x := by
  simp [roundTrip, ofPath, fract_zero]

theorem roundTrip_eq {x y x' y' : X} {γ : Path x y} {γ' : Path x' y'} (h : ∀ s, γ s = γ' s) :
    roundTrip γ = roundTrip γ' := by
  obtain rfl : x = x' := γ.source.symm.trans ((h 0).trans γ'.source)
  obtain rfl : y = y' := γ.target.symm.trans ((h 1).trans γ'.target)
  obtain rfl : γ = γ' := by ext; apply h
  rfl

/-- The round trip loop family associated to a path `γ`. For each parameter `t`,
the loop `roundTripFamily γ t` backtracks at `γ t`. -/
noncomputable def roundTripFamily {x y : X} (γ : Path x y) : ℝ → Loop X :=
  have key : ∀ {t}, x = γ.extend (min 0 t) := (γ.extend_of_le_zero <| min_le_left _ _).symm
  fun t ↦ roundTrip ((γ.truncate 0 t).cast key rfl)

theorem roundTripFamily_continuous {x y : X} {γ : Path x y} : Continuous ↿(roundTripFamily γ) :=
  ofPath_continuous_family _
    (Path.trans_continuous_family _ (γ.truncate_const_continuous_family 0) _ <|
      Path.symm_continuous_family _ <| γ.truncate_const_continuous_family 0)

theorem roundTripFamily_based_at {x y : X} {γ : Path x y} : ∀ t, (roundTripFamily γ) t 0 = x :=
  fun _ ↦ roundTrip_based_at

theorem roundTripFamily_zero {x y : X} {γ : Path x y} :
    (roundTripFamily γ) 0 = ofPath (Path.refl x) := by
  simp only [roundTripFamily, roundTrip, Path.truncate_zero_zero, ofPath]
  ext z
  congr
  ext t
  simp [Path.refl_symm]
  rfl

theorem roundTripFamily_one {x y : X} {γ : Path x y} : (roundTripFamily γ) 1 = roundTrip γ := by
  simp only [roundTripFamily, roundTrip, Path.truncate_zero_one, ofPath]
  rfl

section Average

/-! ## Average value of a loop -/


variable [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] [CompleteSpace F]

/-- The average value of a loop. -/
noncomputable def average (γ : Loop F) : F :=
  ∫ x in (0 : ℝ)..1, γ x

-- unused
@[simp]
theorem zero_average : average (0 : Loop F) = 0 :=
  intervalIntegral.integral_zero

theorem isConst_iff_forall_avg {γ : Loop F} : γ.IsConst ↔ ∀ t, γ t = γ.average := by
  constructor <;> intro h
  · intro t
    have : γ = Loop.const (γ t) := by
      ext s
      rw [h s t]
      rfl
    rw [this]
    simp only [average, const_apply, intervalIntegral.integral_const, one_smul, sub_zero]
  · exact isConst_of_eq h

@[simp]
theorem average_const {f : F} : (const f).average = f := by simp [Loop.average]

open MeasureTheory

@[simp]
theorem average_add {γ₁ γ₂ : Loop F} (hγ₁ : IntervalIntegrable γ₁ volume 0 1)
    (hγ₂ : IntervalIntegrable γ₂ volume 0 1) : (γ₁ + γ₂).average = γ₁.average + γ₂.average := by
  simp [Loop.average, intervalIntegral.integral_add hγ₁ hγ₂]

@[simp]
theorem average_smul {γ : Loop F} {c : ℝ} : (c • γ).average = c • γ.average := by
  simp [Loop.average, intervalIntegral.integral_smul]

theorem isConst_iff_const_avg {γ : Loop F} : γ.IsConst ↔ γ = const γ.average := by
  rw [Loop.isConst_iff_forall_avg, Loop.ext_iff, funext_iff]; rfl

theorem isConst_of_not_mem_support {γ : X → Loop F} {x : X} (hx : x ∉ support γ) : (γ x).IsConst := by
  classical exact Decidable.by_contradiction fun H ↦ hx (subset_closure H)

@[fun_prop]
theorem continuous_average {E : Type _} [TopologicalSpace E] [FirstCountableTopology E]
    [LocallyCompactSpace E] {γ : E → Loop F} (hγ_cont : Continuous ↿γ) :
    Continuous fun x ↦ (γ x).average :=
  continuous_parametric_intervalIntegral_of_continuous' hγ_cont _ _

/-- The normalization of a loop `γ` is the loop `γ - γ.average`. -/
def normalize (γ : Loop F) : Loop F
    where
  toFun t := γ t - γ.average
  per' t := by simp [γ.per]

@[simp]
theorem normalize_apply (γ : Loop F) (t : ℝ) : Loop.normalize γ t = γ t - γ.average :=
  rfl

@[simp]
theorem normalize_of_isConst {γ : Loop F} (h : γ.IsConst) : γ.normalize = 0 := by
  ext t
  simp [isConst_iff_forall_avg.mp h]

end Average

end Loop

section C1

/-! ## Differentiation of loop families -/


local notation "∂₁" => partialFDerivFst ℝ

variable (π : E → ℝ) (N : ℝ) (γ : E → Loop F) (hγ : IsCompact (Loop.support γ))

/-- Differential of a loop family with respect to the parameter. -/
def Loop.diff (γ : E → Loop F) (e : E) : Loop (E →L[ℝ] F)
    where
  toFun t := ∂₁ (fun e t ↦ γ e t) e t
  per' t := by simp only [partialFDerivFst, Loop.per]

@[simp]
theorem Loop.diff_apply (γ : E → Loop F) (e : E) (t : ℝ) :
    Loop.diff γ e t = ∂₁ (fun e t ↦ γ e t) e t :=
  rfl

theorem Loop.continuous_diff {γ : E → Loop F} (h : 𝒞 1 ↿γ) : Continuous ↿(Loop.diff γ) :=
  ContDiff.continuous_partial_fst (h : _)

theorem ContDiff.partial_loop {γ : E → Loop F} {n : ℕ∞} (hγ_diff : 𝒞 n ↿γ) :
    ∀ t, 𝒞 n fun e ↦ γ e t := fun t ↦ hγ_diff.comp ((contDiff_prod_mk_left t).of_le le_top)

variable [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]

theorem Loop.support_diff {γ : E → Loop F} : Loop.support (Loop.diff γ) ⊆ Loop.support γ := by
  unfold Loop.support
  erw [closure_compl, closure_compl]
  rw [compl_subset_compl]
  intro x hx
  rw [mem_interior_iff_mem_nhds] at *
  rcases mem_nhds_iff.mp hx with ⟨U, hU, U_op, hxU⟩
  have U_nhds : U ∈ 𝓝 x := IsOpen.mem_nhds U_op hxU
  apply Filter.mem_of_superset U_nhds
  intro y hy
  have Hy : ∀ t, (fun z ↦ γ z t) =ᶠ[𝓝 y] fun z ↦ (γ z).average := by
    intro t
    apply Filter.mem_of_superset (U_op.mem_nhds hy)
    intro z hz
    exact Loop.isConst_iff_forall_avg.mp (hU hz) t
  have : ∀ t : ℝ, Loop.diff γ y t = D (fun z : E ↦ (γ z).average) y := fun t ↦ (Hy t).fderiv_eq
  intro t s
  simp only [this]


variable [FiniteDimensional ℝ E]

theorem Loop.average_diff {γ : E → Loop F} (hγ_diff : 𝒞 1 ↿γ) (e : E) :
    (Loop.diff γ e).average = D (fun e ↦ (γ e).average) e := by
  change 𝒞 1 ↿fun (e : E) (t : ℝ) ↦ γ e t at hγ_diff
  simp only [Loop.average, hγ_diff.fderiv_parametric_integral]
  rfl

theorem ContDiff.loop_average {γ : E → Loop F} {n : ℕ∞} (hγ_diff : 𝒞 n ↿γ) :
    𝒞 n fun e ↦ (γ e).average :=
  contDiff_parametric_integral_of_contDiff hγ_diff _ _

theorem Loop.diff_normalize {γ : E → Loop F} (hγ_diff : 𝒞 1 ↿γ) (e : E) :
    (Loop.diff γ e).normalize = Loop.diff (fun e ↦ (γ e).normalize) e := by
  ext t x
  simp only [Loop.diff_apply, Loop.normalize_apply, partialFDerivFst]
  rw [fderiv_sub ((hγ_diff.partial_loop t).differentiable le_rfl).differentiableAt,
    Loop.average_diff hγ_diff]
  exact (hγ_diff.loop_average.differentiable le_rfl).differentiableAt

variable {γ}

@[fun_prop]
theorem contDiff_average {n : ℕ∞} (hγ_diff : 𝒞 n (fun (x,t) => γ x t)) : 𝒞 n fun x ↦ (γ x).average :=
  contDiff_parametric_primitive_of_contDiff hγ_diff contDiff_const 0

@[fun_prop]
theorem contDiff_sub_average {n : ℕ∞} (hγ_diff : 𝒞 n ↿γ) :
    𝒞 n ↿fun (x : E) (t : ℝ) ↦ (γ x) t - (γ x).average :=
  hγ_diff.sub (contDiff_average hγ_diff).fst'

end C1
