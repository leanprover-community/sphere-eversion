import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import SphereEversion.Notations

/-! # Spaces of 1-jets and their sections

For real normed spaces `E` and `F`, this file defines the space `OneJetSec E F` of 1-jets
of maps from `E` to `F` as `E × F × (E →L[ℝ] F)`.

A section `𝓕 : JetSet E F` of this space is a map `(𝓕.f, 𝓕.φ) : E → F × (E →L[ℝ] F)`.

It is holonomic at `x`, spelled `𝓕.IsHolonomicAt x` if the differential of `𝓕.f` at `x`
is `𝓕.φ x`.

We then introduced parametrized families of sections, and especially homotopies of sections,
with type `HtpyJetSec E F` and their concatenation operation `HtpyJetSec.comp`.


Implementation note: the time parameter `t` for homotopies is any real number, but all the
homotopies we will construct will be constant for `t ≤ 0` and `t ≥ 1`. It looks like this imposes
more smoothness constraints at `t = 0` and `t = 1` (requiring flat functions), but this is needed
for smooth concatenations anyway.
 -/


noncomputable section

open Set Function Real Filter

open scoped unitInterval Topology ContDiff


variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
  (P : Type*) [NormedAddCommGroup P] [NormedSpace ℝ P]

/-! ## Spaces of 1-jets -/


/-- The space of 1-jets of maps from `E` to `F`. -/
abbrev OneJet :=
  E × F × (E →L[ℝ] F)

instance : MetricSpace (OneJet E F) := inferInstanceAs (MetricSpace (E × F × (E →L[ℝ] F)))

/-- A smooth section of J¹(E, F) → E. -/
@[ext]
structure JetSec where
  f : E → F
  f_diff : 𝒞 ∞ f
  φ : E → E →L[ℝ] F
  φ_diff : 𝒞 ∞ φ

namespace JetSec

variable {E F}

instance : FunLike (JetSec E F) E (F × (E →L[ℝ] F)) where
  coe 𝓕 := fun x ↦ (𝓕.f x, 𝓕.φ x)
  coe_injective' := by
    rintro ⟨⟩ ⟨⟩ h; congr
    exacts [congr_arg (Prod.fst ∘ ·) h, congr_arg (Prod.snd ∘ ·) h]

@[simp]
theorem mk_apply (f : E → F) (f_diff φ φ_diff) (x : E) : mk f f_diff φ φ_diff x = (f x, φ x) := rfl

theorem eq_iff {𝓕 𝓕' : JetSec E F} {x : E} : 𝓕 x = 𝓕' x ↔ 𝓕.f x = 𝓕'.f x ∧ 𝓕.φ x = 𝓕'.φ x :=
  Prod.ext_iff

theorem coe_apply (𝓕 : JetSec E F) (x : E) : 𝓕 x = (𝓕.f x, 𝓕.φ x) :=
  rfl

theorem ext' {𝓕 𝓕' : JetSec E F} (h : ∀ x, 𝓕 x = 𝓕' x) : 𝓕 = 𝓕' :=
  DFunLike.ext _ _ h

/-! ## Holonomic sections-/

/-- A jet section `𝓕` is holonomic if its linear map part at `x`
is the derivative of its function part at `x`. -/
def IsHolonomicAt (𝓕 : JetSec E F) (x : E) : Prop :=
  D 𝓕.f x = 𝓕.φ x

theorem IsHolonomicAt.congr {𝓕 𝓕' : JetSec E F} {x} (h : IsHolonomicAt 𝓕 x) (h' : 𝓕 =ᶠ[𝓝 x] 𝓕') :
    IsHolonomicAt 𝓕' x := by
  have h'' : 𝓕.f =ᶠ[𝓝 x] 𝓕'.f := by
    apply h'.mono
    simp_rw [eq_iff]
    tauto
  unfold JetSec.IsHolonomicAt
  rwa [h''.symm.fderiv_eq, ← (eq_iff.mp h'.self_of_nhds).2]

/-- A formal solution `𝓕` of `R` is partially holonomic in the direction of some subspace `E'`
if its linear map part at `x` is the derivative of its function part at `x` in restriction to
`E'`. -/
def IsPartHolonomicAt (𝓕 : JetSec E F) (E' : Submodule ℝ E) (x : E) :=
  ∀ v ∈ E', D 𝓕.f x v = 𝓕.φ x v

theorem _root_.Filter.Eventually.isPartHolonomicAt_congr {𝓕 𝓕' : JetSec E F} {s : Set E}
    (h : ∀ᶠ x near s, 𝓕 x = 𝓕' x) (E' : Submodule ℝ E) :
    ∀ᶠ x near s, 𝓕.IsPartHolonomicAt E' x ↔ 𝓕'.IsPartHolonomicAt E' x := by
  apply h.eventually_nhdsSet.mono
  intro x hx
  have hf : 𝓕.f =ᶠ[𝓝 x] 𝓕'.f := by
    apply hx.mono
    simp_rw [eq_iff]
    tauto
  unfold JetSec.IsPartHolonomicAt
  rw [hf.fderiv_eq, (eq_iff.mp hx.self_of_nhds).2]

theorem IsPartHolonomicAt.sup (𝓕 : JetSec E F) {E' E'' : Submodule ℝ E} {x : E}
    (h' : 𝓕.IsPartHolonomicAt E' x) (h'' : 𝓕.IsPartHolonomicAt E'' x) :
    𝓕.IsPartHolonomicAt (E' ⊔ E'') x := LinearMap.eqOn_sup h' h''

theorem isPartHolonomicAt_top {𝓕 : JetSec E F} {x : E} :
    IsPartHolonomicAt 𝓕 ⊤ x ↔ IsHolonomicAt 𝓕 x := by
  simp only [IsPartHolonomicAt, Submodule.mem_top, forall_true_left, IsHolonomicAt]
  simp only [← funext_iff, DFunLike.ext_iff]

@[simp]
theorem isPartHolonomicAt_bot (𝓕 : JetSec E F) : IsPartHolonomicAt 𝓕 ⊥ = fun _ ↦ True := by
  ext x
  simp only [IsPartHolonomicAt, Submodule.mem_bot, forall_eq, map_zero, eq_self_iff_true]

end JetSec

/-! ## Homotopies of sections -/

section HtpyJetSec

/-- A parametrized family of sections of J¹(E, F). -/
structure FamilyJetSec where
  f : P → E → F
  f_diff : 𝒞 ∞ ↿f
  φ : P → E → E →L[ℝ] F
  φ_diff : 𝒞 ∞ ↿φ

/-- A homotopy of sections of J¹(E, F). -/
@[reducible]
def HtpyJetSec :=
  FamilyJetSec E F ℝ

variable {E F P}

namespace FamilyJetSec

instance : FunLike (FamilyJetSec E F P) P (JetSec E F) where
  coe S t :=
    { f := S.f t
      f_diff := S.f_diff.comp (contDiff_const.prodMk contDiff_id)
      φ := S.φ t
      φ_diff := S.φ_diff.comp (contDiff_const.prodMk contDiff_id) }
  coe_injective' := by
    rintro ⟨⟩ ⟨⟩ h
    simp only [funext_iff, DFunLike.ext_iff, JetSec.mk_apply, Prod.ext_iff] at h
    congr <;> ext <;> simp [h]

@[simp] theorem mk_apply_apply (f : P → E → F) (f_diff φ φ_diff t x) :
    mk f f_diff φ φ_diff t x = (f t x, φ t x) :=
  rfl

@[simp] theorem mk_apply_f (f : P → E → F) (f_diff φ φ_diff t) :
    (mk f f_diff φ φ_diff t).f = f t :=
  rfl

@[simp] theorem mk_apply_φ (f : P → E → F) (f_diff φ φ_diff t) :
    (mk f f_diff φ φ_diff t).φ = φ t :=
  rfl

theorem contDiff_f (𝓕 : FamilyJetSec E F P) {n : ℕ∞} : 𝒞 n ↿𝓕.f :=
  𝓕.f_diff.of_le (by simp)

theorem contDiff_φ (𝓕 : FamilyJetSec E F P) {n : ℕ∞} : 𝒞 n ↿𝓕.φ :=
  𝓕.φ_diff.of_le (by simp)

end FamilyJetSec

/-- The constant homotopy of formal solutions at a given formal solution. It will be used
as junk value for constructions of formal homotopies that need additional assumptions and also
for trivial induction initialization. -/
def JetSec.constHtpy (𝓕 : JetSec E F) : HtpyJetSec E F where
  f _ := 𝓕.f
  f_diff := 𝓕.f_diff.snd'
  φ _ := 𝓕.φ
  φ_diff := 𝓕.φ_diff.snd'

@[simp]
theorem JetSec.constHtpy_apply (𝓕 : JetSec E F) : ∀ t, 𝓕.constHtpy t = 𝓕 := fun t ↦ by
  ext x <;> rfl

/-! ## Concatenation of homotopies of sections

In this part of the file we build a concatenation operation for homotopies of 1-jet sections.
We first need to introduce a smooth step function on `ℝ`. There is already a version
of this in mathlib called `smooth_transition` but that version is not locally constant
near `0` and `1`, which is not convenient enough for gluing purposes.
-/


/-- A smooth step function on `ℝ`. -/
def smoothStep : ℝ → ℝ := fun t ↦ smoothTransition (2 * t - 1 / 2)

theorem smoothStep.smooth : 𝒞 ∞ smoothStep :=
  smoothTransition.contDiff.comp <| (contDiff_id.const_smul (2 : ℝ)).sub contDiff_const

@[simp]
theorem smoothStep.zero : smoothStep 0 = 0 := by
  apply smoothTransition.zero_of_nonpos
  norm_num

@[simp]
theorem smoothStep.one : smoothStep 1 = 1 := by
  apply smoothTransition.one_of_one_le
  norm_num

theorem smoothStep.mem (t : ℝ) : smoothStep t ∈ I :=
  ⟨smoothTransition.nonneg _, smoothTransition.le_one _⟩

theorem smoothStep.abs_le (t : ℝ) : |smoothStep t| ≤ 1 :=
  _root_.abs_le.mpr ⟨by linarith [(smoothStep.mem t).1], by apply smoothTransition.le_one _⟩

theorem smoothStep.of_lt {t : ℝ} (h : t < 1 / 4) : smoothStep t = 0 := by
  apply smoothTransition.zero_of_nonpos
  linarith

-- unused
theorem smoothStep.pos_of_gt {t : ℝ} (h : 1 / 4 < t) : 0 < smoothStep t := by
  apply smoothTransition.pos_of_pos
  linarith

theorem smoothStep.of_gt {t : ℝ} (h : 3 / 4 < t) : smoothStep t = 1 := by
  apply smoothTransition.one_of_one_le
  linarith

theorem htpy_jet_sec_comp_aux {f g : ℝ → E → F} (hf : 𝒞 ∞ ↿f) (hg : 𝒞 ∞ ↿g) (hfg : f 1 = g 0) :
    𝒞 ∞ ↿(fun t x ↦ if t ≤ 1 / 2 then f (smoothStep <| 2 * t) x
      else g (smoothStep <| 2 * t - 1) x : ℝ → E → F) := by
  have s₁ : 𝒞 ∞ (fun p ↦ (smoothStep (2 * p.1), p.2) : ℝ × E → ℝ × E) :=
    (smoothStep.smooth.comp (contDiff_const.mul contDiff_id)).prodMap contDiff_id
  replace hf := hf.comp s₁
  have s₂ : 𝒞 ∞ (fun p ↦ (smoothStep <| 2 * p.1 - 1, p.2) : ℝ × E → ℝ × E) :=
    (smoothStep.smooth.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)).prodMap
      contDiff_id
  replace hg := hg.comp s₂
  rw [contDiff_iff_contDiffAt] at *
  rintro ⟨t₀, x₀⟩
  rcases lt_trichotomy t₀ (1 / 2) with (ht | rfl | ht)
  · apply (hf (t₀, x₀)).congr_of_eventuallyEq
    have : (Iio (1 / 2) : Set ℝ) ×ˢ univ ∈ 𝓝 (t₀, x₀) :=
      prod_mem_nhds_iff.mpr ⟨Iio_mem_nhds ht, univ_mem⟩
    filter_upwards [this] with p hp
    cases' p with t x
    replace hp : t < 1 / 2 := (prodMk_mem_set_prod_eq.mp hp).1
    change ite (t ≤ 1 / 2) (f (smoothStep (2 * t)) x) (g (smoothStep (2 * t - 1)) x) = _
    rw [if_pos hp.le]
    rfl
  · apply (hf (1 / 2, x₀)).congr_of_eventuallyEq
    have : (Ioo (3 / 8) (5 / 8) : Set ℝ) ×ˢ univ ∈ 𝓝 (1 / (2 : ℝ), x₀) := by
      refine prod_mem_nhds_iff.mpr ⟨Ioo_mem_nhds ?_ ?_, univ_mem⟩ <;> norm_num
    filter_upwards [this] with p hp
    cases' p with t x
    cases' (prodMk_mem_set_prod_eq.mp hp).1 with lt_t t_lt
    change ite (t ≤ 1 / 2) (f (smoothStep (2 * t)) x) (g (smoothStep (2 * t - 1)) x) = _
    split_ifs
    · rfl
    · change g _ x = f (smoothStep <| 2 * t) x
      apply congr_fun
      rw [show smoothStep (2 * t - 1) = 0 by apply smoothStep.of_lt; linarith,
        show smoothStep (2 * t) = 1 by apply smoothStep.of_gt; linarith, hfg]
  · apply (hg (t₀, x₀)).congr_of_eventuallyEq
    have : (Ioi (1 / 2) : Set ℝ) ×ˢ univ ∈ 𝓝 (t₀, x₀) :=
      prod_mem_nhds_iff.mpr ⟨Ioi_mem_nhds ht, univ_mem⟩
    filter_upwards [this] with p hp
    cases' p with t x
    replace hp : ¬t ≤ 1 / 2 := by push_neg; exact (prodMk_mem_set_prod_eq.mp hp).1
    change ite (t ≤ 1 / 2) (f (smoothStep (2 * t)) x) (g (smoothStep (2 * t - 1)) x) = _
    rw [if_neg hp]
    rfl

/-- Concatenation of homotopies of formal solution. The result depend on our choice of
a smooth step function in order to keep smoothness with respect to the time parameter. -/
def HtpyJetSec.comp (𝓕 𝓖 : HtpyJetSec E F) (h : 𝓕 1 = 𝓖 0) : HtpyJetSec E F where
  f t x := if t ≤ 1 / 2 then 𝓕.f (smoothStep <| 2 * t) x else 𝓖.f (smoothStep <| 2 * t - 1) x
  f_diff := htpy_jet_sec_comp_aux 𝓕.f_diff 𝓖.f_diff (show (𝓕 1).f = (𝓖 0).f by rw [h])
  φ t x := if t ≤ 1 / 2 then 𝓕.φ (smoothStep <| 2 * t) x else 𝓖.φ (smoothStep <| 2 * t - 1) x
  φ_diff := htpy_jet_sec_comp_aux 𝓕.φ_diff 𝓖.φ_diff (show (𝓕 1).φ = (𝓖 0).φ by rw [h])

@[simp]
theorem HtpyJetSec.comp_of_le (𝓕 𝓖 : HtpyJetSec E F) (h) {t : ℝ} (ht : t ≤ 1 / 2) :
    𝓕.comp 𝓖 h t = 𝓕 (smoothStep <| 2 * t) := by
  ext x : 2 <;> · dsimp [HtpyJetSec.comp]; exact if_pos ht

theorem HtpyJetSec.comp_le_0 (𝓕 𝓖 : HtpyJetSec E F) (h) :
    ∀ᶠ t near Iic 0, 𝓕.comp 𝓖 h t = 𝓕 0 := by
  have : Iio (1 / 8 : ℝ) ∈ 𝓝ˢ (Iic (0 : ℝ)) :=
    mem_nhdsSet_iff_forall.mpr fun (x : ℝ) (hx : x ≤ 0) ↦ Iio_mem_nhds <| by linarith
  apply mem_of_superset this
  rintro t (ht : t < 1 / 8)
  have ht' : t ≤ 1 / 2 := by linarith
  change 𝓕.comp 𝓖 h t = 𝓕 0
  rw [HtpyJetSec.comp_of_le _ _ h ht']
  have ht'' : 2 * t < 1 / 4 := by linarith
  rw [smoothStep.of_lt ht'']

-- unused
-- @[simp] can prove this
theorem HtpyJetSec.comp_0 (𝓕 𝓖 : HtpyJetSec E F) (h) : 𝓕.comp 𝓖 h 0 = 𝓕 0 :=
  (𝓕.comp_le_0 𝓖 h).self_of_nhdsSet 0 right_mem_Iic

@[simp]
theorem HtpyJetSec.comp_of_not_le (𝓕 𝓖 : HtpyJetSec E F) (h) {t : ℝ} (ht : ¬t ≤ 1 / 2) :
    𝓕.comp 𝓖 h t = 𝓖 (smoothStep <| 2 * t - 1) := by
  rw [one_div] at ht
  ext x : 2 <;> simp [comp, if_neg ht] <;> rfl

theorem HtpyJetSec.comp_ge_1 (𝓕 𝓖 : HtpyJetSec E F) (h) : ∀ᶠ t near Ici 1, 𝓕.comp 𝓖 h t = 𝓖 1 := by
  have : Ioi (7 / 8 : ℝ) ∈ 𝓝ˢ (Ici (1 : ℝ)) :=
    mem_nhdsSet_iff_forall.mpr fun (x : ℝ) (hx : 1 ≤ x) ↦ Ioi_mem_nhds <| by linarith
  apply mem_of_superset this
  rintro t (ht : 7 / 8 < t)
  have ht' : ¬t ≤ 1 / 2 := by linarith
  change 𝓕.comp 𝓖 h t = 𝓖 1
  rw [HtpyJetSec.comp_of_not_le _ _ h ht']
  have ht'' : 3 / 4 < 2 * t - 1 := by linarith
  rw [smoothStep.of_gt ht'']

@[simp]
theorem HtpyJetSec.comp_1 (𝓕 𝓖 : HtpyJetSec E F) (h) : 𝓕.comp 𝓖 h 1 = 𝓖 1 :=
  (𝓕.comp_ge_1 𝓖 h).self_of_nhdsSet 1 left_mem_Ici

end HtpyJetSec
