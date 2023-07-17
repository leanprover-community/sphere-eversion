import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.l2Space
import SphereEversion.ToMathlib.Analysis.Calculus.AffineMap
import SphereEversion.ToMathlib.Logic.Equiv.LocalEquiv

variable {F : Type _} [NormedAddCommGroup F] [NormedSpace ℝ F]

open Set Function Metric AffineMap

open scoped Classical

noncomputable section

namespace InnerProductSpace

variable {E : Type _} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Provided `0 < r`, this is a diffeomorphism from `E` onto the open ball of radius `r` in `E`
centred at a point `c` and sending `0` to `c`.

The values for `r ≤ 0` are junk.

TODO Refactor this: clearly it should really be built along the following lines:
```
variables (c : F) {r : ℝ} (hr : 0 < r)
include hr

def ball_homeomorph_ball : ball (0 : F) 1 ≃ₜ ball c r :=
{ to_fun := λ x, ⟨c +ᵥ homothety (0 : F) r (x : F), ...⟩,
  inv_fun := λ y, ⟨(homothety c r⁻¹ y) -ᵥ c, ...⟩,
  left_inv := ...,
  right_inv := ...,
  continuous_to_fun := ...,
  continuous_inv_fun := ..., }

-- Not quite the right type but nearly there:
#check (homeomorph_unit_ball.trans (ball_homeomorph_ball c hr)).to_local_homeomorph
```
 -/
def diffeomorphToNhd (c : E) (r : ℝ) : LocalHomeomorph E E :=
  if hr : 0 < r then
    { toFun := fun x => c +ᵥ homothety (0 : E) r (homeomorphUnitBall x)
      invFun :=
        (fun y => if hy : y ∈ ball (0 : E) 1 then homeomorphUnitBall.symm ⟨y, hy⟩ else 0) ∘ fun y =>
          homothety c r⁻¹ y -ᵥ c
      source := univ
      target := ball c r
      open_source := isOpen_univ
      open_target := isOpen_ball
      map_source' := fun x _ =>
        by
        have hx : ‖(homeomorphUnitBall x : E)‖ < 1 := by rw [← dist_zero_right];
          exact (homeomorphUnitBall x).property
        rw [← mul_lt_mul_left hr, mul_one] at hx 
        simp only [homothety_apply, vsub_eq_sub, sub_zero, vadd_eq_add, add_zero, mem_ball,
          dist_self_add_left, norm_smul, Real.norm_eq_abs, abs_eq_self.2 hr.le, hx]
      map_target' := fun x h => mem_univ _
      left_inv' := fun x => by
        simp [homothety_apply, norm_smul, abs_eq_self.mpr hr.le, ← mul_assoc, ← smul_assoc,
          hr.ne.symm.is_unit.inv_mul_cancel]
      right_inv' := fun y hy => by
        replace hy : r⁻¹ * ‖y - c‖ < 1
        · rw [← mul_lt_mul_left hr, ← mul_assoc, mul_inv_cancel hr.ne.symm, mul_one, one_mul]
          simpa [dist_eq_norm] using hy
        simp [homothety_apply, norm_smul, abs_eq_self.2 hr.le, ← smul_assoc,
          mul_inv_cancel hr.ne.symm, hy]
      continuous_toFun :=
        continuous_iff_continuousOn_univ.mp <|
          continuous_const.add <|
            (homothety_continuous 0 r).comp <|
              continuous_induced_dom.comp homeomorphUnitBall.continuous
      continuous_invFun :=
        by
        refine' ContinuousOn.comp _ (Continuous.continuousOn _) (mapsTo_homothety_ball c hr)
        · rw [continuousOn_iff_continuous_restrict]
          convert homeomorph_unit_ball.symm.continuous; ext; simp
        · simp only [homothety_apply, vsub_eq_sub, vadd_eq_add, add_sub_cancel]
          exact continuous_const.smul (continuous_id.sub continuous_const) }
  else LocalHomeomorph.refl E

@[simp]
theorem diffeomorphToNhd_source (c : E) (r : ℝ) : (diffeomorphToNhd c r).source = univ :=
  by
  by_cases hr : 0 < r
  · rw [diffeomorphToNhd, dif_pos hr]
  · rw [diffeomorphToNhd, dif_neg hr, LocalHomeomorph.refl_localEquiv, LocalEquiv.refl_source]

@[simp]
theorem diffeomorphToNhd_apply_zero (c : E) {r : ℝ} (hr : 0 < r) : diffeomorphToNhd c r 0 = c := by
  simp only [diffeomorphToNhd, dif_pos hr, vadd_eq_add, LocalHomeomorph.mk_coe, LocalEquiv.coe_mk,
    coe_homeomorphUnitBall_apply_zero, homothety_apply_same, add_zero]

@[simp]
theorem range_diffeomorphToNhd_eq_ball (c : E) {r : ℝ} (hr : 0 < r) :
    range (diffeomorphToNhd c r) = ball c r := by
  erw [LocalEquiv.range_eq_target_of_source_eq_univ _ (diffeomorphToNhd_source c r),
    diffeomorphToNhd, dif_pos hr]

@[simp]
theorem contDiff_diffeomorphToNhd (c : E) (r : ℝ) {n : ℕ∞} : ContDiff ℝ n <| diffeomorphToNhd c r :=
  by
  by_cases hr : 0 < r
  · rw [diffeomorphToNhd, dif_pos hr]
    exact cont_diff_const.add ((contDiff_homothety 0 r).comp contDiff_homeomorphUnitBall)
  · rw [diffeomorphToNhd, dif_neg hr]
    exact contDiff_id

@[simp]
theorem cont_diff_diffeomorphToNhd_inv (c : E) (r : ℝ) {n : ℕ∞} :
    ContDiffOn ℝ n (diffeomorphToNhd c r).symm (diffeomorphToNhd c r).target :=
  by
  by_cases hr : 0 < r
  · rw [diffeomorphToNhd, dif_pos hr]
    have aux : ball c r ⊆ (fun x : E => (fun y : E => homothety c r⁻¹ y -ᵥ c) x) ⁻¹' ball 0 1 :=
      mapsTo_homothety_ball c hr
    refine' ContDiffOn.comp _ (ContDiff.contDiffOn _) aux
    · exact contDiffOn_homeomorphUnitBall_symm fun y hy => dif_pos hy
    · simp only [homothety_apply, vsub_eq_sub, vadd_eq_add, add_sub_cancel]
      exact cont_diff_const.smul (cont_diff_id.sub contDiff_const)
  · rw [diffeomorphToNhd, dif_neg hr]
    exact contDiffOn_id

end InnerProductSpace

variable (F) [FiniteDimensional ℝ F]

/-- The Euclidean space obtained by choosing a basis of `F` and declaring it to be orthnormal.  -/
def L2 :=
  EuclideanSpace ℝ <| Basis.ofVectorSpaceIndex ℝ F

instance : NormedAddCommGroup (L2 F) :=
  PiLp.normedAddCommGroup 2 _

instance : InnerProductSpace ℝ (L2 F) :=
  PiLp.innerProductSpace _

/-- The continuous linear equivalence from `F` with its given norm to itself with the Euclidean
norm obtained from a choice of basis. -/
def selfEquivL2 : F ≃L[ℝ] L2 F :=
  LinearEquiv.toContinuousLinearEquiv
    ((Basis.ofVectorSpace ℝ F).equivFun.trans
      (EuclideanSpace.equiv (Basis.ofVectorSpaceIndex ℝ F) ℝ).symm.toLinearEquiv)

-- We shouldn't really need this lemma.
@[simp]
theorem selfEquivL2_image_univ : selfEquivL2 F '' univ = univ :=
  by
  rw [image_univ]
  exact (selfEquivL2 F : F ≃ L2 F).range_eq_univ

variable {F}

/-- A variant of `inner_product_space.diffeomorph_to_nhd` which provides a function satisfying the
weaker condition `range_diffeomorph_to_nhd_subset_ball` but which applies to any `normed_space`.

In fact one could demand this stronger property but it would be more work and we don't need it. -/
def diffeomorphToNhd (c : F) (r : ℝ) : LocalHomeomorph F F :=
  if hr : 0 < r then by
    let B := selfEquivL2 F '' ball c r
    let f := (selfEquivL2 F).toHomeomorph
    have hB : IsOpen B := f.is_open_map _ is_open_ball
    have hc : selfEquivL2 F c ∈ B := mem_image_of_mem f (mem_ball_self hr)
    let ε := Classical.choose (metric.is_open_iff.mp hB _ hc)
    exact
      (f.trans_local_homeomorph
            (InnerProductSpace.diffeomorphToNhd (selfEquivL2 F c) ε)).transHomeomorph
        f.symm
  else LocalHomeomorph.refl F

@[simp]
theorem diffeomorphToNhd_source (c : F) (r : ℝ) : (diffeomorphToNhd c r).source = univ :=
  by
  by_cases hr : 0 < r
  · simp [diffeomorphToNhd, dif_pos hr]
  · rw [diffeomorphToNhd, dif_neg hr, LocalHomeomorph.refl_localEquiv, LocalEquiv.refl_source]

@[simp]
theorem diffeomorphToNhd_apply_zero (c : F) {r : ℝ} (hr : 0 < r) : diffeomorphToNhd c r 0 = c :=
  by
  rw [diffeomorphToNhd, dif_pos hr]
  let B := selfEquivL2 F '' ball c r
  let f := (selfEquivL2 F).toHomeomorph
  have hB : IsOpen B := f.is_open_map _ is_open_ball
  have hc : selfEquivL2 F c ∈ B := mem_image_of_mem f (mem_ball_self hr)
  let ε := Classical.choose (metric.is_open_iff.mp hB _ hc)
  have hε : 0 < ε := Classical.choose (Classical.choose_spec (metric.is_open_iff.mp hB _ hc))
  change
    (f.trans_local_homeomorph
            (InnerProductSpace.diffeomorphToNhd (selfEquivL2 F c) ε)).transHomeomorph
        f.symm 0 =
      c
  simp [hε]

@[simp]
theorem range_diffeomorphToNhd_subset_ball (c : F) {r : ℝ} (hr : 0 < r) :
    range (diffeomorphToNhd c r) ⊆ ball c r :=
  by
  rw [diffeomorphToNhd, dif_pos hr, ← image_univ]
  let B := selfEquivL2 F '' ball c r
  let f := (selfEquivL2 F).toHomeomorph
  have hB : IsOpen B := f.is_open_map _ is_open_ball
  have hc : selfEquivL2 F c ∈ B := mem_image_of_mem f (mem_ball_self hr)
  let ε := Classical.choose (metric.is_open_iff.mp hB _ hc)
  have hε : 0 < ε := Classical.choose (Classical.choose_spec (metric.is_open_iff.mp hB _ hc))
  have hε' : ball (selfEquivL2 F c) ε ⊆ B :=
    Classical.choose_spec (Classical.choose_spec (metric.is_open_iff.mp hB _ hc))
  change f.symm ∘ InnerProductSpace.diffeomorphToNhd (selfEquivL2 F c) ε ∘ f '' univ ⊆ _
  rw [image_comp f.symm _, image_comp _ f]
  erw [selfEquivL2_image_univ, image_univ, InnerProductSpace.range_diffeomorphToNhd_eq_ball _ hε]
  suffices ball c r = f.symm '' (f '' ball c r) by rw [this]; exact monotone_image hε'
  rw [← image_comp]
  simp

@[simp]
theorem contDiff_diffeomorphToNhd (c : F) (r : ℝ) {n : ℕ∞} : ContDiff ℝ n <| diffeomorphToNhd c r :=
  by
  by_cases hr : 0 < r
  · rw [diffeomorphToNhd, dif_pos hr]
    exact
      (selfEquivL2 F).symm.contDiff.comp
        ((InnerProductSpace.contDiff_diffeomorphToNhd _ _).comp (selfEquivL2 F).contDiff)
  · rw [diffeomorphToNhd, dif_neg hr]
    exact contDiff_id

@[simp]
theorem cont_diff_diffeomorphToNhd_inv (c : F) (r : ℝ) {n : ℕ∞} :
    ContDiffOn ℝ n (diffeomorphToNhd c r).symm (diffeomorphToNhd c r).target :=
  by
  by_cases hr : 0 < r
  · rw [diffeomorphToNhd, dif_pos hr]
    refine' ContDiffOn.comp_continuousLinearMap _ (selfEquivL2 F : F →L[ℝ] L2 F)
    refine' (selfEquivL2 F).symm.contDiff.comp_contDiffOn _
    exact InnerProductSpace.cont_diff_diffeomorphToNhd_inv _ _
  · rw [diffeomorphToNhd, dif_neg hr]
    exact contDiffOn_id

