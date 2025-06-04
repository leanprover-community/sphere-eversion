import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import SphereEversion.Loops.Surrounding
import SphereEversion.Loops.DeltaMollifier
import SphereEversion.ToMathlib.ExistsOfConvex
import SphereEversion.ToMathlib.Analysis.ContDiff

/-!
# The reparametrization lemma

This file contains a proof of Gromov's parametric reparametrization lemma. It concerns the behaviour
of the average value of a loop `γ : S¹ → F` when the loop is reparametrized by precomposing with a
diffeomorphism `S¹ → S¹`.

Given a loop `γ : S¹ → F` for some real vector space `F`, one may integrate to obtain its average
`∫ x in 0..1, (γ x)` in `F`. Although this average depends on the loop's parametrization, it
satisfies a contraint that depends only on the image of the loop: the average is contained in the
convex hull of the image of `γ`. The non-parametric version of the reparametrization lemma says that
conversely, given any point `g` in the interior of the convex hull of the image of `γ`, one may find
a reparametrization of `γ` whose average is `g`.

The reparametrization lemma thus allows one to reduce the problem of constructing a loop whose
average is a given point, to the problem of constructing a loop subject to a condition that depends
only on its image.

In fact the reparametrization lemma holds parametrically. Given a smooth family of loops:
`γ : E × S¹ → F`, `(x, t) ↦ γₓ t`, together with a smooth function `g : E → F`, such that `g x` is
contained in the interior of the convex hull of the image of `γₓ` for all `x`, there exists a smooth
family of diffeomorphism `φ : E × S¹ → S¹`, `(x, t) ↦ φₓ t` such that the average of `γₓ ∘ φₓ` is
`g x` for all `x`.

The idea of the proof is simple: since `g x` is contained in the interior of the convex hull of
the image of `γₓ` one may find `t₀, t₁, ..., tₙ` and barycentric coordinates `w₀, w₁, ..., wₙ` such
that `g x = ∑ᵢ wᵢ • γₓ(tᵢ)`. If there were no smoothness requirement on `φₓ` one could define
it to be a step function which spends time `wᵢ` at each `tᵢ`. However because there is a smoothness
condition, one rounds off the corners of the would-be step function by using a "delta mollifier"
(an approximation to a Dirac delta function).

The above construction works locally in the neighbourhood of any `x` in `E` and one uses a partition
of unity to globalise all the local solutions into the required family: `φ : E × S¹ → S¹`.

The key ingredients are theories of calculus, convex hulls, barycentric coordinates,
existence of delta mollifiers, partitions of unity, and the inverse function theorem.
-/


noncomputable section

open Set Function MeasureTheory Module intervalIntegral Filter
open scoped Topology Manifold ContDiff

variable {E F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

set_option hygiene false
notation "ι" => Fin (finrank ℝ F + 1)
set_option hygiene true

section MetricSpace

variable [MetricSpace E] [FiniteDimensional ℝ F]

theorem Loop.tendsto_mollify_apply (γ : E → Loop F) (h : Continuous ↿γ) (x : E) (t : ℝ) :
    Tendsto (fun z : E × ℕ ↦ (γ z.1).mollify z.2 t) (𝓝 x ×ˢ atTop) (𝓝 (γ x t)) := by
  have hγ : ∀ x, Continuous (γ x) := fun x ↦ h.comp <| Continuous.prodMk_right _
  simp_rw [Loop.mollify_eq_convolution _ (hγ _)]
  rw [← add_zero (γ x t)]
  refine Tendsto.add ?_ ?_
  · rw [← one_smul ℝ (γ x t)]
    refine ((tendsto_natCast_div_add_atTop 1).comp tendsto_snd).smul ?_
    refine ContDiffBump.convolution_tendsto_right ?_ ?_ ?_ tendsto_const_nhds
    · simp_rw [bump]; norm_cast
      exact
        ((tendsto_add_atTop_iff_nat 2).2 (tendsto_const_div_atTop_nhds_zero_nat 1)).comp tendsto_snd
    · filter_upwards with x using (hγ _).aestronglyMeasurable
    · have := h.tendsto (x, t)
      rw [nhds_prod_eq] at this
      exact this.comp ((tendsto_fst.comp tendsto_fst).prodMk tendsto_snd)
  · have : Continuous fun z ↦ intervalIntegral (γ z) 0 1 volume :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (by apply h)
        continuous_const
    rw [← zero_smul ℝ (_ : F)]
    exact (tendsto_one_div_add_atTop_nhds_zero_nat.comp tendsto_snd).smul
      ((this.tendsto x).comp tendsto_fst)

end MetricSpace

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Given a smooth function `g : E → F` between normed vector spaces, a smooth surrounding family
is a smooth family of loops `E → loop F`, `x ↦ γₓ` such that `γₓ` surrounds `g x` for all `x`. -/
structure SmoothSurroundingFamily (g : E → F) where
  smooth_surrounded : 𝒞 ∞ g
  toFun : E → Loop F
  smooth : 𝒞 ∞ ↿toFun
  Surrounds : ∀ x, (toFun x).Surrounds <| g x

namespace SmoothSurroundingFamily

variable {g : E → F} (γ : SmoothSurroundingFamily g) (x y : E)

instance : CoeFun (SmoothSurroundingFamily g) fun _ ↦ E → Loop F :=
  ⟨toFun⟩

protected theorem continuous : Continuous (γ x) := by
  apply Continuous.uncurry_left x γ.smooth.continuous

/-- Given `γ : SmoothSurroundingFamily g` and `x : E`, `γ.surroundingParametersAt x` are the
`tᵢ : ℝ`, for `i = 0, 1, ..., dim F` such that `γ x tᵢ` surround `g x`. -/
def surroundingParametersAt : ι → ℝ :=
  Classical.choose (γ.Surrounds x)

/-- Given `γ : SmoothSurroundingFamily g` and `x : E`, `γ.surroundingPointsAt x` are the
points `γ x tᵢ` surrounding `g x` for parameters `tᵢ : ℝ`, `i = 0, 1, ..., dim F` (defined
by `γ.surroundingParametersAt x`). -/
def surroundingPointsAt : ι → F :=
  γ x ∘ γ.surroundingParametersAt x

/-- Given `γ : SmoothSurroundingFamily g` and `x : E`, `γ.surrounding_weights_at x` are the
barycentric coordinates of `g x` wrt to the points `γ x tᵢ`, for parameters `tᵢ : ℝ`,
`i = 0, 1, ..., dim F` (defined by `γ.surroundingParametersAt x`). -/
def surroundingWeightsAt : ι → ℝ :=
  Classical.choose (Classical.choose_spec (γ.Surrounds x))

theorem surroundPtsPointsWeightsAt :
    SurroundingPts (g x) (γ.surroundingPointsAt x) (γ.surroundingWeightsAt x) :=
  Classical.choose_spec _

/-- Note that we are mollifying the loop `γ y` at the surrounding parameters for `γ x`. -/
def approxSurroundingPointsAt (n : ℕ) (i : ι) : F :=
  (γ y).mollify n (γ.surroundingParametersAt x i)

variable [FiniteDimensional ℝ E] [CompleteSpace F] in
theorem approxSurroundingPointsAt_smooth (n : ℕ) :
    𝒞 ∞ fun y ↦ γ.approxSurroundingPointsAt x y n := by
  refine contDiff_pi.mpr fun i ↦ ?_
  suffices 𝒞 ∞ fun y ↦ ∫ s in (0 : ℝ)..1, deltaMollifier n (γ.surroundingParametersAt x i) s • γ y s
    by simpa [approxSurroundingPointsAt, Loop.mollify]
  apply contDiff_parametric_integral_of_contDiff
  exact ContDiff.smul deltaMollifier_smooth.snd' γ.smooth

variable [FiniteDimensional ℝ F]

/-- The key property from which it should be easy to construct `localCenteringDensity`,
`localCenteringDensityNhd` etc below. -/
theorem eventually_exists_surroundingPts_approxSurroundingPointsAt :
    ∀ᶠ z : E × ℕ in 𝓝 x ×ˢ atTop,
      ∃ w, SurroundingPts (g z.1) (γ.approxSurroundingPointsAt x z.1 z.2) w := by
  let a : ι → E × ℕ → F := fun i z ↦ γ.approxSurroundingPointsAt x z.1 z.2 i
  suffices ∀ i, Tendsto (a i) (𝓝 x ×ˢ atTop) (𝓝 (γ.surroundingPointsAt x i)) by
    have hg : Tendsto (fun z : E × ℕ ↦ g z.fst) (𝓝 x ×ˢ atTop) (𝓝 (g x)) :=
      Tendsto.comp γ.smooth_surrounded.continuous.continuousAt tendsto_fst
    exact eventually_surroundingPts_of_tendsto_of_tendsto' ⟨_, γ.surroundPtsPointsWeightsAt x⟩ this hg
  intro i
  let t := γ.surroundingParametersAt x i
  change Tendsto (fun z : E × ℕ ↦ (γ z.1).mollify z.2 t) (𝓝 x ×ˢ atTop) (𝓝 (γ x t))
  exact Loop.tendsto_mollify_apply γ γ.smooth.continuous x t

/-- This is an auxiliary definition to help construct `centeringDensity` below.

Given `x : E`, it represents a smooth probability distribution on the circle with the property that:
`∫ s in 0..1, γ.localCenteringDensity x y s • γ y s = g y`
for all `y` in a neighbourhood of `x` (see `localCenteringDensity_average` below). -/
def localCenteringDensity [DecidablePred (· ∈ affineBases ι ℝ F)] : E → ℝ → ℝ := fun y ↦ by
  choose n hn₁ _ using
    Filter.eventually_iff_exists_mem.mp
      (γ.eventually_exists_surroundingPts_approxSurroundingPointsAt x)
  choose u _u v hv _huv using mem_prod_iff.mp hn₁
  choose m _hmv using mem_atTop_sets.mp hv
  exact ∑ i, evalBarycentricCoords ι ℝ F (g y) (γ.approxSurroundingPointsAt x y m) i •
      deltaMollifier m (γ.surroundingParametersAt x i)

/-- This is an auxiliary definition to help construct `centeringDensity` below. -/
def localCenteringDensityMp : ℕ := by
  choose n hn₁ _hn₂ using
    Filter.eventually_iff_exists_mem.mp
      (γ.eventually_exists_surroundingPts_approxSurroundingPointsAt x)
  choose u _hu v hv _huv using mem_prod_iff.mp hn₁
  choose m _hmv using mem_atTop_sets.mp hv
  exact m

theorem localCenteringDensity_spec [DecidablePred (· ∈ affineBases ι ℝ F)] :
    γ.localCenteringDensity x y =
      ∑ i,
        evalBarycentricCoords ι ℝ F (g y)
            (γ.approxSurroundingPointsAt x y (γ.localCenteringDensityMp x)) i •
          deltaMollifier (γ.localCenteringDensityMp x) (γ.surroundingParametersAt x i) :=
  rfl

/-- This is an auxiliary definition to help construct `centeringDensity` below. -/
def localCenteringDensityNhd : Set E := by
  choose n hn₁ _hn₂ using
    Filter.eventually_iff_exists_mem.mp
      (γ.eventually_exists_surroundingPts_approxSurroundingPointsAt x)
  choose u _hu v _hv _huv using mem_prod_iff.mp hn₁
  exact interior u

theorem localCenteringDensityNhd_isOpen : IsOpen <| γ.localCenteringDensityNhd x :=
  isOpen_interior

theorem localCenteringDensityNhd_self_mem : x ∈ γ.localCenteringDensityNhd x := by
  let h :=
    Filter.eventually_iff_exists_mem.mp
      (γ.eventually_exists_surroundingPts_approxSurroundingPointsAt x)
  exact mem_interior_iff_mem_nhds.mpr
    (Classical.choose_spec <| mem_prod_iff.mp (Classical.choose_spec h).1).1

-- unused
theorem localCenteringDensityNhd_covers : univ ⊆ ⋃ x, γ.localCenteringDensityNhd x := fun x _ ↦
  mem_iUnion.mpr ⟨x, γ.localCenteringDensityNhd_self_mem x⟩

theorem approxSurroundingPointsAt_of_localCenteringDensityNhd
    (hy : y ∈ γ.localCenteringDensityNhd x) :
    ∃ w, SurroundingPts (g y) (γ.approxSurroundingPointsAt x y (γ.localCenteringDensityMp x)) w := by
  let h :=
    Filter.eventually_iff_exists_mem.mp
      (γ.eventually_exists_surroundingPts_approxSurroundingPointsAt x)
  let nn := Classical.choose h
  let hnn := mem_prod_iff.mp (Classical.choose_spec h).1
  let n := Classical.choose hnn
  let hn := Classical.choose_spec hnn
  change y ∈ interior n at hy
  let v := Classical.choose hn.2
  let hv : v ∈ atTop := (Classical.choose_spec hn.2).1
  let m := Classical.choose (mem_atTop_sets.mp hv)
  let hm := Classical.choose_spec (mem_atTop_sets.mp hv)
  change ∃ w, SurroundingPts (g y) (γ.approxSurroundingPointsAt x y m) w
  suffices (y, m) ∈ nn from (Classical.choose_spec h).2 _ this
  apply (Classical.choose_spec hn.2).2
  change y ∈ n ∧ m ∈ v
  exact ⟨interior_subset hy, hm _ (le_refl _)⟩

theorem approxSurroundingPointsAt_mem_affineBases (hy : y ∈ γ.localCenteringDensityNhd x) :
    γ.approxSurroundingPointsAt x y (γ.localCenteringDensityMp x) ∈ affineBases ι ℝ F :=
  (Classical.choose_spec
      (γ.approxSurroundingPointsAt_of_localCenteringDensityNhd x y hy)).mem_affineBases

variable [DecidablePred (· ∈ affineBases ι ℝ F)]

@[simp]
theorem localCenteringDensity_pos (hy : y ∈ γ.localCenteringDensityNhd x) (t : ℝ) :
    0 < γ.localCenteringDensity x y t := by
  simp only [γ.localCenteringDensity_spec x, Fintype.sum_apply, Pi.smul_apply,
    Algebra.id.smul_eq_mul]
  refine Finset.sum_pos (fun i _ ↦ mul_pos ?_ (deltaMollifier_pos _)) Finset.univ_nonempty
  obtain ⟨w, hw⟩ := γ.approxSurroundingPointsAt_of_localCenteringDensityNhd x y hy
  convert hw.w_pos i
  rw [← hw.coord_eq_w]
  simp [evalBarycentricCoords, γ.approxSurroundingPointsAt_mem_affineBases x y hy]

theorem localCenteringDensity_periodic : Periodic (γ.localCenteringDensity x y) 1 :=
  Finset.univ.periodic_sum fun _ _ ↦ Periodic.smul deltaMollifier_periodic _

variable [FiniteDimensional ℝ E] in
theorem localCenteringDensity_smooth_on :
    smooth_on ↿(γ.localCenteringDensity x) <| γ.localCenteringDensityNhd x ×ˢ (univ : Set ℝ) := by
  let h₀ (yt : E × ℝ) (_ : yt ∈ γ.localCenteringDensityNhd x ×ˢ (univ : Set ℝ)) :=
    congr_fun (γ.localCenteringDensity_spec x yt.fst) yt.snd
  refine ContDiffOn.congr ?_ h₀
  simp only [Fintype.sum_apply, Pi.smul_apply, Algebra.id.smul_eq_mul]
  refine ContDiffOn.sum fun i _ ↦ ContDiffOn.mul ?_ (ContDiff.contDiffOn ?_)
  · let w : F × (ι → F) → ℝ := fun z ↦ evalBarycentricCoords ι ℝ F z.1 z.2 i
    let z : E → F × (ι → F) :=
      (Prod.map g fun y ↦ γ.approxSurroundingPointsAt x y (γ.localCenteringDensityMp x)) ∘
        fun x ↦ (x, x)
    change ContDiffOn ℝ ∞ ((w ∘ z) ∘ Prod.fst) (γ.localCenteringDensityNhd x ×ˢ (univ : Set ℝ))
    rw [prod_univ]
    refine ContDiffOn.comp ?_ contDiff_fst.contDiffOn Subset.rfl
    have h₁ := smooth_barycentric ι ℝ F (Fintype.card_fin _) (n := ∞)
    have h₂ : 𝒞 ∞ (eval i : (ι → ℝ) → ℝ) := contDiff_apply _ _ i
    refine (h₂.comp_contDiffOn h₁).comp ?_ ?_
    · have h₃ := (diag_preimage_prod_self (γ.localCenteringDensityNhd x)).symm.subset
      refine ContDiffOn.comp ?_ (contDiff_id.prodMk contDiff_id).contDiffOn h₃
      refine γ.smooth_surrounded.contDiffOn.prodMap (ContDiff.contDiffOn ?_)
      exact γ.approxSurroundingPointsAt_smooth x _
    · intro y hy
      simp [z, γ.approxSurroundingPointsAt_mem_affineBases x y hy]
  · exact deltaMollifier_smooth.comp contDiff_snd

variable [FiniteDimensional ℝ E] in
theorem localCenteringDensity_continuous (hy : y ∈ γ.localCenteringDensityNhd x) :
    Continuous fun t ↦ γ.localCenteringDensity x y t := by
  refine continuous_iff_continuousAt.mpr fun t ↦ ?_
  have hyt : γ.localCenteringDensityNhd x ×ˢ univ ∈ 𝓝 (y, t) :=
    mem_nhds_prod_iff'.mpr
      ⟨γ.localCenteringDensityNhd x, univ, γ.localCenteringDensityNhd_isOpen x, hy,
        isOpen_univ, mem_univ t, rfl.subset⟩
  exact ((γ.localCenteringDensity_smooth_on x).continuousOn.continuousAt hyt).comp
    (Continuous.prodMk_right y).continuousAt

@[simp]
theorem localCenteringDensity_integral_eq_one (hy : y ∈ γ.localCenteringDensityNhd x) :
    ∫ s in (0 : ℝ)..1, γ.localCenteringDensity x y s = 1 := by
  let n := γ.localCenteringDensityMp x
  simp only [γ.localCenteringDensity_spec x, Prod.forall, exists_prop, gt_iff_lt,
    Fintype.sum_apply, Pi.smul_apply, Algebra.id.smul_eq_mul, Finset.sum_smul]
  rw [intervalIntegral.integral_finset_sum]
  · have h : γ.approxSurroundingPointsAt x y n ∈ affineBases ι ℝ F :=
      γ.approxSurroundingPointsAt_mem_affineBases x y hy
    simp_rw [← smul_eq_mul, intervalIntegral.integral_smul, deltaMollifier_integral_eq_one,
      Algebra.id.smul_eq_mul, mul_one]
    rw [evalBarycentricCoords_apply_of_mem_bases ι ℝ F (g y) h]
    simp_rw [AffineBasis.coords_apply, AffineBasis.sum_coord_apply_eq_one]
  · simp_rw [← smul_eq_mul]
    refine fun i hi ↦ (Continuous.const_smul ?_ _).intervalIntegrable 0 1
    exact deltaMollifier_smooth.continuous

@[simp]
theorem localCenteringDensity_average (hy : y ∈ γ.localCenteringDensityNhd x) :
    ∫ s in (0 : ℝ)..1, γ.localCenteringDensity x y s • γ y s = g y := by
  let n := γ.localCenteringDensityMp x
  simp only [γ.localCenteringDensity_spec x, Prod.forall, exists_prop, gt_iff_lt,
    Fintype.sum_apply, Pi.smul_apply, Algebra.id.smul_eq_mul, Finset.sum_smul]
  rw [intervalIntegral.integral_finset_sum]
  · simp_rw [mul_smul, intervalIntegral.integral_smul]
    change ∑ i, _ • γ.approxSurroundingPointsAt x y n i = _
    have h : γ.approxSurroundingPointsAt x y n ∈ affineBases ι ℝ F :=
      γ.approxSurroundingPointsAt_mem_affineBases x y hy
    erw [evalBarycentricCoords_apply_of_mem_bases ι ℝ F (g y) h]
    simp only [AffineBasis.coords_apply]
    exact AffineBasis.linear_combination_coord_eq_self ..
  · simp_rw [mul_smul]
    refine fun i hi ↦ ((Continuous.smul ?_ (γ.continuous y)).const_smul _).intervalIntegrable 0 1
    exact deltaMollifier_smooth.continuous

/-- Given `γ : SmoothSurroundingFamily g`, together with a point `x : E` and a map `f : ℝ → ℝ`,
`γ.is_centeringDensity x f` is the proposition that `f` is periodic, strictly positive, and
has integral one and that the average of `γₓ` with respect to the measure that `f` defines on
the circle is `g x`.

The continuity assumption is just a legacy convenience and should be dropped. -/
structure IsCenteringDensity (x : E) (f : ℝ → ℝ) : Prop where
  Pos : ∀ t, 0 < f t
  Periodic : Periodic f 1
  integral_one : ∫ s in (0 : ℝ)..1, f s = 1
  average : ∫ s in (0 : ℝ)..1, f s • γ x s = g x
  Continuous : Continuous f

omit [FiniteDimensional ℝ F] [DecidablePred fun x ↦ x ∈ affineBases ι ℝ F] in
-- Can drop if/when have `intervalIntegrable.smul_continuous_on`
theorem isCenteringDensity_convex (x : E) : Convex ℝ { f | γ.IsCenteringDensity x f } := by
  classical
  rintro f ⟨hf₁, hf₂, hf₃, hf₄, hf₅⟩ k ⟨hk₁, hk₂, hk₃, hk₄, hk₅⟩ a b ha hb hab
  have hf₆ : IntervalIntegrable f volume 0 1 := by
    apply intervalIntegrable_of_integral_ne_zero
    rw [hf₃]; exact one_ne_zero
  have hf₇ : IntervalIntegrable (f • (γ x : ℝ → F)) volume 0 1 :=
    (hf₅.smul (γ.continuous x)).intervalIntegrable 0 1
  have hk₆ : IntervalIntegrable k volume 0 1 := by
    apply intervalIntegrable_of_integral_ne_zero
    rw [hk₃]; exact one_ne_zero
  have hk₇ : IntervalIntegrable (k • (γ x : ℝ → F)) volume 0 1 :=
    (hk₅.smul (γ.continuous x)).intervalIntegrable 0 1
  exact {
    Pos := fun t ↦ convex_Ioi (0 : ℝ) (hf₁ t) (hk₁ t) ha hb hab
    Periodic := (hf₂.smul a).add (hk₂.smul b)
    integral_one := by
      simp_rw [Pi.add_apply]
      rw [intervalIntegral.integral_add (hf₆.smul a) (hk₆.smul b)]
      simp [intervalIntegral.integral_smul, hf₃, hk₃, hab]
    average := by
      simp_rw [Pi.add_apply, Pi.smul_apply, add_smul, smul_assoc]
      erw [intervalIntegral.integral_add (hf₇.smul a) (hk₇.smul b)]
      simp [intervalIntegral.integral_smul, ← add_smul, hf₄, hk₄, hab]
    Continuous := Continuous.add (hf₅.const_smul a) (hk₅.const_smul b) }

variable [FiniteDimensional ℝ E]

theorem exists_smooth_isCenteringDensity (x : E) :
    ∃ U ∈ 𝓝 x,
      ∃ f : E → ℝ → ℝ,
        smooth_on (uncurry f) (U ×ˢ (univ : Set ℝ)) ∧ ∀ y ∈ U, γ.IsCenteringDensity y (f y) :=
  ⟨γ.localCenteringDensityNhd x,
    mem_nhds_iff.mpr
      ⟨_, Subset.rfl, γ.localCenteringDensityNhd_isOpen x, γ.localCenteringDensityNhd_self_mem x⟩,
    γ.localCenteringDensity x, γ.localCenteringDensity_smooth_on x, fun y hy ↦
    ⟨γ.localCenteringDensity_pos x y hy, γ.localCenteringDensity_periodic x y,
      γ.localCenteringDensity_integral_eq_one x y hy, γ.localCenteringDensity_average x y hy,
      γ.localCenteringDensity_continuous x y hy⟩⟩

/-- This the key construction. It represents a smooth probability distribution on the circle with
the property that:
`∫ s in 0..1, γ.centeringDensity x s • γ x s = g x`
for all `x : E` (see `centeringDensity_average` below). -/
def centeringDensity : E → ℝ → ℝ :=
  Classical.choose
    (exists_contDiff_of_convex₂ γ.isCenteringDensity_convex γ.exists_smooth_isCenteringDensity)

theorem centeringDensity_smooth : 𝒞 ∞ <| uncurry fun x t ↦ γ.centeringDensity x t :=
  (Classical.choose_spec <|
      exists_contDiff_of_convex₂ γ.isCenteringDensity_convex γ.exists_smooth_isCenteringDensity).1

theorem isCenteringDensityCenteringDensity (x : E) :
    γ.IsCenteringDensity x (γ.centeringDensity x) :=
  (Classical.choose_spec <|
        exists_contDiff_of_convex₂ γ.isCenteringDensity_convex γ.exists_smooth_isCenteringDensity).2
    x

@[simp]
theorem centeringDensity_pos (t : ℝ) : 0 < γ.centeringDensity x t :=
  (γ.isCenteringDensityCenteringDensity x).Pos t

theorem centeringDensity_periodic : Periodic (γ.centeringDensity x) 1 :=
  (γ.isCenteringDensityCenteringDensity x).Periodic

@[simp]
theorem centeringDensity_integral_eq_one : ∫ s in (0)..1, γ.centeringDensity x s = 1 :=
  (γ.isCenteringDensityCenteringDensity x).integral_one

@[simp]
theorem centeringDensity_average : ∫ s in (0)..1, γ.centeringDensity x s • γ x s = g x :=
  (γ.isCenteringDensityCenteringDensity x).average

theorem centeringDensity_continuous : Continuous (γ.centeringDensity x) :=
  (γ.centeringDensity_smooth.continuous).uncurry_left x

theorem centeringDensity_intervalIntegrable (t₁ t₂ : ℝ) :
    IntervalIntegrable (γ.centeringDensity x) volume t₁ t₂ :=
  (γ.centeringDensity_continuous x).intervalIntegrable t₁ t₂

@[simp]
theorem integral_add_one_centeringDensity (t : ℝ) :
    ∫ s in (0)..t + 1, γ.centeringDensity x s = (∫ s in (0)..t, γ.centeringDensity x s) + 1 := by
  have h₁ := γ.centeringDensity_intervalIntegrable x 0 t
  have h₂ := γ.centeringDensity_intervalIntegrable x t (t + 1)
  simp [← integral_add_adjacent_intervals h₁ h₂,
    (γ.centeringDensity_periodic x).intervalIntegral_add_eq t 0]

theorem deriv_integral_centeringDensity_pos (t : ℝ) :
    0 < deriv (fun t ↦ ∫ s in (0)..t, γ.centeringDensity x s) t := by
  rw [intervalIntegral.deriv_integral_right (γ.centeringDensity_intervalIntegrable _ _ _)
      ((γ.centeringDensity_continuous x).stronglyMeasurableAtFilter volume (𝓝 t))
      (centeringDensity_continuous γ x).continuousAt]
  exact centeringDensity_pos γ x t

theorem strictMono_integral_centeringDensity :
    StrictMono fun t ↦ ∫ s in (0)..t, γ.centeringDensity x s :=
  strictMono_of_deriv_pos (γ.deriv_integral_centeringDensity_pos x)

theorem surjective_integral_centeringDensity :
    Surjective fun t ↦ ∫ s in (0)..t, γ.centeringDensity x s :=
  haveI : Continuous fun t ↦ ∫ s in (0)..t, γ.centeringDensity x s :=
    continuous_primitive (γ.centeringDensity_intervalIntegrable x) 0
  EquivariantMap.surjective
    ⟨fun t ↦ ∫ s in (0)..t, γ.centeringDensity x s, γ.integral_add_one_centeringDensity x⟩ this

/-- Given `γ : SmoothSurroundingFamily g`, `x ↦ γ.reparametrize x` is a smooth family of
diffeomorphisms of the circle such that reparametrizing `γₓ` by `γ.reparametrize x` gives a loop
with average `g x`.

This is the key construction and the main "output" of the reparametrization lemma. -/
def reparametrize : E → EquivariantEquiv := fun x ↦
  ({ toFun := fun t ↦ ∫ s in (0)..t, γ.centeringDensity x s
     invFun :=
       (StrictMono.orderIsoOfSurjective _ (γ.strictMono_integral_centeringDensity x)
           (γ.surjective_integral_centeringDensity x)).symm
     left_inv := StrictMono.orderIsoOfSurjective_symm_apply_self _ _ _
     right_inv := fun t ↦ StrictMono.orderIsoOfSurjective_self_symm_apply _
       (γ.strictMono_integral_centeringDensity x) _ t
     map_zero' := integral_same
     eqv' := γ.integral_add_one_centeringDensity x } : EquivariantEquiv).symm

theorem hasDerivAt_reparametrize_symm (s : ℝ) :
    HasDerivAt (γ.reparametrize x).symm (γ.centeringDensity x s) s :=
  integral_hasDerivAt_right (γ.centeringDensity_intervalIntegrable x 0 s)
    ((γ.centeringDensity_continuous x).stronglyMeasurableAtFilter _ _)
    (γ.centeringDensity_continuous x).continuousAt

-- 𝒞 ∞ ↿γ.reparametrize
theorem reparametrize_smooth : 𝒞 ∞ <| uncurry fun (x : E) (t : ℝ) ↦ γ.reparametrize x t := by
  let f : E → ℝ → ℝ := fun x t ↦ ∫ s in (0)..t, γ.centeringDensity x s
  change 𝒞 ∞ fun p : E × ℝ ↦ (StrictMono.orderIsoOfSurjective (f p.1) _ _).symm p.2
  apply contDiff_parametric_symm_of_deriv_pos
  · exact contDiff_parametric_primitive_of_contDiff'' γ.centeringDensity_smooth 0
  · exact fun x ↦ deriv_integral_centeringDensity_pos γ x
  · exact fun x ↦ surjective_integral_centeringDensity γ x

@[simp]
theorem reparametrize_average :
    ((γ x).reparam <| (γ.reparametrize x).equivariantMap).average = g x := by
  change ∫ s : ℝ in (0)..1, γ x (γ.reparametrize x s) = g x
  have h₁ :
    ∀ s, s ∈ uIcc 0 (1 : ℝ) → HasDerivAt (γ.reparametrize x).symm (γ.centeringDensity x s) s :=
    fun s _ ↦ γ.hasDerivAt_reparametrize_symm x s
  have h₂ : ContinuousOn (fun s ↦ γ.centeringDensity x s) (uIcc 0 1) :=
    (γ.centeringDensity_continuous x).continuousOn
  have h₃ : Continuous fun s ↦ γ x (γ.reparametrize x s) :=
    (γ.continuous x).comp (γ.reparametrize_smooth.continuous.uncurry_left x)
  rw [← (γ.reparametrize x).symm.map_zero, ← (γ.reparametrize x).symm.map_one, ←
    integral_comp_smul_deriv h₁ h₂ h₃]
  simp only [comp_apply, EquivariantEquiv.apply_symm_apply, centeringDensity_average]

end SmoothSurroundingFamily
