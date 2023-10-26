import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.UniformSpace.Separation
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import SphereEversion.Notations
import SphereEversion.Indexing
import SphereEversion.ToMathlib.Topology.Paracompact
import SphereEversion.ToMathlib.Topology.Algebra.Order.Compact
import SphereEversion.ToMathlib.Topology.NhdsSet
import SphereEversion.ToMathlib.Topology.Misc
import SphereEversion.ToMathlib.Geometry.Manifold.ChartedSpace
import SphereEversion.ToMathlib.Geometry.Manifold.SmoothManifoldWithCorners
import SphereEversion.ToMathlib.Analysis.NormedSpace.Misc

noncomputable section

open Set Equiv

open scoped Manifold Topology

section General

variable {𝕜 : Type _} [NontriviallyNormedField 𝕜] {E : Type _} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type _} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) (M : Type _)
  [TopologicalSpace M] [ChartedSpace H M] [SmoothManifoldWithCorners I M] {E' : Type _}
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type _} [TopologicalSpace H']
  (I' : ModelWithCorners 𝕜 E' H') (M' : Type _) [TopologicalSpace M'] [ChartedSpace H' M']
  [SmoothManifoldWithCorners I' M']

structure OpenSmoothEmbedding where
  toFun : M → M'
  invFun : M' → M
  left_inv' : ∀ {x}, invFun (toFun x) = x
  isOpen_range : IsOpen (range toFun)
  smooth_to : Smooth I I' toFun
  smooth_inv : SmoothOn I' I invFun (range toFun)

attribute [coe] OpenSmoothEmbedding.toFun

-- Note: this cannot be a `FunLike` instance since `toFun` is not injective in general.
instance : CoeFun (OpenSmoothEmbedding I M I' M') fun _ => M → M' :=
  ⟨OpenSmoothEmbedding.toFun⟩

namespace OpenSmoothEmbedding

variable {I I' M M'}

variable (f : OpenSmoothEmbedding I M I' M')

@[simp]
theorem coe_mk (f g h₁ h₂ h₃ h₄) : ⇑(⟨f, g, h₁, h₂, h₃, h₄⟩ : OpenSmoothEmbedding I M I' M') = f :=
  rfl

@[simp]
theorem left_inv (x : M) : f.invFun (f x) = x := by apply f.left_inv'

@[simp]
theorem invFun_comp_coe : f.invFun ∘ f = id :=
  funext f.left_inv

@[simp]
theorem right_inv {y : M'} (hy : y ∈ range f) : f (f.invFun y) = y := by
  obtain ⟨x, rfl⟩ := hy;
  rw [f.left_inv]

theorem smoothAt_inv {y : M'} (hy : y ∈ range f) : SmoothAt I' I f.invFun y :=
  (f.smooth_inv y hy).contMDiffAt <| f.isOpen_range.mem_nhds hy

theorem smoothAt_inv' {x : M} : SmoothAt I' I f.invFun (f x) :=
  f.smoothAt_inv <| mem_range_self x

theorem leftInverse : Function.LeftInverse f.invFun f :=
  left_inv f

theorem injective : Function.Injective f :=
  f.leftInverse.injective

protected theorem continuous : Continuous f :=
  f.smooth_to.continuous

theorem open_map : IsOpenMap f :=
  f.leftInverse.isOpenMap f.isOpen_range f.smooth_inv.continuousOn

theorem coe_comp_invFun_eventuallyEq (x : M) : f ∘ f.invFun =ᶠ[𝓝 (f x)] id :=
  Filter.eventually_of_mem (f.open_map.range_mem_nhds x) fun _ hy => f.right_inv hy

/- Note that we are slightly abusing the fact that `tangent_space I x` and
`tangent_space I (f.inv_fun (f x))` are both definitionally `E` below. -/
def fderiv (x : M) : TangentSpace I x ≃L[𝕜] TangentSpace I' (f x) :=
  have h₁ : MDifferentiableAt I' I f.invFun (f x) :=
    ((f.smooth_inv (f x) (mem_range_self x)).mdifferentiableWithinAt le_top).mdifferentiableAt
      (f.open_map.range_mem_nhds x)
  have h₂ : MDifferentiableAt I I' f x := f.smooth_to.contMDiff.mdifferentiable le_top _
  ContinuousLinearEquiv.equivOfInverse (mfderiv I I' f x) (mfderiv I' I f.invFun (f x))
    (by
      intro v
      erw [← ContinuousLinearMap.comp_apply, ← mfderiv_comp x h₁ h₂, f.invFun_comp_coe, mfderiv_id,
        ContinuousLinearMap.coe_id', id.def])
    (by
      intro v
      have hx : x = f.invFun (f x) := by rw [f.left_inv]
      have hx' : f (f.invFun (f x)) = f x := by rw [f.left_inv]
      rw [hx] at h₂
      erw [hx, hx', ← ContinuousLinearMap.comp_apply, ← mfderiv_comp (f x) h₂ h₁,
        ((hasMFDerivAt_id I' (f x)).congr_of_eventuallyEq
            (f.coe_comp_invFun_eventuallyEq x)).mfderiv,
        ContinuousLinearMap.coe_id', id.def])

@[simp]
theorem fderiv_coe (x : M) :
    (f.fderiv x : TangentSpace I x →L[𝕜] TangentSpace I' (f x)) = mfderiv I I' f x := by ext; rfl

@[simp]
theorem fderiv_symm_coe (x : M) :
    ((f.fderiv x).symm : TangentSpace I' (f x) →L[𝕜] TangentSpace I x) =
      mfderiv I' I f.invFun (f x) :=
  by ext; rfl

theorem fderiv_symm_coe' {x : M'} (hx : x ∈ range f) :
    ((f.fderiv (f.invFun x)).symm :
        TangentSpace I' (f (f.invFun x)) →L[𝕜] TangentSpace I (f.invFun x)) =
      (mfderiv I' I f.invFun x : TangentSpace I' x →L[𝕜] TangentSpace I (f.invFun x)) :=
  by rw [fderiv_symm_coe, f.right_inv hx]

open Filter

theorem openEmbedding : OpenEmbedding f :=
  openEmbedding_of_continuous_injective_open f.continuous f.injective f.open_map

theorem inducing : Inducing f :=
  f.openEmbedding.toInducing

theorem forall_near' {P : M → Prop} {A : Set M'} (h : ∀ᶠ m near f ⁻¹' A, P m) :
    ∀ᶠ m' near A ∩ range f, ∀ m, m' = f m → P m :=
  by
  rw [eventually_nhdsSet_iff] at h ⊢
  rintro _ ⟨hfm₀, m₀, rfl⟩
  have : ∀ U ∈ 𝓝 m₀, ∀ᶠ m' in 𝓝 (f m₀), m' ∈ f '' U :=
    by
    intro U U_in
    exact f.open_map.image_mem_nhds U_in
  apply (this _ <| h m₀ hfm₀).mono
  rintro _ ⟨m₀, hm₀, hm₀'⟩ m₁ rfl
  rwa [← f.injective hm₀']

theorem eventually_nhdsSet_mono {α : Type _} [TopologicalSpace α] {s t : Set α} {P : α → Prop}
    (h : ∀ᶠ x near t, P x) (h' : s ⊆ t) : ∀ᶠ x near s, P x :=
  h.filter_mono (nhdsSet_mono h')

-- TODO: optimize this proof which is probably more complicated than it needs to be
theorem forall_near [T2Space M'] {P : M → Prop} {P' : M' → Prop} {K : Set M} (hK : IsCompact K)
    {A : Set M'} (hP : ∀ᶠ m near f ⁻¹' A, P m) (hP' : ∀ᶠ m' near A, m' ∉ f '' K → P' m')
    (hPP' : ∀ m, P m → P' (f m)) : ∀ᶠ m' near A, P' m' :=
  by
  rw [show A = A ∩ range f ∪ A ∩ (range f)ᶜ by simp]
  apply Filter.Eventually.union
  · have : ∀ᶠ m' near A ∩ range f, m' ∈ range f :=
      f.isOpen_range.forall_near_mem_of_subset (inter_subset_right _ _)
    apply (this.and <| f.forall_near' hP).mono
    rintro _ ⟨⟨m, rfl⟩, hm⟩
    exact hPP' _ (hm _ rfl)
  · have op : IsOpen ((f '' K)ᶜ) := by
      rw [isOpen_compl_iff]
      exact (hK.image f.continuous).isClosed
    have : A ∩ (range f)ᶜ ⊆ A ∩ (f '' K)ᶜ :=
      inter_subset_inter_right _ (compl_subset_compl.mpr (image_subset_range f K))
    apply eventually_nhdsSet_mono _ this
    rw [eventually_nhdsSet_iff] at hP' ⊢
    rintro x ⟨hx, hx'⟩
    have hx' : ∀ᶠ y in 𝓝 x, y ∈ (f '' K)ᶜ := isOpen_iff_eventually.mp op x hx'
    apply ((hP' x hx).and hx').mono
    rintro y ⟨hy, hy'⟩
    exact hy hy'

variable (I M)

-- unused
/-- The identity map is a smooth open embedding. -/
@[simps]
nonrec def id : OpenSmoothEmbedding I M I M where
  toFun := id
  invFun := id
  left_inv' := rfl
  isOpen_range := IsOpenMap.id.isOpen_range
  smooth_to := smooth_id
  smooth_inv := smoothOn_id

variable {I M}

/- -- unused
@[simps!]
def comp {E'' : Type _} [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] {H'' : Type _}
    [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''} {M'' : Type _} [TopologicalSpace M'']
    [ChartedSpace H'' M''] [SmoothManifoldWithCorners I'' M'']
    (g : OpenSmoothEmbedding I' M' I'' M'') (f : OpenSmoothEmbedding I M I' M') :
    OpenSmoothEmbedding I M I'' M'' where
  toFun := g ∘ f
  invFun := f.invFun ∘ g.invFun
  left_inv' x := by simp only [Function.comp_apply, left_inv]
  isOpen_range := (g.open_map.comp f.open_map).isOpen_range
  smooth_to := g.smooth_to.comp f.smooth_to
  smooth_inv :=
    (f.smooth_inv.comp' g.smooth_inv).mono
      (by
        change range (g ∘ f) ⊆ range g ∩ g.inv_fun ⁻¹' range f
        refine' subset_inter_iff.mpr ⟨range_comp_subset_range f g, _⟩
        rintro x' ⟨x, rfl⟩
        exact ⟨x, by simp only [left_inv]⟩) -/

end OpenSmoothEmbedding

namespace ContinuousLinearEquiv

variable (e : E ≃L[𝕜] E') [CompleteSpace E] [CompleteSpace E']

-- unused
@[simps]
def toOpenSmoothEmbedding : OpenSmoothEmbedding 𝓘(𝕜, E) E 𝓘(𝕜, E') E'
    where
  toFun := e
  invFun := e.symm
  left_inv' {x} := e.symm_apply_apply x
  isOpen_range := e.isOpenMap.isOpen_range
  smooth_to := (e : E →L[𝕜] E').contMDiff
  smooth_inv := (e.symm : E' →L[𝕜] E).contMDiff.contMDiffOn

end ContinuousLinearEquiv

end General

section WithoutBoundary

open Metric hiding mem_nhds_iff

open Function

universe u

section GeneralNonsense

variable {𝕜 E H M : Type _} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M]
  [SmoothManifoldWithCorners I M] {x : M} {n : ℕ∞}

theorem extChartAt_target_eq_image_chart_target :
    (extChartAt I x).target = I '' (chartAt H x).target :=
  by
  erw [(chartAt H x).toLocalEquiv.trans_target'' I.toLocalEquiv, I.source_eq, univ_inter]
  rfl

@[simp]
theorem modelWithCornersSelf.extChartAt {e : E} : extChartAt 𝓘(𝕜, E) e = LocalEquiv.refl E := by
  simp

theorem contMDiffOn_ext_chart_symm :
    ContMDiffOn 𝓘(𝕜, E) I n (extChartAt I x).symm (extChartAt I x).target :=
  by
  have hs : (extChartAt I x).target ⊆ (chartAt E (extChartAt I x x)).source := by
    simp only [subset_univ, mfld_simps]
  have h2s : MapsTo (extChartAt I x).symm (extChartAt I x).target (chartAt H x).source := by
    rw [← extChartAt_source I]; exact (extChartAt I x).symm_mapsTo
  refine' (contMDiffOn_iff_of_subset_source hs h2s).mpr ⟨continuousOn_extChartAt_symm I x, _⟩
  simp_rw [modelWithCornersSelf.extChartAt, LocalEquiv.refl_symm, LocalEquiv.refl_coe,
    comp.right_id, id.def, image_id']
  exact (contDiffOn_congr fun y hy => (extChartAt I x).right_inv hy).mpr contDiffOn_id

end GeneralNonsense

variable {F H : Type _} (M : Type u) [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [LocallyCompactSpace M] [SigmaCompactSpace M]
  (IF : ModelWithCorners ℝ F H) [SmoothManifoldWithCorners IF M]

/- Clearly should be generalised. Maybe what we really want is a theory of local diffeomorphisms.

Note that the input `f` is morally an `open_smooth_embedding` but stated in terms of `cont_diff`
instead of `cont_mdiff`. This is more convenient for our purposes. -/
def openSmoothEmbOfDiffeoSubsetChartTarget (x : M) {f : LocalHomeomorph F F} (hf₁ : f.source = univ)
    (hf₂ : ContDiff ℝ ∞ f) (hf₃ : ContDiffOn ℝ ∞ f.symm f.target)
    (hf₄ : range f ⊆ IF '' (chartAt H x).target) : OpenSmoothEmbedding 𝓘(ℝ, F) F IF M
    where
  toFun := (extChartAt IF x).symm ∘ f
  invFun := f.invFun ∘ extChartAt IF x
  left_inv' {y} := by
    obtain ⟨z, hz, hz'⟩ := hf₄ (mem_range_self y)
    have aux : f.symm (IF z) = y := by rw [hz']; exact f.left_inv (hf₁.symm ▸ mem_univ _)
    simp only [← hz', (chartAt H x).right_inv hz, aux, extChartAt, LocalHomeomorph.extend,
      LocalEquiv.coe_trans, LocalHomeomorph.invFun_eq_coe, ModelWithCorners.toLocalEquiv_coe,
      LocalHomeomorph.coe_coe, LocalEquiv.coe_trans_symm, LocalHomeomorph.coe_coe_symm,
      ModelWithCorners.left_inv, ModelWithCorners.toLocalEquiv_coe_symm, Function.comp_apply, aux]
  isOpen_range :=
    IsOpenMap.isOpen_range fun u hu =>
      by
      have aux : IsOpen (f '' u) := f.image_open_of_open hu (hf₁.symm ▸ subset_univ u)
      convert isOpen_extChartAt_preimage' IF x aux
      rw [image_comp]
      refine'
        (extChartAt IF x).symm_image_eq_source_inter_preimage ((image_subset_range f u).trans _)
      rw [extChartAt_target_eq_image_chart_target]
      exact hf₄
  smooth_to :=
    by
    refine' contMDiffOn_ext_chart_symm.comp_contMDiff hf₂.contMDiff fun y => _
    rw [extChartAt_target_eq_image_chart_target]
    exact hf₄ (mem_range_self y)
  smooth_inv := by
    rw [← extChartAt_target_eq_image_chart_target] at hf₄
    have hf' : range ((extChartAt IF x).symm ∘ f) ⊆ extChartAt IF x ⁻¹' f.target :=
      by
      rw [range_comp, ← image_subset_iff, ← f.image_source_eq_target, hf₁, image_univ]
      exact (LocalEquiv.image_symm_image_of_subset_target _ hf₄).subset
    have hf'' : range ((extChartAt IF x).symm ∘ f) ⊆ (chartAt H x).source :=
      by
      rw [← extChartAt_source IF, range_comp, ← LocalEquiv.symm_image_target_eq_source]
      exact (monotone_image hf₄).trans Subset.rfl
    exact hf₃.contMDiffOn.comp (contMDiffOn_extChartAt.mono hf'') hf'

@[simp]
theorem coe_openSmoothEmbOfDiffeoSubsetChartTarget (x : M) {f : LocalHomeomorph F F}
    (hf₁ : f.source = univ) (hf₂ : ContDiff ℝ ∞ f) (hf₃ : ContDiffOn ℝ ∞ f.symm f.target)
    (hf₄ : range f ⊆ IF '' (chartAt H x).target) :
    (openSmoothEmbOfDiffeoSubsetChartTarget M IF x hf₁ hf₂ hf₃ hf₄ : F → M) =
      (extChartAt IF x).symm ∘ f :=
  by simp [openSmoothEmbOfDiffeoSubsetChartTarget]

theorem range_openSmoothEmbOfDiffeoSubsetChartTarget (x : M) {f : LocalHomeomorph F F}
    (hf₁ : f.source = univ) (hf₂ : ContDiff ℝ ∞ f) (hf₃ : ContDiffOn ℝ ∞ f.symm f.target)
    (hf₄ : range f ⊆ IF '' (chartAt H x).target) :
    range (openSmoothEmbOfDiffeoSubsetChartTarget M IF x hf₁ hf₂ hf₃ hf₄) =
      (extChartAt IF x).symm '' range f :=
  by rw [coe_openSmoothEmbOfDiffeoSubsetChartTarget, range_comp]

variable {M} (F)
variable [ModelWithCorners.Boundaryless IF] [FiniteDimensional ℝ F]

theorem nice_atlas' {ι : Type _} {s : ι → Set M} (s_op : ∀ j, IsOpen <| s j)
    (cov : (⋃ j, s j) = univ) (U : Set F) (hU₁ : (0 : F) ∈ U) (hU₂ : IsOpen U) :
    ∃ (ι' : Type u) (t : Set ι') (φ : t → OpenSmoothEmbedding 𝓘(ℝ, F) F IF M),
      t.Countable ∧
        (∀ i, ∃ j, range (φ i) ⊆ s j) ∧
          (LocallyFinite fun i => range (φ i)) ∧ (⋃ i, φ i '' U) = univ :=
  by
  set W : M → ℝ → Set M := fun x r =>
    (extChartAt IF x).symm ∘ diffeomorphToNhd (extChartAt IF x x) r '' U with W_def
  let B : M → ℝ → Set M := ChartedSpace.ball IF
  let p : M → ℝ → Prop := fun x r =>
    0 < r ∧ ball (extChartAt IF x x) r ⊆ (extChartAt IF x).target ∧ ∃ j, B x r ⊆ s j
  have hW₀ : ∀ x r, p x r → x ∈ W x r := fun x r h => ⟨0, hU₁, by simp [h.1]⟩
  have hW₁ : ∀ x r, p x r → IsOpen (W x r) :=
    by
    rintro x r ⟨h₁, h₂, -, -⟩
    simp only [W_def]
    rw [image_comp]
    let V := diffeomorphToNhd (extChartAt IF x x) r '' U
    change IsOpen ((extChartAt IF x).symm '' V)
    have hV₁ : IsOpen V :=
      ((diffeomorphToNhd (extChartAt IF x x) r).isOpen_image_iff_of_subset_source (by simp)).mp hU₂
    have hV₂ : V ⊆ (extChartAt IF x).target :=
      Subset.trans ((image_subset_range _ _).trans (by simp [h₁])) h₂
    rw [(extChartAt IF x).symm_image_eq_source_inter_preimage hV₂]
    exact isOpen_extChartAt_preimage' IF x hV₁
  have hB : ∀ x, (𝓝 x).HasBasis (p x) (B x) := fun x =>
    ChartedSpace.nhds_hasBasis_balls_of_open_cov IF x s_op cov
  obtain ⟨t, ht₁, ht₂, ht₃, ht₄⟩ := exists_countable_locallyFinite_cover surjective_id hW₀ hW₁ hB
  let g : M × ℝ → LocalHomeomorph F F := fun z => diffeomorphToNhd (extChartAt IF z.1 z.1) z.2
  have hg₁ : ∀ z, (g z).source = univ := by simp
  have hg₂ : ∀ z, ContDiff ℝ ∞ (g z) := by simp
  have hg₃ : ∀ z, ContDiffOn ℝ ∞ (g z).symm (g z).target := by simp
  refine'
    ⟨M × ℝ, t, fun z =>
      openSmoothEmbOfDiffeoSubsetChartTarget M IF z.1.1 (hg₁ z.1) (hg₂ z.1) (hg₃ z.1) _, ht₁,
      fun z => _, _, _⟩
  · obtain ⟨⟨x, r⟩, hxr⟩ := z
    obtain ⟨hr : 0 < r, hr' : ball (extChartAt IF x x) r ⊆ _, -⟩ := ht₂ _ hxr
    rw [← extChartAt_target_eq_image_chart_target]
    exact (range_diffeomorphToNhd_subset_ball (extChartAt IF x x) hr).trans hr'
  · obtain ⟨⟨x, r⟩, hxr⟩ := z
    obtain ⟨hr : 0 < r, -, j, hj : B x r ⊆ s j⟩ := ht₂ _ hxr
    simp_rw [range_openSmoothEmbOfDiffeoSubsetChartTarget]
    exact ⟨j, (monotone_image (range_diffeomorphToNhd_subset_ball _ hr)).trans hj⟩
  · simp_rw [range_openSmoothEmbOfDiffeoSubsetChartTarget]
    refine' ht₄.subset _
    rintro ⟨⟨x, r⟩, hxr⟩
    obtain ⟨hr : 0 < r, -, -⟩ := ht₂ _ hxr
    exact monotone_image (range_diffeomorphToNhd_subset_ball _ hr)
  · simpa only [iUnion_coe_set] using ht₃

variable [Nonempty M]

theorem nice_atlas {ι : Type _} {s : ι → Set M} (s_op : ∀ j, IsOpen <| s j)
    (cov : (⋃ j, s j) = univ) :
    ∃ n,
      ∃ φ : IndexType n → OpenSmoothEmbedding 𝓘(ℝ, F) F IF M,
        (∀ i, ∃ j, range (φ i) ⊆ s j) ∧
          (LocallyFinite fun i => range (φ i)) ∧ (⋃ i, φ i '' ball 0 1) = univ :=
  by
  obtain ⟨ι', t, φ, h₁, h₂, h₃, h₄⟩ := nice_atlas' F IF s_op cov (ball 0 1) (by simp) isOpen_ball
  have htne : t.Nonempty := by
    by_contra contra
    simp only [iUnion_coe_set, not_nonempty_iff_eq_empty.mp contra, mem_empty_iff_false,
      iUnion_of_empty, iUnion_empty, @eq_comm _ _ univ, univ_eq_empty_iff] at h₄
    exact not_isEmpty_of_nonempty M h₄
  obtain ⟨n, ⟨fn⟩⟩ := (Set.countable_iff_exists_nonempty_indexType_equiv htne).mp h₁
  refine' ⟨n, φ ∘ fn, fun i => h₂ (fn i), h₃.comp_injective fn.injective, _⟩
  erw [fn.surjective.iUnion_comp fun i => φ i '' ball 0 1, h₄]

end WithoutBoundary

namespace OpenSmoothEmbedding

section Updating

variable {𝕜 EX EM EY EN EM' X M Y N M' : Type _} [NontriviallyNormedField 𝕜] [NormedAddCommGroup EX]
  [NormedSpace 𝕜 EX] [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] [NormedAddCommGroup EM']
  [NormedSpace 𝕜 EM'] [NormedAddCommGroup EY] [NormedSpace 𝕜 EY] [NormedAddCommGroup EN]
  [NormedSpace 𝕜 EN] {HX : Type _} [TopologicalSpace HX] {IX : ModelWithCorners 𝕜 EX HX}
  {HY : Type _} [TopologicalSpace HY] {IY : ModelWithCorners 𝕜 EY HY} {HM : Type _}
  [TopologicalSpace HM] {IM : ModelWithCorners 𝕜 EM HM} {HM' : Type _} [TopologicalSpace HM']
  {IM' : ModelWithCorners 𝕜 EM' HM'} {HN : Type _} [TopologicalSpace HN]
  {IN : ModelWithCorners 𝕜 EN HN} [TopologicalSpace X] [ChartedSpace HX X]
  [SmoothManifoldWithCorners IX X] [TopologicalSpace M] [ChartedSpace HM M]
  [SmoothManifoldWithCorners IM M] [TopologicalSpace M'] [ChartedSpace HM' M']

section NonMetric

variable [TopologicalSpace Y] [ChartedSpace HY Y] [SmoothManifoldWithCorners IY Y]
  [TopologicalSpace N] [ChartedSpace HN N] [SmoothManifoldWithCorners IN N]
  (φ : OpenSmoothEmbedding IX X IM M) (ψ : OpenSmoothEmbedding IY Y IN N) (f : M → N) (g : X → Y)

section

attribute [local instance] Classical.dec

/-- This is definition `def:update` in the blueprint. -/
def update (m : M) : N :=
  if m ∈ range φ then ψ (g (φ.invFun m)) else f m

end

@[simp]
theorem update_of_nmem_range {m : M} (hm : m ∉ range φ) : update φ ψ f g m = f m := if_neg hm

@[simp]
theorem update_of_mem_range {m : M} (hm : m ∈ range φ) : update φ ψ f g m = ψ (g (φ.invFun m)) :=
  if_pos hm

@[simp]
theorem update_apply_embedding (x : X) : update φ ψ f g (φ x) = ψ (g x) := by simp [update]

-- This small auxiliary result is used in the next two lemmas.
theorem nice_update_of_eq_outside_compact_aux {K : Set X} (g : X → Y)
    (hg : ∀ x : X, x ∉ K → f (φ x) = ψ (g x)) {m : M} (hm : m ∉ φ '' K) : φ.update ψ f g m = f m :=
  by
  by_cases hm' : m ∈ range φ
  · obtain ⟨x, rfl⟩ := hm'
    replace hm : x ∉ K; · contrapose! hm; exact mem_image_of_mem φ hm
    simp [hg x hm]
  · exact if_neg hm'

open Function

/-- This is lemma `lem:smooth_updating` in the blueprint. -/
theorem smooth_update (f : M' → M → N) (g : M' → X → Y) {k : M' → M} {K : Set X}
    (hK : IsClosed (φ '' K)) (hf : Smooth (IM'.prod IM) IN (uncurry f))
    (hg : Smooth (IM'.prod IX) IY (uncurry g)) (hk : Smooth IM' IM k)
    (hg' : ∀ y x, x ∉ K → f y (φ x) = ψ (g y x)) :
    Smooth IM' IN fun x => update φ ψ (f x) (g x) (k x) :=
  by
  have hK' : ∀ x, k x ∉ φ '' K → update φ ψ (f x) (g x) (k x) = f x (k x) := fun x hx =>
    nice_update_of_eq_outside_compact_aux φ ψ (f x) (g x) (hg' x) hx
  refine' contMDiff_of_locally_contMDiffOn fun x => _
  let U := range φ
  let V := (φ '' K)ᶜ
  have h₂ : IsOpen (k ⁻¹' V) := hK.isOpen_compl.preimage hk.continuous
  have h₃ : V ∪ U = univ := by
    rw [← compl_subset_iff_union, compl_compl]
    exact image_subset_range φ K
  have h₄ : ∀ x, k x ∈ U → update φ ψ (f x) (g x) (k x) = (ψ ∘ g x ∘ φ.invFun) (k x) := fun m hm =>
    by intros ; exact if_pos hm
  by_cases hx : k x ∈ U
  ·
    refine'
      ⟨k ⁻¹' U, φ.isOpen_range.preimage hk.continuous, hx,
        (contMDiffOn_congr h₄).mpr <|
          ψ.smooth_to.comp_contMDiffOn <|
            hg.comp_contMDiffOn
              (smoothOn_id.prod_mk <| φ.smooth_inv.comp hk.smoothOn Subset.rfl)⟩
  · refine'
      ⟨k ⁻¹' V, h₂, _, (contMDiffOn_congr hK').mpr (hf.comp (smooth_id.prod_mk hk)).contMDiffOn⟩
    exact ((Set.ext_iff.mp h₃ (k x)).mpr trivial).resolve_right hx

end NonMetric

section Metric

variable [MetricSpace Y] [ChartedSpace HY Y] [SmoothManifoldWithCorners IY Y] [MetricSpace N]
  [ChartedSpace HN N] [SmoothManifoldWithCorners IN N] (φ : OpenSmoothEmbedding IX X IM M)
  (ψ : OpenSmoothEmbedding IY Y IN N) (f : M → N) (g : X → Y)

/-- This is `lem:dist_updating` in the blueprint. -/
theorem dist_update [ProperSpace Y] {K : Set X} (hK : IsCompact K) {P : Type _} [MetricSpace P]
    {KP : Set P} (hKP : IsCompact KP) (f : P → M → N) (hf : Continuous ↿f)
    (hf' : ∀ p, f p '' range φ ⊆ range ψ) {ε : M → ℝ} (hε : ∀ m, 0 < ε m) (hε' : Continuous ε) :
    ∃ η > (0 : ℝ),
      ∀ g : P → X → Y,
        ∀ p ∈ KP,
          ∀ p' ∈ KP,
            ∀ x ∈ K,
              dist (g p' x) (ψ.invFun (f p (φ x))) < η →
                dist (update φ ψ (f p') (g p') <| φ x) (f p <| φ x) < ε (φ x) :=
  by
  let F : P × X → Y := fun q => (ψ.invFun ∘ f q.1 ∘ φ) q.2
  let K₁ := Metric.cthickening 1 (F '' KP.prod K)
  have hK₁ : IsCompact K₁ :=
    by
    refine'
      Metric.isCompact_of_isClosed_isBounded Metric.isClosed_cthickening
        (Bornology.IsBounded.cthickening <| IsCompact.isBounded <| _)
    apply (hKP.prod hK).image
    exact
      ψ.smooth_inv.continuousOn.comp_continuous
        (hf.comp <| continuous_fst.prod_mk <| φ.continuous.comp continuous_snd) fun q =>
        hf' q.1 ⟨φ q.2, mem_range_self _, rfl⟩
  have h₁ : UniformContinuousOn ψ K₁ :=
    hK₁.uniformContinuousOn_of_continuous ψ.continuous.continuousOn
  have hεφ : ∀ x ∈ K, 0 < (ε ∘ φ) x := fun x _hx => hε _
  obtain ⟨ε₀, hε₀, hε₀'⟩ := hK.exists_forall_le' (hε'.comp φ.continuous).continuousOn hεφ
  obtain ⟨τ, hτ : 0 < τ, hτ'⟩ := Metric.uniformContinuousOn_iff.mp h₁ ε₀ hε₀
  refine' ⟨min τ 1, by simp [hτ], fun g p hp p' _hp' x hx hη => _⟩
  cases' lt_min_iff.mp hη with H H'
  specialize hεφ x hx
  apply lt_of_lt_of_le _ (hε₀' x hx); clear hε₀'
  simp only [update_apply_embedding]
  have h₁ : g p' x ∈ K₁ :=
    Metric.mem_cthickening_of_dist_le (g p' x) (F (p, x)) 1 _ ⟨(p, x), ⟨hp, hx⟩, rfl⟩ H'.le
  have h₂ : f p (φ x) ∈ range ψ := hf' p ⟨φ x, mem_range_self _, rfl⟩
  rw [← ψ.right_inv h₂]
  exact hτ' _ h₁ _ (Metric.self_subset_cthickening _ ⟨(p, x), ⟨hp, hx⟩, rfl⟩) H

end Metric

end Updating

end OpenSmoothEmbedding
