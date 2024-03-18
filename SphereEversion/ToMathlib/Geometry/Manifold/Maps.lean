/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Topology.ProperMap

/-! ## Smooth immersions and embeddings

In this file, we define immersions and smooth embeddings and prove some of their basic properties.

## Main definitions
* `Immersion I I' f n`: a `C^n` map `f : M → M'` is an immersion iff
its `mfderiv` is injective at each point
* `InjImmersion`: an immersion which is also injective
* `OpenSmoothEmbedding`, `SmoothEmbedding`: (open) smooth embeddings

## Main results
* `SmoothEmbedding.toInjImmersion`: smooth embeddings are injective immersions
* `Embedding.of_proper_injective_immersion`: proper injective immersions are smooth embeddings

## Implementation notes
The initial design of immersions only assumed injectivity of the differential.
This is not sufficient to ensure immersions are `C^n`:
While mathlib's `mfderiv` has junk value zero when `f` is not differentiable and the zero map is
only injective if `M` has dimension zero (in which case `f` is always `C^n`), this argument only
shows immersions are `MDifferentiable`, not `C^n`.

**NOTE.** This is **not** the correct definition in the infinite-dimensional context,
but in finite dimensions, the general definition is equivalent to the one in this file.

## Tags
manifold, immersion

-/
noncomputable section

open Set Function

open scoped Manifold

-- Let `M` be a manifold with corners over the pair `(E, H)`.
-- Let `M'` be a manifold with corners over the pair `(E', H')`.
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [instE: NormedAddCommGroup E] [instE': NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [SmoothManifoldWithCorners I M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] (I' : ModelWithCorners 𝕜 E' H')
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  [SmoothManifoldWithCorners I' M']

section Definition

/-- A `C^n` immersion `f : M → M` is a `C^n` map whose differential is injective at every point. -/
structure Immersion (f : M → M') (n : ℕ∞) : Prop :=
  contMDiff : ContMDiff I I' n f
  diff_injective : ∀ p, Injective (mfderiv I I' f p)

instance {f : M → M'} {n : ℕ∞} : FunLike (Immersion I I' f n) M M' where
  coe := fun _ ↦ f
  coe_injective' := by
    intro h _ _
    congr

/-- An injective `C^n` immersion -/
structure InjImmersion (f : M → M') (n : ℕ∞) extends Immersion I I' f n : Prop :=
  injective : Injective f

attribute [coe] InjImmersion.toImmersion
/-- Coerce injective immersions to immersions. -/
instance coe {f : M → M'} {n : ℕ∞} : Coe (InjImmersion I I' f n) (Immersion I I' f n) :=
  ⟨InjImmersion.toImmersion⟩

theorem coe_injective {f : M → M'} {n : ℕ∞} : Function.Injective ((↑) : (InjImmersion I I' f n) → (Immersion I I' f n)) := by
  intro h h' _
  congr

-- this errors; is this instance useful?
-- instance {f : M → M'} {n : ℕ∞} : FunLike (InjImmersion I I' f n) M M' where
--   coe := fun _ ↦ f
--   coe_injective' := by
--     intro h h' hyp
--     apply coe_injective (DFunLike.coe_injective hyp)

-- TODO: add ContDiffEmbedding and OpenContDiffEmbedding also? how to avoid API duplication?

/-- A smooth embedding `f : M → M'` is a smooth map which is both an immersion and a topological
  embedding. (We do not assume smoothness of the inverse, as this follows automatically.
  See `SmoothEmbedding.diffeomorph_of_surjective` and variants.) -/
structure SmoothEmbedding (f : M → M') (n : ℕ∞) extends Embedding f : Prop :=
  smooth : Smooth I I' f
  diff_injective : ∀ p, Injective (mfderiv I I' f p)

/-- A `SmoothEmbedding` with open range. -/
structure OpenSmoothEmbedding (f : M → M') (n : ℕ∞) extends SmoothEmbedding I I' f n : Prop :=
  isOpen_range : IsOpen <| range f

variable {I I'} in
lemma OpenSmoothEmbedding.toOpenEmbedding {f : M → M'} {n : ℕ∞} (h : OpenSmoothEmbedding I I' f n) :
    OpenEmbedding f where
  toEmbedding := h.toEmbedding
  open_range := h.isOpen_range

end Definition

/-! Immersions and embeddings -/
section ImmersionEmbeddings

variable {f : M → M'} {n : ℕ∞}

/-- A smooth embedding is an injective immersion. -/
lemma SmoothEmbedding.toInjImmersion (h : SmoothEmbedding I I' f n) : InjImmersion I I' f n where
  contMDiff := h.smooth.contMDiff
  diff_injective := h.diff_injective
  injective := h.toEmbedding.inj

-- an injective immersion need not be an embedding: cue the standard example

/-- A proper smooth injective immersion is an embedding, in fact a closed embedding. -/
lemma Embedding.of_proper_injective_immersion (h : Immersion I I' f ∞) (hp : IsProperMap f)
    (hf : Injective f) : SmoothEmbedding I I' f n where
  -- TODO: use "a proper injective continuous map is a closed embedding"
  -- does mathlib have this and the converse already?
  toEmbedding := sorry
  smooth := h.contMDiff
  diff_injective := h.diff_injective

end ImmersionEmbeddings

namespace OpenSmoothEmbedding

variable {f : M → M'} {n : ℕ∞}
variable {I I'}

instance : FunLike (SmoothEmbedding I I' f n) M M' where
  coe := fun _ ↦ f
  coe_injective' := by
    intro h _ _
    congr

attribute [coe] OpenSmoothEmbedding.toSmoothEmbedding
/-- Coerce open smooth embeddings to smooth embeddings. -/
instance coe : Coe (OpenSmoothEmbedding I I' f n) (SmoothEmbedding I I' f n) :=
  ⟨toSmoothEmbedding⟩

theorem coe_injective : Function.Injective ((↑) : (OpenSmoothEmbedding I I' f n) → (SmoothEmbedding I I' f n)) := by
  intro h h' _
  congr

-- Note. Contrary to the previous definition, `invFun` is not part of the data, so we cna
-- have a `FunLike` coercion!
instance : FunLike (OpenSmoothEmbedding I I' f n) M M' where
  coe := fun _ ↦ f
  coe_injective' := by
    intro h h' hyp
    apply coe_injective (DFunLike.coe_injective hyp)

lemma injective (h : OpenSmoothEmbedding I I' f n) : Injective h := h.toEmbedding.inj

protected theorem continuous (h : OpenSmoothEmbedding I I' f n) : Continuous h :=
  (h.smooth).continuous

lemma isOpenMap (h : OpenSmoothEmbedding I I' f n) : IsOpenMap f := h.toOpenEmbedding.isOpenMap

theorem inducing (h : OpenSmoothEmbedding I I' f n) : Inducing f :=
  h.toOpenEmbedding.toInducing

/-- An open smooth embedding on a non-empty domain is a partial homeomorphism. -/
def toPartialHomeomorph [Nonempty M]
    (h : OpenSmoothEmbedding I I' f n) : PartialHomeomorph M M' :=
  h.toOpenEmbedding.toPartialHomeomorph

-- currently unused; is this lemma needed? what's a good name?
lemma toPartialHomeomorph_coe [Nonempty M] (h : OpenSmoothEmbedding I I' f n) :
  h.toPartialHomeomorph = h.toOpenEmbedding.toPartialHomeomorph := rfl

lemma toPartialHomeomorph_coeFn [Nonempty M] (h : OpenSmoothEmbedding I I' f n) :
  h.toPartialHomeomorph = f := rfl

 -- currently unused; is this lemma needed?
lemma toPartialHomeomorph_source [Nonempty M] (h : OpenSmoothEmbedding I I' f n) :
    (h.toPartialHomeomorph).source = univ := by
  rw [h.toPartialHomeomorph_coe, OpenEmbedding.toPartialHomeomorph_source]

/-- A choice of inverse function: values outside `f.range` are arbitrary. -/
@[pp_dot]
def invFun [Nonempty M] (h : OpenSmoothEmbedding I I' f n) : M' → M :=
  (h.toPartialHomeomorph).invFun

@[simp]
lemma left_inv [Nonempty M] (h : OpenSmoothEmbedding I I' f n) (x : M) :
    h.invFun (h x) = x := by
  apply (h.toOpenEmbedding).toPartialHomeomorph_left_inv

lemma smoothOn_inv [Nonempty M] (h : OpenSmoothEmbedding I I' f n) :
    SmoothOn I' I h.invFun (range f) := by
  -- This will follow from a good theory of embedded submanifolds and diffeomorphisms:
  -- - the image of a smooth embedding is a submanifold
  -- - a smooth embedding `f` is a diffeomorphism to its image,
  --   hence has a smooth inverse function
  -- - on `im(f)`, this inverse coincides with `f.invFun`
  sorry

variable [Nonempty M]

@[simp]
theorem invFun_comp_coe (h : OpenSmoothEmbedding I I' f n) : h.invFun ∘ h = id := by
  ext
  apply h.left_inv

@[simp]
theorem right_inv {y : M'} (h : OpenSmoothEmbedding I I' f n) (hy : y ∈ range h) : h (h.invFun y) = y := by
  obtain ⟨x, rfl⟩ := hy
  erw [h.left_inv]

theorem smoothAt_inv {y : M'} (h : OpenSmoothEmbedding I I' f n) (hy : y ∈ range h) : SmoothAt I' I h.invFun y :=
  (h.smoothOn_inv y hy).contMDiffAt <| h.isOpen_range.mem_nhds hy

theorem smoothAt_inv' {x : M} (h : OpenSmoothEmbedding I I' f n) : SmoothAt I' I h.invFun (h x) :=
  h.smoothAt_inv <| mem_range_self x

theorem leftInverse (h : OpenSmoothEmbedding I I' f n) : Function.LeftInverse h.invFun h := fun x ↦ left_inv h x

section filters

open Topology in
theorem coe_comp_invFun_eventuallyEq (h : OpenSmoothEmbedding I I' f n) (x : M) : h ∘ h.invFun =ᶠ[𝓝 (h x)] id :=
  Filter.eventually_of_mem (h.isOpenMap.range_mem_nhds x) fun _ hy ↦ h.right_inv hy

open Filter
open scoped Topology
-- XXX: is the custom notation in Notations useful and should be kept?

theorem forall_near' (h : OpenSmoothEmbedding I I' f n) {P : M → Prop} {A : Set M'}
    (hyp : ∀ᶠ (m : M) in 𝓝ˢ (f ⁻¹' A), P m) :
    ∀ᶠ (m' : M') in 𝓝ˢ (A ∩ range f), ∀ (m : M), m' = f m → P m := by
  rw [eventually_nhdsSet_iff_forall] at hyp ⊢
  rintro _ ⟨hfm₀, m₀, rfl⟩
  have : ∀ U ∈ 𝓝 m₀, ∀ᶠ m' in 𝓝 (f m₀), m' ∈ f '' U := by
    intro U U_in
    exact (h.isOpenMap).image_mem_nhds U_in
  apply (this _ <| hyp m₀ hfm₀).mono
  rintro _ ⟨m₀, hm₀, hm₀'⟩ m₁ rfl
  rwa [← h.injective hm₀']

variable {X : Type*} [TopologicalSpace X]

-- belongs to Topology.NhdsSet
theorem eventually_nhdsSet_mono {s t : Set X} {P : X → Prop}
    (h : ∀ᶠ (x : X) in 𝓝ˢ t, P x) (h' : s ⊆ t) : ∀ᶠ (x : X) in 𝓝ˢ s, P x :=
  h.filter_mono (nhdsSet_mono h')

-- TODO: optimize this proof which is probably more complicated than it needs to be
theorem forall_near [T2Space M'] {P : M → Prop} {P' : M' → Prop} {K : Set M}
    (h : OpenSmoothEmbedding I I' f n) (hK : IsCompact K) {A : Set M'}
    (hP : ∀ᶠ (m : M) in 𝓝ˢ (f ⁻¹' A), P m) (hP' : ∀ᶠ (m' : M') in 𝓝ˢ A, m' ∉ f '' K → P' m')
    (hPP' : ∀ m, P m → P' (f m)) : ∀ᶠ (m' : M') in 𝓝ˢ A, P' m' := by
  rw [show A = A ∩ range f ∪ A ∩ (range f)ᶜ by simp]
  apply Filter.Eventually.union
  · have : ∀ᶠ (m' : M') in 𝓝ˢ (A ∩ range f), m' ∈ range f :=
      h.isOpen_range.mem_nhdsSet.mpr (inter_subset_right _ _)
    apply (this.and <| h.forall_near' hP).mono
    rintro _ ⟨⟨m, rfl⟩, hm⟩
    exact hPP' _ (hm _ rfl)
  · have op : IsOpen ((f '' K)ᶜ) := by
      rw [isOpen_compl_iff]
      exact (hK.image h.continuous).isClosed
    have : A ∩ (range f)ᶜ ⊆ A ∩ (f '' K)ᶜ :=
      inter_subset_inter_right _ (compl_subset_compl.mpr (image_subset_range f K))
    apply eventually_nhdsSet_mono _ this
    rw [eventually_nhdsSet_iff_forall] at hP' ⊢
    rintro x ⟨hx, hx'⟩
    have hx' : ∀ᶠ y in 𝓝 x, y ∈ (f '' K)ᶜ := isOpen_iff_eventually.mp op x hx'
    apply ((hP' x hx).and hx').mono
    rintro y ⟨hy, hy'⟩
    exact hy hy'

end filters

end OpenSmoothEmbedding

section composition

variable {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''}
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H'' M''] [SmoothManifoldWithCorners I'' M'']
variable {g' : M' → M''} {f' : M → M'}

variable {I I'}

@[simps!]
def Immersion.comp
    (g : Immersion I' I'' g' ⊤) (f : Immersion I I' f' ⊤) :
    Immersion I I'' (g ∘ f) ⊤ where
  contMDiff := g.contMDiff.comp f.contMDiff
  diff_injective p := by
    -- the same argument as below, FIXME deduplicate
    have aux : MDifferentiableAt I' I'' g' (f' p) := sorry --g.contMDiff.mdifferentiableAt
    have : MDifferentiableAt I I' f' p := sorry --f.contMDiff.mdifferentiableAt
    have : mfderiv I I'' (g ∘ f) p = (mfderiv I' I'' g (f p)).comp (mfderiv I I' f p) := by
      apply mfderiv_comp
      -- XXX what is going on here? something's not set up right...
      apply aux
      apply this
    rw [this]
    apply Injective.comp (g.diff_injective (f p)) (f.diff_injective p)

@[simps!]
def InjImmersion.comp
    (g : InjImmersion I' I'' g' ⊤) (f : InjImmersion I I' f' ⊤) :
    InjImmersion I I'' (g' ∘ f') ⊤ where
  toImmersion := g.toImmersion.comp f.toImmersion
  injective := g.injective.comp f.injective

@[simps!]
def SmoothEmbedding.comp
    (g : SmoothEmbedding I' I'' g' ⊤) (f : SmoothEmbedding I I' f' ⊤) :
    SmoothEmbedding I I'' (g ∘ f) ⊤ where
  toEmbedding := g.toEmbedding.comp (f.toEmbedding)
  smooth := g.smooth.comp f.smooth
  diff_injective p := by
    have aux : MDifferentiableAt I' I'' g' (f' p) := g.smooth.mdifferentiableAt
    have : MDifferentiableAt I I' f' p := f.smooth.mdifferentiableAt
    have : mfderiv I I'' (g ∘ f) p = (mfderiv I' I'' g (f p)).comp (mfderiv I I' f p) := by
      apply mfderiv_comp
      -- XXX what is going on here? something's not set up right...
      apply aux
      apply this
    rw [this]
    apply Injective.comp (g.diff_injective (f p)) (f.diff_injective p)

@[simps!]
def OpenSmoothEmbedding.comp
    (g : OpenSmoothEmbedding I' I'' g' ⊤) (f : OpenSmoothEmbedding I I' f' ⊤) :
    OpenSmoothEmbedding I I'' (g ∘ f) ⊤ where
  toSmoothEmbedding := g.toSmoothEmbedding.comp (f.toSmoothEmbedding)
  isOpen_range := (g.isOpenMap.comp f.isOpenMap).isOpen_range

end composition

-- other sanity check: identity; continuous linear equivalences
-- and more generally, local diffeomorphisms: all done on a branch
