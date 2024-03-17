/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
import Mathlib.Geometry.Manifold.MFDeriv.Defs
import Mathlib.Topology.ProperMap

/-! ## Smooth immersions

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

/-- An injective `C^n` immersion -/
structure InjImmersion (f : M → M') (n : ℕ∞) extends Immersion I I' f n : Prop :=
  injective : Injective f

/-- A `C^n` embedding `f : M → M'` is a `C^n` map which is both an immersion and a topological
  embedding. (We do not assume smoothness of the inverse, as this follows automatically.
  See `SmoothEmbedding.diffeomorph_of_surjective` and variants.) -/
structure SmoothEmbedding (f : M → M') (n : ℕ∞) extends Embedding f : Prop :=
  --differentiable : ContMDiff I I' n f
  smooth : Smooth I I' f
  diff_injective : ∀ p, Injective (mfderiv I I' f p)

/-- A `SmoothEmbedding` with open range. -/
structure OpenSmoothEmbeddingMR (f : M → M') (n : ℕ∞) extends SmoothEmbedding I I' f n : Prop :=
  isOpen_range : IsOpen <| range f

variable {I I'} in
lemma OpenSmoothEmbeddingMR.toOpenEmbedding {f : M → M'} {n : ℕ∞} (h : OpenSmoothEmbeddingMR I I' f n) :
    OpenEmbedding f where
  toEmbedding := h.toEmbedding
  open_range := h.isOpen_range

end Definition

/-! Immersions and embeddings -/
section ImmersionEmbeddings

variable {f : M → M'} {n : ℕ∞}

/-- A smooth embedding is an injective immersion. -/
lemma SmoothEmbedding.toInjImmersion (h : SmoothEmbedding I I' f n) : InjImmersion I I' f n where
  differentiable := h.smooth.contMDiff
  diff_injective := h.diff_injective
  injective := h.toEmbedding.inj

-- an injective immersion need not be an embedding: cue the standard example

/-- A proper injective immersion is an embedding, in fact a closed embedding. -/
lemma Embedding.of_proper_injective_immersion (h : Immersion I I' f n) (hp : IsProperMap f)
    (hf : Injective f) : SmoothEmbedding I I' f n where
  -- TODO: use "a proper injective continuous map is a closed embedding"
  -- does mathlib have this and the converse already?
  toEmbedding := sorry
  smooth := sorry -- h.differentiable
  diff_injective := h.diff_injective

end ImmersionEmbeddings

namespace OpenSmoothEmbeddingMR

variable {f : M → M'} {n : ℕ∞}
variable {I I'}

instance : FunLike (SmoothEmbedding I I' f n) M M' where
  coe := fun _ ↦ f
  coe_injective' := by
    intro h _ _
    congr

attribute [coe] OpenSmoothEmbeddingMR.toSmoothEmbedding
/-- Coerce open smooth embeddings to smooth embeddings. -/
instance coe : Coe (OpenSmoothEmbeddingMR I I' f n) (SmoothEmbedding I I' f n) :=
  ⟨toSmoothEmbedding⟩

theorem coe_injective : Function.Injective ((↑) : (OpenSmoothEmbeddingMR I I' f n) → (SmoothEmbedding I I' f n)) := by
  intro h h' _
  congr

-- Note. Contrary to the previous definition, `invFun` is not part of the data, so we cna
-- have a `FunLike` coercion!
instance : FunLike (OpenSmoothEmbeddingMR I I' f n) M M' where
  coe := fun _ ↦ f
  coe_injective' := by
    intro h h' hyp
    apply coe_injective (DFunLike.coe_injective hyp)

-- Wait: this doesn't make *any* sense if the codomain is empty!

/-- An open smooth embedding on a non-empty domain is a partial homeomorphism. -/
def toPartialHomeomorph [Nonempty M]
    (h : OpenSmoothEmbeddingMR I I' f n) : PartialHomeomorph M M' :=
  h.toOpenEmbedding.toPartialHomeomorph

-- currently unused; is this lemma needed? what's a good name?
lemma toPartialHomeomorph_coe [Nonempty M] (h : OpenSmoothEmbeddingMR I I' f n) :
  h.toPartialHomeomorph = h.toOpenEmbedding.toPartialHomeomorph := rfl

lemma toPartialHomeomorph_coeFn [Nonempty M] (h : OpenSmoothEmbeddingMR I I' f n) :
  h.toPartialHomeomorph = f := rfl

 -- currently unused; is this lemma needed?
lemma toPartialHomeomorph_source [Nonempty M] (h : OpenSmoothEmbeddingMR I I' f n) :
    (h.toPartialHomeomorph).source = univ := by
  rw [h.toPartialHomeomorph_coe, OpenEmbedding.toPartialHomeomorph_source]

/-- A choice of inverse function: values outside `f.range` are arbitrary. -/
@[pp_dot]
def invFun [Nonempty M] (h : OpenSmoothEmbeddingMR I I' f n) : M' → M :=
  (h.toPartialHomeomorph).invFun

@[simp]
lemma left_inv [Nonempty M] (h : OpenSmoothEmbeddingMR I I' f n) {x : M}:
    h.invFun (f x) = x := by
  apply (h.toOpenEmbedding).toPartialHomeomorph_left_inv

lemma smoothOn_inv [Nonempty M] (h : OpenSmoothEmbeddingMR I I' f n) :
    SmoothOn I' I h.invFun (range f) := by
  sorry -- TODO: prove this!

lemma isOpenMap (h : OpenSmoothEmbeddingMR I I' f n) : IsOpenMap f := h.toOpenEmbedding.isOpenMap

theorem inducing (h : OpenSmoothEmbeddingMR I I' f n) : Inducing f :=
  h.toOpenEmbedding.toInducing

end OpenSmoothEmbeddingMR
