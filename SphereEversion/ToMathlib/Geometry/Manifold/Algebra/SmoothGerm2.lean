import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import SphereEversion.ToMathlib.Topology.Germ

import Mathlib.Topology.ContinuousFunction.Algebra

/-! # Germs of smooth functions

WIP rewrite of `SmoothGerm`, to allow any smooth map between manifolds

## Main definitions
* `smoothGerm I I' N x`: the set of germs of smooth functions `f : M → N` at `x : M`.

-/

noncomputable section

open Filter Set

open scoped Manifold Topology BigOperators

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  -- declare a smooth manifold `M` over the pair `(E, H)` with model `I`.
  {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners 𝕜 E H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [SmoothManifoldWithCorners I M]
variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']

section ringhom

variable (I' : ModelWithCorners 𝕜 E' H')
  (R : Type*) [CommRing R] [TopologicalSpace R] [ChartedSpace H' R] [SmoothRing I' R]

/-- The map `C^∞(M, R) → Germ (𝓝 x) R` as a ring homomorphism, for a smooth ring `R`. -/
def RingHom.germOfContMDiffMap (x : M) : C^∞⟮I, M; I', R⟯ →+* Germ (𝓝 x) R :=
  RingHom.comp (Germ.coeRingHom _) SmoothMap.coeFnRingHom

end ringhom

-- Definition of germs of smooth maps, between any two manifolds.
section definition

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  -- M is a manifold over (E, H) with model I
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  -- N is a manifold over (E', H') with model I'
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] (I' : ModelWithCorners 𝕜 E' H')
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

variable (N) in
/-- The set of all germs of smooth functions `M → N` at `x : N`. -/
def smoothGerm (x : M) : Set (Germ (𝓝 x) N) :=
  { Filter.Germ.ofFun f | f : SmoothMap I I' M N }

instance (x : M) [ChartedSpace H' N] : Coe C^∞⟮I, M; I', N⟯ (smoothGerm I I' N x) :=
  ⟨fun f ↦ ⟨(f : M → N), ⟨f, rfl⟩⟩⟩

@[simp]
theorem smoothGerm.coe_coe (f : C^∞⟮I, M; I', N⟯) (x : M) :
    ((f : smoothGerm I I' N x) : (𝓝 x).Germ N) = (f : (𝓝 x).Germ N) :=
  rfl

@[simp]
theorem smoothGerm.coe_eq_coe (f g : C^∞⟮I, M; I', N⟯) {x : M} (h : ∀ᶠ y in 𝓝 x, f y = g y) :
    (f : smoothGerm I I' N x) = (g : smoothGerm I I' N x) := by
  ext
  apply Quotient.sound
  exact h

end definition

section germRing

variable (I' : ModelWithCorners 𝕜 E' H')
  (R : Type*) [CommRing R] [TopologicalSpace R] [ChartedSpace H' R] [SmoothRing I' R]

-- TODO: add variants of this for semirings, commutative etc

-- If `R` has the appropriate structure, `smoothGerm I I' R x` is a subgroup etc.
-- Proofs of the axioms are easy by choosing explicit representatives.

def smoothGerm.toSubsemigroup (x : M) : Subsemigroup (Germ (𝓝 x) R) where
  carrier := smoothGerm I I' R x
  mul_mem' ha hb := by
    choose f hf using ha
    choose g hg using hb
    use f * g
    rw [← hf, ← hg]
    rw [SmoothMap.coe_mul, Germ.coe_mul]

def smoothGerm.toAddSubgroup (x : M) : Submonoid (Germ (𝓝 x) R) where
  toSubsemigroup := smoothGerm.toSubsemigroup I I' R x
  one_mem' := ⟨1, by rw [SmoothMap.coe_one, Germ.coe_one]⟩

def smoothGerm.toSubsemiring (x : M) : Subsemiring (Germ (𝓝 x) R) where
  __ := smoothGerm.toAddSubgroup I I' R x
  zero_mem' := ⟨0, by rw [SmoothMap.coe_zero, Germ.coe_zero]⟩
  add_mem' ha hb := by
    choose f hf using ha
    choose g hg using hb
    use f + g
    rw [← hf, ← hg]
    rw [SmoothMap.coe_add, Germ.coe_add]

/-- If `R` is a smooth ring, `smoothGerm I I' R x` is a subring of `Germ (𝓝 x) R`. -/
def smoothGerm.toSubring (x : M) : Subring (Germ (𝓝 x) R) where
  toSubsemiring := smoothGerm.toSubsemiring I I' R x
  neg_mem' {a} h := by
    choose f hf using h
    use -f
    rw [← hf]
    rw [SmoothMap.coe_neg, Germ.coe_neg]

-- TODO: do I want further coercion lemmas? e.g.
-- x : subring iff it is a member of the carrier, named sth like `smoothGerm.toSubring_mem_coe`

lemma toSubring_eq_range (x : M) :
    smoothGerm.toSubring I I' R x = (RingHom.germOfContMDiffMap I I' R x).range := by
  rfl
  -- TODO: add an explicit proof; this step is good: rw [RingHom.range_eq_map]

-- failed to infer: AddCommMonoid { x_1 // x_1 ∈ smoothGerm I I' R x }
-- @[simp]
-- theorem smoothGerm.coe_sum {ι} (f : ι → C^∞⟮I, M; I', R⟯) (s : Finset ι) (x : M) :
--     ((∑ i in s, f i : C^∞⟮I, M; I', R⟯) : smoothGerm I I' R x) = ∑ i in s, (f i : smoothGerm I I' R x) :=
--   map_sum (RingHom.rangeRestrict (RingHom.germOfContMDiffMap I I' R x)) f s

-- failed to synthesize instance Semiring ↑(smoothGerm I I' R x)
-- example (x : M) : Module (smoothGerm I I' R x) (Germ (𝓝 x) G) := by infer_instance
-- example (x : N) : Module (Germ (𝓝 x) ℝ) (Germ (𝓝 x) F) := by infer_instance

-- next, after that: adapt the following lines; then PR to mathlib (or so)
-- def smoothGerm.valueOrderRingHom (x : N) : smoothGerm IG x →+*o ℝ :=
--   Filter.Germ.valueOrderRingHom.comp <| Subring.orderedSubtype _

-- def smoothGerm.valueRingHom (x : N) : smoothGerm IG x →+* ℝ :=
--   Filter.Germ.valueRingHom.comp <| Subring.subtype _

-- theorem smoothGerm.valueOrderRingHom_toRingHom (x : N) :
--     (smoothGerm.valueOrderRingHom IG x).toRingHom = smoothGerm.valueRingHom IG x :=
--   rfl

end germRing
