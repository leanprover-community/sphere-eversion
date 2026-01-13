import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.LinearAlgebra.Dual.Lemmas
import SphereEversion.Notations
import SphereEversion.ToMathlib.Analysis.NormedSpace.OperatorNorm.Prod
import SphereEversion.ToMathlib.LinearAlgebra.Basic

/-! # Dual pairs

Convex integration improves maps by successively modify their derivative in a direction of a
vector field (almost) without changing their derivative along some complementary hyperplace.

In this file we introduce the linear algebra part of the story of such modifications.
The main gadget here are dual pairs on a real topological vector space `E`.
Each `p : DualPair E` is made of a (continuous) linear form `p.π : E →L[ℝ] ℝ` and a vector
`p.v : E` such that `p.π p.v = 1`.

Those pairs are used to build the updating operation turning `φ : E →L[ℝ] F` into
`p.update φ w` which equals `φ` on `ker p.π` and sends `v` to the given `w : F`.

After formalizing the above definitions, we first record a number of trivial algebraic lemmas.
Then we prove a lemma which is geometrically obvious but not so easy to formalize:
`injective_update_iff` states, starting with an injective `φ`, that the updated
map `p.update φ w` is injective if and only if `w` isn't in the image of `ker p.π` under `φ`.
This is crucial in order to apply convex integration to immersions.

Then we prove continuity and smoothness lemmas for this operation.
-/


noncomputable section

open Function ContinuousLinearMap

open LinearMap (ker)

open scoped ContDiff

/-! ## General theory -/

section NoNorm

variable (E : Type*) {E' F G : Type*}

variable [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

variable [AddCommGroup E'] [Module ℝ E'] [TopologicalSpace E']

variable [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- A continuous linear form `π` and a vector `v` that pair to one. In particular `ker π` is a
hyperplane and `v` spans a complement of this hyperplane. -/
structure DualPair where
  π : E →L[ℝ] ℝ
  v : E
  pairing : π v = 1

namespace DualPair

variable {E}

attribute [local simp] ContinuousLinearMap.toSpanSingleton_apply

theorem pi_ne_zero (p : DualPair E) : p.π ≠ 0 := fun H ↦ by
  simpa [H] using p.pairing

theorem ker_pi_ne_top (p : DualPair E) : p.π.ker ≠ ⊤ := fun H ↦ by
  have : p.π.toLinearMap p.v = 1 := p.pairing
  simpa [LinearMap.ker_eq_top.mp H]

theorem v_ne_zero (p : DualPair E) : p.v ≠ 0 := fun H ↦ by simpa [H] using p.pairing

/-- Given a dual pair `p`, `p.span_v` is the line spanned by `p.v`. -/
def spanV (p : DualPair E) : Submodule ℝ E :=
  Submodule.span ℝ {p.v}

theorem mem_spanV (p : DualPair E) {u : E} : u ∈ p.spanV ↔ ∃ t : ℝ, u = t • p.v := by
  simp [DualPair.spanV, Submodule.mem_span_singleton, eq_comm]

/-- Update a continuous linear map `φ : E →L[ℝ] F` using a dual pair `p` on `E` and a
vector `w : F`. The new map coincides with `φ` on `ker p.π` and sends `p.v` to `w`. -/
def update (p : DualPair E) (φ : E →L[ℝ] F) (w : F) : E →L[ℝ] F :=
  φ + (w - φ p.v) ⬝ p.π

@[simp]
theorem update_ker_pi (p : DualPair E) (φ : E →L[ℝ] F) (w : F) {u} (hu : u ∈ p.π.ker) :
    p.update φ w u = φ u := by
  rw [LinearMap.mem_ker] at hu
  simpa [update] using Or.inl hu

@[simp]
theorem update_v (p : DualPair E) (φ : E →L[ℝ] F) (w : F) : p.update φ w p.v = w := by
  simp [update, p.pairing]

@[simp]
theorem update_self (p : DualPair E) (φ : E →L[ℝ] F) : p.update φ (φ p.v) = φ := by
  simp only [update, add_zero, ContinuousLinearMap.toSpanSingleton_zero,
    ContinuousLinearMap.zero_comp, sub_self]

@[simp]
theorem update_update (p : DualPair E) (φ : E →L[ℝ] F) (w w' : F) :
    p.update (p.update φ w') w = p.update φ w := by
  simp_rw [update, add_apply, coe_comp', (· ∘ ·), toSpanSingleton_apply, p.pairing, one_smul,
    add_sub_cancel, add_assoc, ← ContinuousLinearMap.add_comp, ← toSpanSingleton_add,
    sub_add_eq_add_sub, add_sub_cancel]

theorem inf_eq_bot (p : DualPair E) : p.π.ker ⊓ p.spanV = ⊥ := bot_unique <| fun x hx ↦ by
  have : p.π x = 0 ∧ ∃ a : ℝ, a • p.v = x := by
    simpa [DualPair.spanV, Submodule.mem_span_singleton] using hx
  rcases this with ⟨H, t, rfl⟩
  rw [p.π.map_smul, p.pairing, smul_eq_mul, mul_one] at H
  simp [H]

theorem sup_eq_top (p : DualPair E) : p.π.ker ⊔ p.spanV = ⊤ := by
  rw [Submodule.sup_eq_top_iff]
  intro x
  refine ⟨x - p.π x • p.v, ?_, p.π x • p.v, ?_, ?_⟩ <;>
    simp [DualPair.spanV, Submodule.mem_span_singleton, p.pairing]

theorem decomp (p : DualPair E) (e : E) : ∃ u ∈ p.π.ker, ∃ t : ℝ, e = u + t • p.v := by
  have : e ∈ p.π.ker ⊔ p.spanV := by
    rw [p.sup_eq_top]
    exact Submodule.mem_top
  simp_rw [Submodule.mem_sup, DualPair.mem_spanV] at this
  rcases this with ⟨u, hu, -, ⟨t, rfl⟩, rfl⟩
  exact ⟨u, hu, t, rfl⟩

-- useful with `DualPair.decomp`
theorem update_apply (p : DualPair E) (φ : E →L[ℝ] F) {w : F} {t : ℝ} {u} (hu : u ∈ p.π.ker) :
    p.update φ w (u + t • p.v) = φ u + t • w := by
  rw [map_add, map_smul, p.update_v, p.update_ker_pi _ _ hu]

/-- Map a dual pair under a linear equivalence. -/
@[simps]
def map (p : DualPair E) (L : E ≃L[ℝ] E') : DualPair E' :=
  ⟨p.π ∘L ↑L.symm, L p.v, (congr_arg p.π <| L.symm_apply_apply p.v).trans p.pairing⟩

theorem update_comp_left (p : DualPair E) (ψ' : F →L[ℝ] G) (φ : E →L[ℝ] F) (w : F) :
    p.update (ψ' ∘L φ) (ψ' w) = ψ' ∘L p.update φ w := by
  ext1 u
  simp only [update, add_apply, ContinuousLinearMap.comp_apply, toSpanSingleton_apply, map_add,
    map_smul, map_sub]

theorem map_update_comp_right (p : DualPair E) (ψ' : E →L[ℝ] F) (φ : E ≃L[ℝ] E') (w : F) :
    (p.map φ).update (ψ' ∘L ↑φ.symm) w = p.update ψ' w ∘L ↑φ.symm := by
  ext1 u
  simp [update]

/-! ## Injectivity criterion -/


@[simp]
theorem injective_update_iff (p : DualPair E) {φ : E →L[ℝ] F} (hφ : Injective φ) {w : F} :
    Injective (p.update φ w) ↔ w ∉ (p.π.ker).map (φ : E →ₛₗ[.id ℝ] F) := by
  constructor
  · rintro h ⟨u, hu, rfl⟩
    have : p.update φ (φ u) p.v = φ u := p.update_v φ (φ u)
    nth_rw 2 [← p.update_ker_pi φ (φ u) hu] at this
    simp [← h this, p.pairing] at hu
  · intro hw
    refine (injective_iff_map_eq_zero (p.update φ w)).mpr fun x hx ↦ ?_
    rcases p.decomp x with ⟨u, hu, t, rfl⟩
    rw [map_add, map_smul, update_v, p.update_ker_pi _ _ hu] at hx
    obtain rfl : t = 0 := by
      by_contra ht
      apply hw
      refine ⟨-t⁻¹ • u, (p.π.ker).smul_mem _ hu, ?_⟩
      rw [map_smul]
      have : -t⁻¹ • (φ u + t • w) + w = -t⁻¹ • (0 : F) + w := congr_arg (-t⁻¹ • · + w) hx
      rwa [smul_add, neg_smul, neg_smul, inv_smul_smul₀ ht, smul_zero, zero_add,
        neg_add_cancel_right, ← neg_smul] at this
    rw [zero_smul, add_zero] at hx ⊢
    exact (injective_iff_map_eq_zero φ).mp hφ u hx

end DualPair

end NoNorm

/-! ## Smoothness and continuity -/


namespace DualPair

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/- In the next two lemmas, finite dimensionality of `E` is clearly uneeded, but allows
to use `contDiff_clm_apply_iff` and `continuous_clm_apply`. -/
theorem smooth_update [FiniteDimensional ℝ E] (p : DualPair E) {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {φ : G → E →L[ℝ] F} (hφ : 𝒞 ∞ φ) {w : G → F} (hw : 𝒞 ∞ w) :
    𝒞 ∞ fun g ↦ p.update (φ g) (w g) := by
  apply hφ.add
  rw [contDiff_clm_apply_iff]
  intro y
  exact (hw.sub (contDiff_clm_apply_iff.mp hφ p.v)).const_smul _

theorem continuous_update [FiniteDimensional ℝ E] (p : DualPair E) {X : Type*} [TopologicalSpace X]
    {φ : X → E →L[ℝ] F} (hφ : Continuous φ) {w : X → F} (hw : Continuous w) :
    Continuous fun g ↦ p.update (φ g) (w g) := by
  apply hφ.add
  rw [continuous_clm_apply]
  intro y
  exact (hw.sub (continuous_clm_apply.mp hφ p.v)).const_smul _

end DualPair

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- Given a finite basis `e : basis ι ℝ E`, and `i : ι`,
`e.DualPair i` is given by the `i`th basis element and its dual. -/
def Module.Basis.dualPair [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Basis ι ℝ E) (i : ι) : DualPair E where
  π := LinearMap.toContinuousLinearMap (e.dualBasis i)
  v := e i
  pairing := by simp
