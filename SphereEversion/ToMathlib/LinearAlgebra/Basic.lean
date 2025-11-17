import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.LinearAlgebra.Span.Defs

/-! Note: some results should go to `LinearAlgebra.Span`. -/


open Submodule Function

section

variable {R : Type*} {R₂ : Type*} {M : Type*} {M₂ : Type*} [Semiring R] [Semiring R₂]
  [AddCommMonoid M] [AddCommMonoid M₂] {σ₁₂ : R →+* R₂} [Module R M] [Module R₂ M₂]

theorem Submodule.sup_eq_span_union (s t : Submodule R M) : s ⊔ t = span R (s ∪ t) := by
  rw [span_union, span_eq s, span_eq t]

end

section

variable {R : Type*} {R₂ : Type*} {M : Type*} {M₂ : Type*} [Ring R] [Ring R₂] [AddCommGroup M]
  [AddCommGroup M₂] {σ₁₂ : R →+* R₂} [Module R M] [Module R₂ M₂] {p q : Submodule R M}
  [RingHomSurjective σ₁₂]

theorem LinearMap.injective_iff_of_direct_sum (f : M →ₛₗ[σ₁₂] M₂) (hpq : p ⊓ q = ⊥)
    (hpq' : p ⊔ q = ⊤) :
    Injective f ↔ Disjoint p (LinearMap.ker f) ∧ Disjoint q (LinearMap.ker f) ∧
      Disjoint (map f p) (map f q) := by
  constructor
  · intro h
    simp [disjoint_iff_inf_le, LinearMap.ker_eq_bot.mpr h, ← Submodule.map_inf _ h, hpq]
  · rintro ⟨hp, hq, h⟩
    rw [LinearMap.disjoint_ker] at *
    rw [← LinearMap.ker_eq_bot, ← @inf_top_eq _ _ _ (LinearMap.ker f), ← hpq']
    rw [← le_bot_iff]
    rintro x ⟨hx, hx' : x ∈ p ⊔ q⟩
    rcases mem_sup.mp hx' with ⟨u, hu, v, hv, rfl⟩
    rw [mem_bot]
    erw [← sub_neg_eq_add, LinearMap.sub_mem_ker_iff] at hx
    have hu' : f u ∈ map f p := mem_map_of_mem hu
    have hv' : f (-v) ∈ map f q := mem_map_of_mem (q.neg_mem hv)
    rw [← hx] at hv'
    have H : f u ∈ map f p ⊓ map f q := mem_inf.mpr ⟨hu', hv'⟩
    rw [disjoint_iff_inf_le] at h
    rw [hp u hu (h H), zero_add]
    rw [hp u hu (h H), f.map_zero, f.map_neg, eq_comm, neg_eq_zero] at hx
    exact hq v hv hx

end
