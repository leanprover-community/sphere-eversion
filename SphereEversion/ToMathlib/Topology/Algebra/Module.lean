import Mathbin.Topology.Algebra.Module.Basic

open Filter ContinuousLinearMap Function

open scoped Topology BigOperators Filter

namespace ContinuousLinearMap

variable {R₁ M₁ M₂ M₃ : Type _} [Semiring R₁]

variable [TopologicalSpace M₁] [AddCommMonoid M₁]

variable [TopologicalSpace M₂] [AddCommMonoid M₂]

variable [TopologicalSpace M₃] [AddCommMonoid M₃]

variable [Module R₁ M₁] [Module R₁ M₂] [Module R₁ M₃]

theorem fst_prod_zero_add_zero_prod_snd [ContinuousAdd M₁] [ContinuousAdd M₂] :
    (ContinuousLinearMap.fst R₁ M₁ M₂).Prod 0 +
        ContinuousLinearMap.prod 0 (ContinuousLinearMap.snd R₁ M₁ M₂) =
      ContinuousLinearMap.id R₁ (M₁ × M₂) :=
  by
  rw [ContinuousLinearMap.ext_iff]
  intro x
  simp_rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    ContinuousLinearMap.zero_apply, Prod.mk_add_mk, add_zero, zero_add, Prod.mk.eta]

end ContinuousLinearMap

variable {R₁ : Type _} {R₂ : Type _} {R₃ : Type _} [Semiring R₁] [Semiring R₂] [Semiring R₃]
  {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
  {σ₂₃ : R₂ →+* R₃} {σ₃₂ : R₃ →+* R₂} [RingHomInvPair σ₂₃ σ₃₂] [RingHomInvPair σ₃₂ σ₂₃]
  {σ₁₃ : R₁ →+* R₃} {σ₃₁ : R₃ →+* R₁} [RingHomInvPair σ₁₃ σ₃₁] [RingHomInvPair σ₃₁ σ₁₃]
  [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomCompTriple σ₃₂ σ₂₁ σ₃₁] {M₁ : Type _}
  [TopologicalSpace M₁] [AddCommMonoid M₁] {M'₁ : Type _} [TopologicalSpace M'₁] [AddCommMonoid M'₁]
  {M₂ : Type _} [TopologicalSpace M₂] [AddCommMonoid M₂] {M₃ : Type _} [TopologicalSpace M₃]
  [AddCommMonoid M₃] {M₄ : Type _} [TopologicalSpace M₄] [AddCommMonoid M₄] [Module R₁ M₁]
  [Module R₁ M'₁] [Module R₂ M₂] [Module R₃ M₃]

section

theorem Function.Surjective.clm_comp_injective {g : M₁ →SL[σ₁₂] M₂} (hg : Function.Surjective g) :
    Function.Injective fun f : M₂ →SL[σ₂₃] M₃ => f.comp g :=
  by
  intro f f' hff'
  rw [ContinuousLinearMap.ext_iff] at hff' ⊢
  intro x
  obtain ⟨y, rfl⟩ := hg x
  exact hff' y

end

namespace ContinuousLinearEquiv

theorem cancel_right {f f' : M₂ →SL[σ₂₃] M₃} {e : M₁ ≃SL[σ₁₂] M₂} :
    f.comp (e : M₁ →SL[σ₁₂] M₂) = f'.comp (e : M₁ →SL[σ₁₂] M₂) ↔ f = f' :=
  by
  constructor
  · simp_rw [ContinuousLinearMap.ext_iff, ContinuousLinearMap.comp_apply, coe_coe]
    intro h v; rw [← e.apply_symm_apply v, h]
  · rintro rfl; rfl

theorem cancel_left {e : M₂ ≃SL[σ₂₃] M₃} {f f' : M₁ →SL[σ₁₂] M₂} :
    (e : M₂ →SL[σ₂₃] M₃).comp f = (e : M₂ →SL[σ₂₃] M₃).comp f' ↔ f = f' :=
  by
  constructor
  · simp_rw [ContinuousLinearMap.ext_iff, ContinuousLinearMap.comp_apply, coe_coe]
    intro h v; rw [← e.symm_apply_apply (f v), h, e.symm_apply_apply]
  · rintro rfl; rfl

end ContinuousLinearEquiv

