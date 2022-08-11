import topology.algebra.module.basic

open filter continuous_linear_map
open_locale topological_space big_operators filter

variables {R₁ : Type*} {R₂ : Type*} {R₃ : Type*} [semiring R₁] [semiring R₂] [semiring R₃]
{σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁} [ring_hom_inv_pair σ₁₂ σ₂₁] [ring_hom_inv_pair σ₂₁ σ₁₂]
{σ₂₃ : R₂ →+* R₃} {σ₃₂ : R₃ →+* R₂} [ring_hom_inv_pair σ₂₃ σ₃₂] [ring_hom_inv_pair σ₃₂ σ₂₃]
{σ₁₃ : R₁ →+* R₃} {σ₃₁ : R₃ →+* R₁} [ring_hom_inv_pair σ₁₃ σ₃₁] [ring_hom_inv_pair σ₃₁ σ₁₃]
[ring_hom_comp_triple σ₁₂ σ₂₃ σ₁₃] [ring_hom_comp_triple σ₃₂ σ₂₁ σ₃₁]
{M₁ : Type*} [topological_space M₁] [add_comm_monoid M₁]
{M'₁ : Type*} [topological_space M'₁] [add_comm_monoid M'₁]
{M₂ : Type*} [topological_space M₂] [add_comm_monoid M₂]
{M₃ : Type*} [topological_space M₃] [add_comm_monoid M₃]
{M₄ : Type*} [topological_space M₄] [add_comm_monoid M₄]
[module R₁ M₁] [module R₁ M'₁] [module R₂ M₂] [module R₃ M₃]

namespace continuous_linear_equiv

include σ₂₁ σ₁₃
@[simp] theorem cancel_right {f f' : M₂ →SL[σ₂₃] M₃} {e : M₁ ≃SL[σ₁₂] M₂} :
  f.comp e.to_continuous_linear_map = f'.comp e.to_continuous_linear_map ↔ f = f' :=
begin
  split,
  { simp_rw [continuous_linear_map.ext_iff, continuous_linear_map.comp_apply, coe_def_rev, coe_coe],
    intros h v, rw [← e.apply_symm_apply v, h] },
  { rintro rfl, refl }
end

omit σ₂₁
include σ₃₂

@[simp] theorem cancel_left {e : M₂ ≃SL[σ₂₃] M₃} {f f' : M₁ →SL[σ₁₂] M₂} :
  e.to_continuous_linear_map.comp f = e.to_continuous_linear_map.comp f' ↔ f = f' :=
begin
  split,
  { simp_rw [continuous_linear_map.ext_iff, continuous_linear_map.comp_apply, coe_def_rev, coe_coe],
    intros h v, rw [← e.symm_apply_apply (f v), h, e.symm_apply_apply] },
  { rintro rfl, refl }
end

omit σ₃₂

end continuous_linear_equiv
