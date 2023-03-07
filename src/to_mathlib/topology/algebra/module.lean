import topology.algebra.module.basic

open filter continuous_linear_map function
open_locale topology big_operators filter


namespace continuous_linear_map

variables {R₁ M₁ M₂ M₃ : Type*} [semiring R₁]
variables [topological_space M₁] [add_comm_monoid M₁]
variables [topological_space M₂] [add_comm_monoid M₂]
variables [topological_space M₃] [add_comm_monoid M₃]
variables [module R₁ M₁] [module R₁ M₂] [module R₁ M₃]

-- unused
lemma comp_fst_add_comp_snd [has_continuous_add M₃] (f : M₁ →L[R₁] M₃) (g : M₂ →L[R₁] M₃) :
  f.comp (continuous_linear_map.fst R₁ M₁ M₂) +
  g.comp (continuous_linear_map.snd R₁ M₁ M₂) =
  f.coprod g :=
rfl

lemma fst_prod_zero_add_zero_prod_snd [has_continuous_add M₁] [has_continuous_add M₂] :
  (continuous_linear_map.fst R₁ M₁ M₂).prod 0 +
  continuous_linear_map.prod 0 (continuous_linear_map.snd R₁ M₁ M₂) =
  continuous_linear_map.id R₁ (M₁ × M₂) :=
begin
  rw [continuous_linear_map.ext_iff],
  intro x,
  simp_rw [continuous_linear_map.add_apply, continuous_linear_map.id_apply,
    continuous_linear_map.prod_apply, continuous_linear_map.coe_fst',
    continuous_linear_map.coe_snd', continuous_linear_map.zero_apply, prod.mk_add_mk, add_zero,
    zero_add, prod.mk.eta]
end


end continuous_linear_map

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

section
include σ₁₃
lemma function.surjective.clm_comp_injective {g : M₁ →SL[σ₁₂] M₂}
  (hg : function.surjective g) : function.injective (λ f : M₂ →SL[σ₂₃] M₃, f.comp g) :=
begin
  intros f f' hff',
  rw [continuous_linear_map.ext_iff] at hff' ⊢,
  intros x,
  obtain ⟨y, rfl⟩ := hg x,
  exact hff' y,
end
end

namespace continuous_linear_equiv

include σ₂₁ σ₁₃
theorem cancel_right {f f' : M₂ →SL[σ₂₃] M₃} {e : M₁ ≃SL[σ₁₂] M₂} :
  f.comp (e : M₁ →SL[σ₁₂] M₂) = f'.comp (e : M₁ →SL[σ₁₂] M₂) ↔ f = f' :=
begin
  split,
  { simp_rw [continuous_linear_map.ext_iff, continuous_linear_map.comp_apply, coe_coe],
    intros h v, rw [← e.apply_symm_apply v, h] },
  { rintro rfl, refl }
end

omit σ₂₁
include σ₃₂

theorem cancel_left {e : M₂ ≃SL[σ₂₃] M₃} {f f' : M₁ →SL[σ₁₂] M₂} :
  (e : M₂ →SL[σ₂₃] M₃).comp f = (e : M₂ →SL[σ₂₃] M₃).comp f' ↔ f = f' :=
begin
  split,
  { simp_rw [continuous_linear_map.ext_iff, continuous_linear_map.comp_apply, coe_coe],
    intros h v, rw [← e.symm_apply_apply (f v), h, e.symm_apply_apply] },
  { rintro rfl, refl }
end

omit σ₃₂

end continuous_linear_equiv
