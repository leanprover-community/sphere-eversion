import data.real.nnreal
import algebra.big_operators.finprod

open real set function
open_locale nnreal interval big_operators

/-- to algebra.ring.basic or something -/
@[simp] lemma smul_add_one_sub_smul {R M : Type*} [ring R] [add_comm_monoid M] [module R M]
  {r : R} {m : M} : r • m + (1 - r) • m = m :=
by rw [← add_smul, add_sub_cancel'_right, one_smul]

section product_monoid

@[to_additive]
lemma prod.one_mk_mul_one_mk {M N : Type*} [monoid M] [has_mul N] (b₁ b₂ : N) :
  ((1 : M), b₁) * (1, b₂) = (1, b₁ * b₂) :=
by rw [prod.mk_mul_mk, mul_one]

lemma prod.smul_zero_mk {M α β : Type*} [monoid M] [add_monoid α] [distrib_mul_action M α]
  [has_smul M β] (a : M) (c : β) :
  a • ((0 : α), c) = (0, a • c) :=
by rw [prod.smul_mk, smul_zero]

end product_monoid


lemma nnabs_coe (K : ℝ≥0) : nnabs K = K := by simp

lemma abs_le_abs_of_nonneg {α : Type*} [add_comm_group α] [linear_order α]
   [covariant_class α α (+) (≤)] {a b : α}
  (ha : 0 ≤ a) (hab : a ≤ b) :
  |a| ≤ |b| :=
by rwa [abs_of_nonneg ha, abs_of_nonneg (ha.trans hab)]

lemma abs_le_abs_of_nonpos {α : Type*} [add_comm_group α] [linear_order α]
   [covariant_class α α (+) (≤)] {a b : α}
  (ha : a ≤ 0) (hab : b ≤ a) :
  |a| ≤ |b| :=
by { rw [abs_of_nonpos ha, abs_of_nonpos (hab.trans ha)], exact neg_le_neg_iff.mpr hab }

namespace set
variables {α β γ : Type*}


lemma function.injective.inj_on_range {j : α → β} {φ : β → γ}
  (h : injective $ φ ∘ j) : inj_on φ (range j) :=
begin
  rintros - ⟨x, rfl⟩ - ⟨y, rfl⟩ H,
  exact congr_arg j (h H)
end


/- to data.set.finite -/
lemma finite_of_finite_preimage {s : set β} {f : α → β} (h : (f ⁻¹' s).finite)
  (hs : s ⊆ range f) : s.finite :=
by { rw [← image_preimage_eq_of_subset hs], exact finite.image f h }

end set


section finprod
/-! ## Missing finprod/finsum lemmas -/

variables {M : Type*} [comm_monoid M] {ι ι' : Type*}

@[to_additive]
lemma finset.prod_equiv [decidable_eq ι] {e : ι ≃ ι'} {f : ι' → M} {s' : finset ι'} {s : finset ι}
  (h : s = s'.image e.symm) :
  ∏ i' in s', f i' = ∏ i in s, f (e i) :=
begin
  rw [h],
  refine finset.prod_bij' (λ i' hi', e.symm i') (λ a ha, finset.mem_image_of_mem _ ha)
    (λ a ha, by simp_rw [e.apply_symm_apply]) (λ i hi, e i) (λ a ha, _)
    (λ a ha, e.apply_symm_apply a) (λ a ha, e.symm_apply_apply a),
  rcases finset.mem_image.mp ha with ⟨i', hi', rfl⟩,
  rwa [e.apply_symm_apply]
end

end finprod
