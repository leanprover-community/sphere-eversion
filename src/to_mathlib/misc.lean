import data.real.nnreal

open real set
open_locale nnreal interval

/-- to algebra.ring.basic or something -/
@[simp] lemma smul_add_one_sub_smul {R M : Type*} [ring R] [add_comm_monoid M] [module R M]
  {r : R} {m : M} : r • m + (1 - r) • m = m :=
by rw [← add_smul, add_sub_cancel'_right, one_smul]

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

lemma interval_oc_subset_of_mem_Ioc {α : Type*} [linear_order α] {a b c d : α}
  (ha : a ∈ Ioc c d) (hb : b ∈ Ioc c d) : Ι a b ⊆ Ι c d :=
begin
   rw interval_oc_of_le (ha.1.le.trans ha.2),
   exact Ioc_subset_Ioc (le_min ha.1.le hb.1.le) (max_le ha.2 hb.2)
end

lemma interval_subset_Ioo  {α : Type*} [linear_order α] {a b c d : α}
  (ha : a ∈ Ioo c d) (hb : b ∈ Ioo c d) : interval a b ⊆ Ioo c d :=
λ t ⟨ht, ht'⟩, ⟨(lt_min ha.1 hb.1).trans_le ht, ht'.trans_lt (max_lt ha.2 hb.2)⟩

lemma interval_oc_subset_Ioo  {α : Type*} [linear_order α] {a b c d : α}
  (ha : a ∈ Ioo c d) (hb : b ∈ Ioo c d) : Ι a b ⊆ Ioo c d :=
λ t ⟨ht, ht'⟩, ⟨(lt_min ha.1 hb.1).trans ht, ht'.trans_lt (max_lt ha.2 hb.2)⟩

namespace set
variables {α β : Type*}

/- near `set.Iic_union_Ici` -/
lemma Iic_union_Ici' {α : Type*} [linear_order α] {a b : α} (h : b ≤ a) :
  Iic a ∪ Ici b = univ :=
eq_univ_of_forall $ λ x, (le_total x a).imp id $ le_trans h

/- to data.set.finite -/
lemma finite_of_finite_preimage {s : set β} {f : α → β} (h : finite (f ⁻¹' s))
  (hs : s ⊆ range f) : finite s :=
by { rw [← image_preimage_eq_of_subset hs], exact finite.image f h }

@[simp] lemma mk_diag_preimage_prod (s t : set α) :
  (λ (a : α), (a, a))⁻¹' (s ×ˢ t) = s ∩ t :=
rfl

@[simp] lemma mk_diag_preimage_prod_self (s : set α) :
  (λ (a : α), (a, a))⁻¹' (s ×ˢ s) = s :=
s.inter_self

end set

lemma has_mem.mem.mul {a b : ℝ} (ha : a ∈ (set.Icc 0 1 : set ℝ)) (hb : b ∈ (set.Icc 0 1 : set ℝ)) :
  a*b ∈ (set.Icc 0 1 : set ℝ) :=
begin
  rw mem_Icc at *,
  split ; nlinarith
end

lemma int.fract.mem_Ico {α : Type*} [linear_ordered_ring α] [floor_ring α] (a : α) :
  int.fract a ∈ (set.Ico 0 1 : set α) :=
⟨int.fract_nonneg a, int.fract_lt_one a⟩

lemma int.fract.mem_Icc {α : Type*} [linear_ordered_ring α] [floor_ring α] (a : α) :
  int.fract a ∈ (set.Icc 0 1 : set α) :=
Ico_subset_Icc_self (int.fract.mem_Ico a)
