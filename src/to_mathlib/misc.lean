import data.real.nnreal

open real set
open_locale nnreal interval

lemma has_mem.mem.out {α : Type*} {p : α → Prop} {x} (h : x ∈ {y | p y}) : p x :=
h

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

namespace set
variables {α β : Type*}

lemma ord_connected.interval_oc_subset {α : Type*} [linear_order α] {a b : α} {s : set α}
  (hs : ord_connected s) (ha : a ∈ s) (hb : b ∈ s) : Ι a b ⊆ s :=
Ioc_subset_Icc_self.trans $ hs.interval_subset ha hb

lemma ord_connected_interval_oc {α : Type*} [linear_order α] {a b : α} :
  ord_connected (Ι a b) :=
ord_connected_Ioc

lemma Ioc_subset_interval_oc_self {α : Type*} [linear_order α] {a b : α} :
  Ioc a b ⊆ interval_oc a b :=
Ioc_subset_Ioc (min_le_left a b) (le_max_right a b)

/- near `set.Iic_union_Ici` -/
lemma Iic_union_Ici_of_ge {α : Type*} [linear_order α] {a b : α} (h : b ≤ a) :
  Iic a ∪ Ici b = univ :=
eq_univ_of_forall $ λ x, (le_total x a).imp id $ le_trans h

/- to data.set.finite -/
lemma finite_of_finite_preimage {s : set β} {f : α → β} (h : finite (f ⁻¹' s))
  (hs : s ⊆ range f) : finite s :=
by { rw [← image_preimage_eq_of_subset hs], exact finite.image f h }

@[simp] lemma diag_preimage_prod (s t : set α) :
  (λ a, (a, a)) ⁻¹' (s ×ˢ t) = s ∩ t :=
rfl

@[simp] lemma diag_preimage_prod_self (s : set α) :
  (λ a, (a, a)) ⁻¹' (s ×ˢ s) = s :=
s.inter_self

end set
