import data.real.nnreal

open real set
open_locale nnreal interval

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

/- to data.set.finite -/
namespace set
variables {α β : Type*}

lemma finite_of_finite_preimage {s : set β} {f : α → β} (h : finite (f ⁻¹' s))
  (hs : s ⊆ range f) : finite s :=
by { rw [← image_preimage_eq_of_subset hs], exact finite.image f h }

end set
