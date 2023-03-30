import data.set.lattice

namespace set
variables {α β : Type*} {ι : Sort*}

-- Put next to Union_prod_const...
lemma const_prod_Union {s : ι → set α} {t : set β} : t ×ˢ (⋃ i, s i) = ⋃ i, t ×ˢ s i :=
by { ext, simp }

-- Put next to Union₂_prod_const...
lemma const_prod_Union₂ {κ : ι → Sort*} {s : Π i, κ i → set α} {t : set β} :
  t ×ˢ (⋃ i j, s i j) = ⋃ i j, t ×ˢ s i j :=
by simp_rw [const_prod_Union]

lemma bUnion_le {α ι : Type*} [partial_order ι] (s : ι → set α) (i : ι) :
  (⋃ j ≤ i, s j) = (⋃ j < i, s j) ∪ s i :=
begin
  simp only [(λ j, le_iff_lt_or_eq : ∀ j, j ≤ i ↔ j < i ∨ j = i)],
  erw [bUnion_union, bUnion_singleton],
  refl
end

lemma bUnion_ge {α ι : Type*} [partial_order ι] (s : ι → set α) (i : ι) :
  (⋃ j ≥ i, s j) = s i ∪ (⋃ j > i, s j) :=
begin
  erw [@bUnion_le α (order_dual ι) _ s i, union_comm],
  refl
end

end set
