import data.set.prod

open set

namespace set

lemma univ_prod_inter_univ_prod {α β : Type*} {s t : set β} :
  (univ : set α) ×ˢ s ∩ (univ : set α) ×ˢ t = (univ : set α) ×ˢ (s ∩ t) :=
begin
  ext ⟨a, b⟩,
  simp
end

@[simp] lemma univ_prod_nonempty_iff {α β : Type*} [nonempty α] {s : set β} :
  ((univ : set α) ×ˢ s).nonempty ↔ s.nonempty :=
begin
  inhabit α,
  split,
  { rintro ⟨⟨-, b⟩, ⟨-, h : b ∈ s⟩⟩,
    exact ⟨b, h⟩ },
  { rintro ⟨b, h⟩,
    exact ⟨⟨default, b⟩, ⟨trivial, h⟩⟩ }
end

end set
