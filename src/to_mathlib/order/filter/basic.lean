import order.filter.basic

open set

namespace filter

variables {α : Type*} {f : filter α}

lemma exists_mem_and_iff {P : set α → Prop} {Q : set α → Prop} (hP : antitone P) (hQ : antitone Q) :
  (∃ u ∈ f, P u) ∧ (∃ u ∈ f, Q u) ↔ (∃ u ∈ f, P u ∧ Q u) :=
begin
  split,
  { rintro ⟨⟨u, huf, hPu⟩, v, hvf, hQv⟩, exact ⟨u ∩ v, inter_mem huf hvf,
    hP (inter_subset_left _ _) hPu, hQ (inter_subset_right _ _) hQv⟩ },
  { rintro ⟨u, huf, hPu, hQu⟩, exact ⟨⟨u, huf, hPu⟩, u, huf, hQu⟩ }
end

end filter
