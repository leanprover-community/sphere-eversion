import topology.basic

open set

variables {X : Type*} [topological_space X]

/-- The filter of neighborhoods of a set in a topological space. -/
def nhds_set (s : set X) : filter X :=
Sup (nhds '' s)

lemma mem_nhds_set {s t : set X} : s ∈ nhds_set t ↔
  ∃ U, is_open U ∧ t ⊆ U ∧ U ⊆ s :=
begin
  simp only [nhds_set, filter.mem_Sup, forall_apply_eq_imp_iff₂, mem_image, and_imp,
    exists_prop, forall_exists_index, mem_nhds_iff],
  split,
  { intros h, choose f h1f h2f h3f using h,
    refine ⟨⋃ (x : X) (h : x ∈ t), f x h, _, _, _⟩,
    { exact is_open_Union (λ x, is_open_Union (h2f x)) },
    { intros x hxt, simp only [mem_Union], exact ⟨x, hxt, h3f x hxt⟩ },
    { simpa only [Union_subset_iff] } },
  { rintro ⟨U, hU, htU, hUs⟩ x hxt, exact ⟨U, hUs, hU, htU hxt⟩ }
end

lemma is_open.mem_nhds_set {U s : set X} (hU : is_open U) : U ∈ nhds_set s ↔ s ⊆ U :=
begin
  rw [mem_nhds_set], split,
  { rintro ⟨V, hV, htV, hVU⟩, exact htV.trans hVU },
  { intro hsU, exact ⟨U, hU, hsU, subset.rfl⟩ }
end
