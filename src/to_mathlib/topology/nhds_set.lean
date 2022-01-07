import topology.basic

open set

variables {X : Type*} [topological_space X]

-- to set/basic
lemma forall_mem_image {α β} {f : α → β} {s : set α} {p : β → Prop} :
  (∀ y ∈ f '' s, p y) ↔ (∀ x ∈ s, p (f x)) :=
by simp only [mem_image, and_imp, forall_exists_index, forall_apply_eq_imp_iff₂]

lemma subset_interior_iff {s t : set X} : t ⊆ interior s ↔ ∃ U, is_open U ∧ t ⊆ U ∧ U ⊆ s :=
⟨λ h, ⟨interior s, is_open_interior, h, interior_subset⟩,
  λ ⟨U, hU, htU, hUs⟩, htU.trans (interior_maximal hUs hU)⟩

/-- The filter of neighborhoods of a set in a topological space. -/
def nhds_set (s : set X) : filter X :=
Sup (nhds '' s)

lemma subset_interior_iff_mem_nhds_set {U s : set X} : s ⊆ interior U ↔ U ∈ nhds_set s :=
by simp_rw [nhds_set, filter.mem_Sup, forall_mem_image, subset_interior_iff_nhds]

lemma mem_nhds_set {s t : set X} : s ∈ nhds_set t ↔ ∃ U, is_open U ∧ t ⊆ U ∧ U ⊆ s :=
by { rw [← subset_interior_iff_mem_nhds_set, subset_interior_iff] }

lemma is_open.mem_nhds_set {U s : set X} (hU : is_open U) : U ∈ nhds_set s ↔ s ⊆ U :=
by rw [← subset_interior_iff_mem_nhds_set, interior_eq_iff_open.mpr hU]
