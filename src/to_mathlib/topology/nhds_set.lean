import topology.basic

open set

variables {X : Type*} [topological_space X] {U s t s₁ s₂ t₁ t₂ : set X}

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

lemma subset_interior_iff_mem_nhds_set : s ⊆ interior U ↔ U ∈ nhds_set s :=
by simp_rw [nhds_set, filter.mem_Sup, forall_mem_image, subset_interior_iff_nhds]

lemma mem_nhds_set : s ∈ nhds_set t ↔ ∃ U, is_open U ∧ t ⊆ U ∧ U ⊆ s :=
by { rw [← subset_interior_iff_mem_nhds_set, subset_interior_iff] }

lemma is_open.mem_nhds_set (hU : is_open U) : U ∈ nhds_set s ↔ s ⊆ U :=
by rw [← subset_interior_iff_mem_nhds_set, interior_eq_iff_open.mpr hU]

lemma mem_nhds_set_empty : U ∈ nhds_set (∅ : set X) :=
subset_interior_iff_mem_nhds_set.mp $ empty_subset _

lemma mem_nhds_interior : s ∈ nhds_set (interior s) :=
subset_interior_iff_mem_nhds_set.mp subset.rfl

lemma nhds_set_empty : nhds_set (∅ : set X) = ⊥ :=
by { ext, simp [mem_nhds_set_empty] }

lemma monotone_nhds_set : monotone (nhds_set : set X → filter X) :=
by { intros s t hst O, simp_rw [← subset_interior_iff_mem_nhds_set], exact subset.trans hst }

lemma union_mem_nhds_set (h₁ : s₁ ∈ nhds_set t₁) (h₂ : s₂ ∈ nhds_set t₂) :
  s₁ ∪ s₂ ∈ nhds_set (t₁ ∪ t₂) :=
begin
  rw [← subset_interior_iff_mem_nhds_set] at *,
  exact union_subset
    (h₁.trans $ interior_mono $ subset_union_left _ _)
    (h₂.trans $ interior_mono $ subset_union_right _ _)
end
