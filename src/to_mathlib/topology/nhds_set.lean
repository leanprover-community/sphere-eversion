import topology.basic
import topology.separation

open set filter
open_locale topological_space filter

variables {α : Type*} [topological_space α]

lemma is_open.mem_nhds_iff {a : α} {s : set α} (hs : is_open s) : s ∈ 𝓝 a ↔ a ∈ s :=
⟨mem_of_mem_nhds, λ ha, mem_nhds_iff.2 ⟨s, subset.refl _, hs, ha⟩⟩

lemma compl_singleton_mem_nhds_iff [t1_space α] {x y : α} : {x}ᶜ ∈ 𝓝 y ↔ y ≠ x :=
is_open_compl_singleton.mem_nhds_iff

variables {X : Type*} [topological_space X] {U s t s₁ s₂ t₁ t₂ : set X} {x : X}

-- to set/basic
lemma forall_mem_image {α β} {f : α → β} {s : set α} {p : β → Prop} :
  (∀ y ∈ f '' s, p y) ↔ (∀ x ∈ s, p (f x)) :=
by simp only [mem_image, and_imp, forall_exists_index, forall_apply_eq_imp_iff₂]

-- to topology/basic
lemma subset_interior_iff {s t : set X} : t ⊆ interior s ↔ ∃ U, is_open U ∧ t ⊆ U ∧ U ⊆ s :=
⟨λ h, ⟨interior s, is_open_interior, h, interior_subset⟩,
  λ ⟨U, hU, htU, hUs⟩, htU.trans (interior_maximal hUs hU)⟩

lemma interior_eq_univ {s : set X} : interior s = univ ↔ s = univ :=
⟨λ h, univ_subset_iff.mp $ h.symm.trans_le interior_subset, λ h, h.symm ▸ interior_univ⟩

/-- The filter of neighborhoods of a set in a topological space. -/
def nhds_set (s : set X) : filter X :=
Sup (nhds '' s)

localized "notation `𝓝ˢ` := nhds_set" in topological_space

lemma mem_nhds_set_iff : U ∈ 𝓝ˢ s ↔ ∀ (x : X), x ∈ s → U ∈ 𝓝 x :=
by simp_rw [nhds_set, filter.mem_Sup, forall_mem_image]

lemma subset_interior_iff_mem_nhds_set : s ⊆ interior U ↔ U ∈ 𝓝ˢ s :=
by simp_rw [mem_nhds_set_iff, subset_interior_iff_nhds]

lemma mem_nhds_set : s ∈ 𝓝ˢ t ↔ ∃ U, is_open U ∧ t ⊆ U ∧ U ⊆ s :=
by { rw [← subset_interior_iff_mem_nhds_set, subset_interior_iff] }

lemma is_open.mem_nhds_set (hU : is_open U) : U ∈ 𝓝ˢ s ↔ s ⊆ U :=
by rw [← subset_interior_iff_mem_nhds_set, interior_eq_iff_open.mpr hU]

@[simp] lemma nhds_set_singleton : 𝓝ˢ {x} = 𝓝 x :=
by { ext,
     rw [← subset_interior_iff_mem_nhds_set, ← mem_interior_iff_mem_nhds, singleton_subset_iff] }

lemma mem_nhds_set_interior : s ∈ 𝓝ˢ (interior s) :=
subset_interior_iff_mem_nhds_set.mp subset.rfl

lemma mem_nhds_set_empty : U ∈ 𝓝ˢ (∅ : set X) :=
subset_interior_iff_mem_nhds_set.mp $ empty_subset _

lemma nhds_set_empty : 𝓝ˢ (∅ : set X) = ⊥ :=
by { ext, simp [mem_nhds_set_empty] }

lemma nhds_set_univ : 𝓝ˢ (univ : set X) = ⊤ :=
by { ext, rw [← subset_interior_iff_mem_nhds_set, univ_subset_iff, interior_eq_univ, mem_top] }

lemma monotone_nhds_set : monotone (𝓝ˢ : set X → filter X) :=
by { intros s t hst O, simp_rw [← subset_interior_iff_mem_nhds_set], exact subset.trans hst }

lemma union_mem_nhds_set (h₁ : s₁ ∈ 𝓝ˢ t₁) (h₂ : s₂ ∈ 𝓝ˢ t₂) : s₁ ∪ s₂ ∈ 𝓝ˢ (t₁ ∪ t₂) :=
begin
  rw [← subset_interior_iff_mem_nhds_set] at *,
  exact union_subset
    (h₁.trans $ interior_mono $ subset_union_left _ _)
    (h₂.trans $ interior_mono $ subset_union_right _ _)
end

lemma compl_singleton_mem_nhds_set_iff [t1_space α] {x : α} {s : set α} :
  {x}ᶜ ∈ 𝓝ˢ s ↔ x ∉ s :=
by rwa [is_open_compl_singleton.mem_nhds_set, subset_compl_singleton_iff]

@[simp] lemma nhds_set_le_iff [t1_space X] : 𝓝ˢ s ≤ 𝓝ˢ t ↔ s ⊆ t :=
begin
  refine ⟨_, λ h, monotone_nhds_set h⟩,
  simp_rw [filter.le_def], intros h x hx,
  specialize h {x}ᶜ,
  simp_rw [compl_singleton_mem_nhds_set_iff] at h,
  by_contra hxt,
  exact h hxt hx,
end

@[simp] lemma nhds_set_congr [t1_space X] : 𝓝ˢ s = 𝓝ˢ t ↔ s = t :=
by { simp_rw [le_antisymm_iff], exact and_congr nhds_set_le_iff nhds_set_le_iff }

@[simp] lemma nhds_le_nhds_set [t1_space X] : 𝓝 x ≤ 𝓝ˢ s ↔ x ∈ s :=
by rw [← nhds_set_singleton, nhds_set_le_iff, singleton_subset_iff]
