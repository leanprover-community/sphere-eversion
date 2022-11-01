import topology.nhds_set

variables {α : Type*} [topological_space α] {s t s₁ s₂ t₁ t₂ : set α} {x : α}

open filter
open_locale filter topological_space

lemma is_open.nhds_set_eq_principal {s : set α} (h : is_open s) : 𝓝ˢ s = 𝓟 s :=
begin
  apply le_antisymm _ principal_le_nhds_set,
  rw [filter.le_principal_iff, h.mem_nhds_set]
end

lemma is_open.forall_near_mem_of_subset {s t : set α} (h : is_open s) (ht : t ⊆ s) : ∀ᶠ x in 𝓝ˢ t, x ∈ s :=
begin
  apply eventually.filter_mono (nhds_set_mono ht),
  rw [h.nhds_set_eq_principal, eventually_principal],
  exact λ x, id
end

/-
In the next lemma, the inequality cannot be improved to an equality. For instance,
if α has two elements and the coarse topology and s and t are distinct singletons then
𝓝ˢ (s ∩ t) = ⊥ while 𝓝ˢ s ⊓ 𝓝ˢ t = ⊤ and those are different.
-/
lemma nhds_set_inter_le (s t : set α) : 𝓝ˢ (s ∩ t) ≤  𝓝ˢ s ⊓ 𝓝ˢ t :=
(@monotone_nhds_set α _).map_inf_le s t

lemma sup_Sup {α : Type*} [complete_lattice α] {s : set α} {a : α} : a ⊔ (Sup s) = Sup (s ∪ {a}) :=
by simp only [set.union_singleton, Sup_insert]

lemma Sup_sup {α : Type*} [complete_lattice α] {s : set α} {a : α} : (Sup s) ⊔ a = Sup (s ∪ {a}) :=
by simp only [sup_Sup, sup_comm]

lemma is_closed.nhds_set_le_sup {t : set α} (h : is_closed t) (s : set α) :
  𝓝ˢ s ≤ 𝓝ˢ (s ∩ t) ⊔ 𝓟 tᶜ :=
calc 𝓝ˢ s = 𝓝ˢ ((s ∩ t) ∪ (s ∩ tᶜ)) : by rw set.inter_union_compl s t
... = 𝓝ˢ (s ∩ t) ⊔ 𝓝ˢ (s ∩ tᶜ) : by rw nhds_set_union
... ≤ 𝓝ˢ (s ∩ t) ⊔ 𝓝ˢ tᶜ : sup_le_sup_left (monotone_nhds_set (s.inter_subset_right tᶜ)) _
... = 𝓝ˢ (s ∩ t) ⊔ 𝓟 tᶜ : by rw (is_open_compl_iff.mpr h).nhds_set_eq_principal

lemma is_closed.nhds_set_le_sup' {t : set α} (h : is_closed t) (s : set α) :
  𝓝ˢ s ≤ 𝓝ˢ (t ∩ s) ⊔ 𝓟 tᶜ :=
by {rw set.inter_comm, exact h.nhds_set_le_sup s }

lemma eventually_nhds_set_iff {p : α → Prop} : (∀ᶠ x in 𝓝ˢ s, p x) ↔ (∀ x ∈ s, ∀ᶠ y in 𝓝 x, p y) :=
by rw [nhds_set, eventually_Sup, set.ball_image_iff]

lemma filter.eventually.eventually_nhds_set {p : α → Prop} (h : ∀ᶠ y in 𝓝ˢ s, p y) :
  ∀ᶠ y in 𝓝ˢ s, ∀ᶠ x in 𝓝 y, p x :=
eventually_nhds_set_iff.mpr (λ x x_in, (eventually_nhds_set_iff.mp h x x_in).eventually_nhds)

lemma filter.eventually.on_set {p : α → Prop} (h : ∀ᶠ y in 𝓝ˢ s, p y) : ∀ x ∈ s, p x :=
eventually_principal.mp $ eventually.filter_mono principal_le_nhds_set h

lemma filter.eventually.union {p : α → Prop} (hs : ∀ᶠ x in 𝓝ˢ s, p x) (ht : ∀ᶠ x in 𝓝ˢ t, p x) :
  ∀ᶠ x in 𝓝ˢ (s ∪ t), p x :=
begin
  rw nhds_set_union,
  exact ⟨hs, ht⟩
end

-- This lemma goes to filter.basic, after filter.eventually_principal
lemma filter.eventually.forall_mem {α : Type*} {f : filter α} {s : set α} {P : α → Prop}
  (hP : ∀ᶠ x in f, P x) (hf : 𝓟 s ≤ f) : ∀ x ∈ s, P x :=
filter.eventually_principal.mp (hP.filter_mono hf)

lemma filter.eventually.nhds_set_forall_mem {α : Type*} [topological_space α]
  {s : set α} {P : α → Prop}
  (hP : ∀ᶠ x in nhds_set s, P x) : ∀ x ∈ s, P x :=
hP.forall_mem principal_le_nhds_set
