import Mathlib.Topology.NhdsSet
import Mathlib.Topology.Constructions

variable {α : Type _} [TopologicalSpace α] {s t s₁ s₂ t₁ t₂ : Set α} {x : α}

open Filter

open scoped Filter Topology

theorem IsOpen.nhdsSet_eq_principal {s : Set α} (h : IsOpen s) : 𝓝ˢ s = 𝓟 s := by
  apply le_antisymm _ principal_le_nhdsSet
  rw [Filter.le_principal_iff, h.mem_nhdsSet]

theorem IsOpen.forall_near_mem_of_subset {s t : Set α} (h : IsOpen s) (ht : t ⊆ s) :
    ∀ᶠ x in 𝓝ˢ t, x ∈ s := by
  apply Eventually.filter_mono (nhdsSet_mono ht)
  rw [h.nhdsSet_eq_principal, eventually_principal]
  exact fun x => id

/-
In the next lemma, the inequality cannot be improved to an equality. For instance,
if α has two elements and the coarse topology and s and t are distinct singletons then
𝓝ˢ (s ∩ t) = ⊥ while 𝓝ˢ s ⊓ 𝓝ˢ t = ⊤ and those are different.
-/
theorem nhdsSet_inter_le (s t : Set α) : 𝓝ˢ (s ∩ t) ≤ 𝓝ˢ s ⊓ 𝓝ˢ t :=
  (@monotone_nhdsSet α _).map_inf_le s t

theorem sup_sSup {α : Type _} [CompleteLattice α] {s : Set α} {a : α} :
    a ⊔ sSup s = sSup (s ∪ {a}) := by simp only [Set.union_singleton, sSup_insert]

theorem sSup_sup {α : Type _} [CompleteLattice α] {s : Set α} {a : α} :
    sSup s ⊔ a = sSup (s ∪ {a}) := by simp only [sup_sSup, sup_comm]

theorem IsClosed.nhdsSet_le_sup {t : Set α} (h : IsClosed t) (s : Set α) :
    𝓝ˢ s ≤ 𝓝ˢ (s ∩ t) ⊔ 𝓟 (tᶜ) :=
  calc
    𝓝ˢ s = 𝓝ˢ (s ∩ t ∪ s ∩ tᶜ) := by rw [Set.inter_union_compl s t]
    _ = 𝓝ˢ (s ∩ t) ⊔ 𝓝ˢ (s ∩ tᶜ) := by rw [nhdsSet_union]
    _ ≤ 𝓝ˢ (s ∩ t) ⊔ 𝓝ˢ (tᶜ) := (sup_le_sup_left (monotone_nhdsSet (s.inter_subset_right (tᶜ))) _)
    _ = 𝓝ˢ (s ∩ t) ⊔ 𝓟 (tᶜ) := by rw [h.isOpen_compl.nhdsSet_eq_principal]

theorem IsClosed.nhdsSet_le_sup' {t : Set α} (h : IsClosed t) (s : Set α) :
    𝓝ˢ s ≤ 𝓝ˢ (t ∩ s) ⊔ 𝓟 (tᶜ) := by rw [Set.inter_comm]; exact h.nhdsSet_le_sup s

theorem eventually_nhdsSet_iff {p : α → Prop} : (∀ᶠ x in 𝓝ˢ s, p x) ↔ ∀ x ∈ s, ∀ᶠ y in 𝓝 x, p y :=
  by rw [nhdsSet, eventually_sSup, Set.ball_image_iff]

theorem Filter.Eventually.eventually_nhdsSet {p : α → Prop} (h : ∀ᶠ y in 𝓝ˢ s, p y) :
    ∀ᶠ y in 𝓝ˢ s, ∀ᶠ x in 𝓝 y, p x :=
  eventually_nhdsSet_iff.mpr fun x x_in => (eventually_nhdsSet_iff.mp h x x_in).eventually_nhds

theorem Filter.Eventually.on_set {p : α → Prop} (h : ∀ᶠ y in 𝓝ˢ s, p y) : ∀ x ∈ s, p x :=
  eventually_principal.mp <| Eventually.filter_mono principal_le_nhdsSet h

theorem Filter.eventually_nhdsSet_union {p : α → Prop} :
    (∀ᶠ x in 𝓝ˢ (s ∪ t), p x) ↔ (∀ᶠ x in 𝓝ˢ s, p x) ∧ ∀ᶠ x in 𝓝ˢ t, p x := by
  rw [nhdsSet_union, eventually_sup]

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem Filter.nhdsSet_prod_le_prod {α β : Type _} [TopologicalSpace α] [TopologicalSpace β]
    {s : Set α} {t : Set β} : 𝓝ˢ (s ×ˢ t) ≤ 𝓝ˢ s ×ˢ 𝓝ˢ t := by
  apply sSup_le _
  rintro f ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩ U hU
  simp only [mem_nhdsSet_iff_forall, nhds_prod_eq, mem_prod_iff] at *
  rcases hU with ⟨V, V_in, W, W_in, hVW⟩
  exact ⟨V, V_in x hx, W, W_in y hy, hVW⟩

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem Filter.eventually_nhdsSet_prod_iff {α β : Type _} [TopologicalSpace α] [TopologicalSpace β]
    {p : α × β → Prop} {s : Set α} {t : Set β} :
    (∀ᶠ q in 𝓝ˢ (s ×ˢ t), p q) ↔
      ∀ x ∈ s, ∀ y ∈ t,
          ∃ pa : α → Prop, (∀ᶠ x' in 𝓝 x, pa x') ∧ ∃ pb : β → Prop, (∀ᶠ y' in 𝓝 y, pb y') ∧
            ∀ {x : α}, pa x → ∀ {y : β}, pb y → p (x, y) :=
  by simp_rw [eventually_nhdsSet_iff, Set.forall_prod_set, nhds_prod_eq, eventually_prod_iff]

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem Filter.eventually_nhdsSet_of_prod {α β : Type _} [TopologicalSpace α] [TopologicalSpace β]
    {p : α × β → Prop} {pa : α → Prop} {pb : β → Prop}
    (hp : ∀ {x : α}, pa x → ∀ {y : β}, pb y → p (x, y)) {s : Set α} {t : Set β}
    (hs : ∀ᶠ x in 𝓝ˢ s, pa x) (ht : ∀ᶠ y in 𝓝ˢ t, pb y) : ∀ᶠ q in 𝓝ˢ (s ×ˢ t), p q := by
  apply Filter.nhdsSet_prod_le_prod
  apply mem_of_superset (prod_mem_prod hs ht)
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  exact hp hx hy

theorem Filter.Eventually.union {p : α → Prop} (hs : ∀ᶠ x in 𝓝ˢ s, p x) (ht : ∀ᶠ x in 𝓝ˢ t, p x) :
    ∀ᶠ x in 𝓝ˢ (s ∪ t), p x :=
  Filter.eventually_nhdsSet_union.mpr ⟨hs, ht⟩

theorem eventually_nhdsSet_iUnion₂ {α ι : Type _} [TopologicalSpace α] {p : ι → Prop}
    {s : ι → Set α} {P : α → Prop} :
    (∀ᶠ x in 𝓝ˢ (⋃ (i) (_ : p i), s i), P x) ↔ ∀ i, p i → ∀ᶠ x in 𝓝ˢ (s i), P x := by
  simp_rw [eventually_nhdsSet_iff, Set.mem_iUnion₂]
  constructor
  exact fun h i hi x hx => h x ⟨i, hi, hx⟩
  rintro h x ⟨i, hi, hx⟩
  exact h i hi x hx

theorem eventually_nhdsSet_iUnion {α ι : Type _} [TopologicalSpace α] {s : ι → Set α}
    {P : α → Prop} : (∀ᶠ x in 𝓝ˢ (⋃ i, s i), P x) ↔ ∀ i, ∀ᶠ x in 𝓝ˢ (s i), P x := by
  simpa using @eventually_nhdsSet_iUnion₂ _ _ _ (fun _ => True) s P

-- This lemma goes to filter.basic, after filter.eventually_principal
theorem Filter.Eventually.forall_mem {α : Type _} {f : Filter α} {s : Set α} {P : α → Prop}
    (hP : ∀ᶠ x in f, P x) (hf : 𝓟 s ≤ f) : ∀ x ∈ s, P x :=
  Filter.eventually_principal.mp (hP.filter_mono hf)

theorem Filter.Eventually.nhdsSet_forall_mem {α : Type _} [TopologicalSpace α] {s : Set α}
    {P : α → Prop} (hP : ∀ᶠ x in nhdsSet s, P x) : ∀ x ∈ s, P x :=
  hP.forall_mem principal_le_nhdsSet

theorem subset_of_mem_nhdsSet {α : Type _} [TopologicalSpace α] {s t : Set α} (h : t ∈ 𝓝ˢ s) :
    s ⊆ t := fun x hx => mem_of_mem_nhds <| mem_nhdsSet_iff_forall.mp h x hx
