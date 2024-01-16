import Mathlib.Topology.NhdsSet
import Mathlib.Topology.Constructions

variable {α : Type _} [TopologicalSpace α] {s t s₁ s₂ t₁ t₂ : Set α} {x : α}

open Filter

open scoped Filter Topology

theorem IsOpen.forall_near_mem_of_subset {s t : Set α} (h : IsOpen s) (ht : t ⊆ s) :
    ∀ᶠ x in 𝓝ˢ t, x ∈ s :=
  (h.mem_nhdsSet).mpr ht

theorem eventually_nhdsSet_iff {p : α → Prop} : (∀ᶠ x in 𝓝ˢ s, p x) ↔ ∀ x ∈ s, ∀ᶠ y in 𝓝 x, p y :=
  eventually_nhdsSet_iff_forall

theorem Filter.eventually_nhdsSet_union {p : α → Prop} :
    (∀ᶠ x in 𝓝ˢ (s ∪ t), p x) ↔ (∀ᶠ x in 𝓝ˢ s, p x) ∧ ∀ᶠ x in 𝓝ˢ t, p x :=
  Eventually.union_nhdsSet

theorem Filter.nhdsSet_prod_le_prod {α β : Type _} [TopologicalSpace α] [TopologicalSpace β]
    {s : Set α} {t : Set β} : 𝓝ˢ (s ×ˢ t) ≤ 𝓝ˢ s ×ˢ 𝓝ˢ t := nhdsSet_prod_le s t

theorem Filter.eventually_nhdsSet_of_prod {α β : Type _} [TopologicalSpace α] [TopologicalSpace β]
    {p : α × β → Prop} {pa : α → Prop} {pb : β → Prop}
    (hp : ∀ {x : α}, pa x → ∀ {y : β}, pb y → p (x, y)) {s : Set α} {t : Set β}
    (hs : ∀ᶠ x in 𝓝ˢ s, pa x) (ht : ∀ᶠ y in 𝓝ˢ t, pb y) : ∀ᶠ q in 𝓝ˢ (s ×ˢ t), p q :=
  Filter.Eventually.prod_nhdsSet (fun {x} a {y} a_1 ↦ hp a a_1) hs ht

theorem Filter.Eventually.nhdsSet_forall_mem {α : Type _} [TopologicalSpace α] {s : Set α}
    {P : α → Prop} (hP : ∀ᶠ x in nhdsSet s, P x) : ∀ x ∈ s, P x :=
  hP.forall_mem principal_le_nhdsSet
