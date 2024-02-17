import Mathlib.Topology.Algebra.Order.Compact
import Mathlib.Topology.Instances.Real

-- PRed in #9872
/-- The **extreme value theorem**: a continuous function realizes its minimum on a compact set `s`.
  This variant is for functions into a `NoMaxOrder`, without the assumption `s.Nonempty`. -/
theorem IsCompact.exists_forall_le' {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [LinearOrder α] [ClosedIicTopology α] [NoMaxOrder α] {f : β → α}
    {s : Set β} (hs : IsCompact s) (hf : ContinuousOn f s) {a : α} (hf' : ∀ b ∈ s, a < f b) :
    ∃ a', a < a' ∧ ∀ b ∈ s, a' ≤ f b := by
  rcases s.eq_empty_or_nonempty with (rfl | hs')
  · obtain ⟨a', ha'⟩ := exists_gt a
    exact ⟨a', ha', fun _ a ↦ a.elim⟩
  · obtain ⟨x, hx, hx'⟩ := hs.exists_isMinOn hs' hf
    exact ⟨f x, hf' x hx, hx'⟩
