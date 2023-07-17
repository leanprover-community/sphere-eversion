import Mathbin.Topology.Algebra.Order.Compact
import Mathbin.Topology.Instances.Real

/-- A variant of `is_compact.exists_forall_le` for real-valued functions that does not require the
assumption `s.nonempty`. -/
theorem IsCompact.exists_forall_le' {β : Type _} [TopologicalSpace β] {s : Set β} (hs : IsCompact s)
    {f : β → ℝ} (hf : ContinuousOn f s) {a : ℝ} (hf' : ∀ b ∈ s, a < f b) :
    ∃ a', a < a' ∧ ∀ b ∈ s, a' ≤ f b :=
  by
  rcases s.eq_empty_or_nonempty with (rfl | hs')
  · exact ⟨a + 1, by simp only [lt_add_iff_pos_right, zero_lt_one], fun b hb => by simpa using hb⟩
  · obtain ⟨x, hx, hx'⟩ := hs.exists_forall_le hs' hf
    exact ⟨f x, hf' x hx, hx'⟩

