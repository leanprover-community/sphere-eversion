import topology.algebra.order.compact
import topology.instances.real

/-- A variant of `is_compact.exists_forall_le` for real-valued functions that does not require the
assumption `s.nonempty`. -/
lemma is_compact.exists_forall_le' {β : Type*} [topological_space β]
  {s : set β} (hs : is_compact s)
  {f : β → ℝ} (hf : continuous_on f s) {a : ℝ} (hf' : ∀ b ∈ s, a < f b) :
  ∃ a', a < a' ∧ ∀ b ∈ s, a' ≤ f b :=
begin
  rcases s.eq_empty_or_nonempty with rfl | hs',
  { exact ⟨a + 1, by simp only [lt_add_iff_pos_right, zero_lt_one], λ b hb, by simpa using hb⟩, },
  { obtain ⟨x, hx, hx'⟩ := hs.exists_forall_le hs' hf,
    exact ⟨f x, hf' x hx, hx'⟩, },
end
