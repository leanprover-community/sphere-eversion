import Mathlib.Topology.Separation.Hausdorff

theorem t2Space_iff_of_isOpenQuotientMap {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] {π : α → β} (h : IsOpenQuotientMap π) :
    T2Space β ↔ IsClosed {q : α × α | π q.1 = π q.2} := by
  rw [t2_iff_isClosed_diagonal]
  replace h := IsOpenQuotientMap.prodMap h h
  constructor <;> intro H
  · exact H.preimage h.continuous
  · simp_rw [← isOpen_compl_iff] at H ⊢
    convert h.isOpenMap _ H
    exact (h.surjective.image_preimage _).symm
