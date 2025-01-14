import Mathlib.Topology.Separation.Hausdorff
open Set Function

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-
TODO? State a specialized version for quotient maps? Note the open map assumption is still
a separate assumption there, because there is no `QuotientMap.prod_map`.
-/
theorem t2Space_iff_of_continuous_surjective_open {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] {π : α → β} (hcont : Continuous π) (hsurj : Surjective π)
    (hop : IsOpenMap π) : T2Space β ↔ IsClosed {q : α × α | π q.1 = π q.2} := by
  rw [t2_iff_isClosed_diagonal]
  constructor <;> intro H
  · exact H.preimage (hcont.prodMap hcont)
  · simp_rw [← isOpen_compl_iff] at H ⊢
    convert hop.prodMap hop _ H
    exact ((hsurj.prodMap hsurj).image_preimage _).symm
