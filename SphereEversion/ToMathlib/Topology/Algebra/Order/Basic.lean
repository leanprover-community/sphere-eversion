import Mathlib.Topology.Order.Basic

open scoped Topology

open Filter Set

variable {α : Type _} [LinearOrder α] [NoMaxOrder α] [NoMinOrder α] [TopologicalSpace α]
  [OrderTopology α]

-- TODO: golf the next proof
theorem hasBasis_nhdsSet_Iic (a : α) : (𝓝ˢ <| Iic a).HasBasis (fun b => a < b) fun b => Iio b :=
  ⟨by
    intro u
    rw [mem_nhdsSet_iff_forall]
    simp only [mem_Iic, exists_prop]
    constructor
    · intro h
      have : ∀ x ≤ a, ∃ p : α × α, x ∈ Ioo p.1 p.2 ∧ Ioo p.1 p.2 ⊆ u :=
        by
        intro x hx
        rcases(nhds_basis_Ioo x).mem_iff.mp (h x hx) with ⟨⟨c, d⟩, ⟨hc, hd⟩, H⟩
        exact ⟨(c, d), ⟨hc, hd⟩, H⟩
      choose! p hp using this
      rcases(nhds_basis_Ioo a).mem_iff.mp (h a le_rfl) with ⟨⟨c, d⟩, ⟨hc, hd⟩, H⟩
      dsimp only at H hc hd
      use d, hd
      rintro x (hx : x < d)
      cases' le_or_lt x c with hx' hx'
      · cases' hp x (hx'.trans hc.le) with H H'
        exact H' H
      · exact H ⟨hx', hx⟩
    · rintro ⟨b, hb, hb'⟩ x hx
      apply mem_of_superset _ hb'
      apply Iio_mem_nhds (hx.trans_lt hb)⟩

theorem hasBasis_nhdsSet_Iic' [DenselyOrdered α] (a : α) :
    (𝓝ˢ <| Iic a).HasBasis (fun b => a < b) fun b => Iic b :=
  ⟨fun u => by
    rw [(hasBasis_nhdsSet_Iic a).mem_iff]
    dsimp only
    constructor <;> rintro ⟨b, hb, hb'⟩
    · rcases exists_between hb with ⟨c, hc, hc'⟩
      exact ⟨c, hc, Subset.trans (Iic_subset_Iio.mpr hc') hb'⟩
    · exact ⟨b, hb, Iio_subset_Iic_self.trans hb'⟩⟩

theorem hasBasis_nhdsSet_Ici (a : α) : (𝓝ˢ <| Ici a).HasBasis (fun b => b < a) fun b => Ioi b :=
  @hasBasis_nhdsSet_Iic (OrderDual α) _ _ _ _ _ _

theorem hasBasis_nhdsSet_Ici' [DenselyOrdered α] (a : α) :
    (𝓝ˢ <| Ici a).HasBasis (fun b => b < a) fun b => Ici b :=
  @hasBasis_nhdsSet_Iic' (OrderDual α) _ _ _ _ _ _ _

