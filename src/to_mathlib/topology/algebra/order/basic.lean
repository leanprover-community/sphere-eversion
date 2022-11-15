import topology.algebra.order.basic

open_locale topological_space
open filter set

variables {α : Type*}  [linear_order α] [no_max_order α] [no_min_order α]
  [topological_space α] [order_topology α]

-- TODO: golf the next proof

lemma has_basis_nhds_set_Iic (a : α) : (𝓝ˢ $ Iic a).has_basis (λ b, a < b) (λ b, Iio b) :=
⟨begin
  intros u,
  rw [mem_nhds_set_iff_forall],
  simp only [mem_Iic, exists_prop],
  split,
  { intros h,
    have : ∀ x ≤ a, ∃ p : α × α, x ∈ Ioo p.1 p.2 ∧ Ioo p.1 p.2 ⊆ u,
    { intros x hx,
      rcases (nhds_basis_Ioo x).mem_iff.mp (h x hx) with ⟨⟨c, d⟩, ⟨hc, hd⟩, H⟩,
      exact ⟨(c, d), ⟨hc, hd⟩, H⟩ },
    choose! p hp using this,
    rcases (nhds_basis_Ioo a).mem_iff.mp (h a le_rfl) with ⟨⟨c, d⟩, ⟨hc, hd⟩, H⟩,
    dsimp only at H hc hd,
    use [d, hd],
    rintros x (hx : x < d),
    cases le_or_lt x c with hx' hx',
    { cases hp x (hx'.trans hc.le) with H H',
      exact H' H },
    { exact H ⟨hx', hx⟩ }, },
  { rintros ⟨b, hb, hb'⟩ x hx,
    apply mem_of_superset _ hb',
    apply Iio_mem_nhds (hx.trans_lt hb) }
end⟩

lemma has_basis_nhds_set_Iic' [densely_ordered α] (a : α) : (𝓝ˢ $ Iic a).has_basis (λ b, a < b) (λ b, Iic b) :=
⟨λ u, begin
  rw (has_basis_nhds_set_Iic a).mem_iff,
  dsimp only,
  split; rintro ⟨b, hb, hb'⟩,
  { rcases exists_between hb with ⟨c, hc, hc'⟩,
    exact ⟨c, hc, subset_trans (Iic_subset_Iio.mpr hc') hb'⟩ },
  { exact ⟨b, hb, Iio_subset_Iic_self.trans hb'⟩ }
end⟩

lemma has_basis_nhds_set_Ici (a : α) : (𝓝ˢ $ Ici a).has_basis (λ b, b < a) (λ b, Ioi b) :=
@has_basis_nhds_set_Iic (order_dual α) _ _ _ _ _ _

lemma has_basis_nhds_set_Ici' [densely_ordered α] (a : α) : (𝓝ˢ $ Ici a).has_basis (λ b, b < a) (λ b, Ici b) :=
@has_basis_nhds_set_Iic' (order_dual α) _ _ _ _ _ _ _
