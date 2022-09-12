import geometry.manifold.charted_space
import to_mathlib.topology.local_homeomorph

namespace charted_space

open set

variables (H : Type*) (M : Type*) [topological_space H] [topological_space M] [charted_space H M]

@[simp] lemma Union_source_eq_univ : (⋃ (x : M), (chart_at H x).source) = (univ : set M) :=
eq_univ_iff_forall.mpr (λ x, mem_Union.mpr ⟨x, mem_chart_source H x⟩)

variables {M}

lemma is_open_iff (s : set M) :
  is_open s ↔ ∀ (x : M), is_open $ chart_at H x '' ((chart_at H x).source ∩ s) :=
begin
  refine ⟨λ h x, (chart_at H x).image_open_of_open' h, λ h, _⟩,
  rw [← s.inter_univ, ← Union_source_eq_univ H M, s.inter_Union],
  refine is_open_Union (λ x, _),
  have : s ∩ (chart_at H x).source ⊆ (chart_at H x).source := inter_subset_right _ _,
  rw [(chart_at H x).is_open_image_iff_of_subset_source this, inter_comm],
  exact h x,
end

end charted_space
