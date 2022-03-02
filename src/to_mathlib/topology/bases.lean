import topology.bases

open_locale filter topological_space

namespace filter
-- Next one should go to order.filter.bases after has_countable_basis.is_countably_generated
instance is_countably_generated_prod {α β : Type*} (f : filter α) (g : filter β)
  [is_countably_generated f] [is_countably_generated g] : is_countably_generated (f ×ᶠ g) :=
begin
  rcases f.exists_antitone_basis with ⟨s, hs⟩,
  rcases g.exists_antitone_basis with ⟨t, ht⟩,
  exact has_countable_basis.is_countably_generated ⟨hs.1.prod ht.1, set.countable_encodable _⟩
end
end filter

instance topological_space.prod.first_countable_topology (α : Type*) [t : topological_space α]
  {β : Type*} [topological_space β]
  [topological_space.first_countable_topology α] [topological_space.first_countable_topology β] :
    topological_space.first_countable_topology (α × β) :=
⟨begin
  rintros ⟨a, b⟩,
  rw nhds_prod_eq,
  apply_instance
end⟩
