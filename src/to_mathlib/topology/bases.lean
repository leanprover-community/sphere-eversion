import topology.bases

open_locale filter topological_space

instance topological_space.prod.first_countable_topology (α : Type*) [t : topological_space α]
  {β : Type*} [topological_space β]
  [topological_space.first_countable_topology α] [topological_space.first_countable_topology β] :
    topological_space.first_countable_topology (α × β) :=
⟨begin
  rintros ⟨a, b⟩,
  rw nhds_prod_eq,
  apply_instance
end⟩
