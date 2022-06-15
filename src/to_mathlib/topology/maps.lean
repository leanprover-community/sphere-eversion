import topology.maps

open set
open_locale topological_space

variables {α β : Type*} [topological_space α] [topological_space β]

lemma is_open_map.range_mem_nhds
  {f : α → β} (hf : is_open_map f) (x : α) :
  range f ∈ 𝓝 (f x) :=
mem_nhds_iff.mpr ⟨range f, subset.rfl, hf.is_open_range, mem_range_self x⟩
-- by { rw ← image_univ, exact hf.image_mem_nhds filter.univ_mem, }
