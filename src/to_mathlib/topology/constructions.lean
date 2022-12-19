import topology.constructions

open set function filter
open_locale topological_space filter

universe u
variables {ι : Type u} {X Y : Type*} [topological_space X] [topological_space Y]

-- This needs to go into topology.constructions which imports locally_finite and defines the
-- product topology.
lemma locally_finite.prod_right {f : ι → set X} (hf : locally_finite f) (g : ι → set Y) :
  locally_finite (λ i, f i ×ˢ g i) :=
begin
  rintros ⟨x, y⟩,
  rcases hf x with ⟨U, U_in, hU⟩,
  refine ⟨U ×ˢ univ, prod_mem_nhds U_in univ_mem, _⟩,
  apply finite.subset hU,
  rintros i ⟨⟨x', y'⟩, ⟨⟨H, -⟩, ⟨H', -⟩⟩⟩,
  exact ⟨x', H, H'⟩
end

lemma locally_finite.prod_left {f : ι → set X} (hf : locally_finite f) (g : ι → set Y) :
  locally_finite (λ i, g i ×ˢ f i) :=
begin
  rintros ⟨y, x⟩,
  rcases hf x with ⟨U, U_in, hU⟩,
  refine ⟨univ ×ˢ U, prod_mem_nhds univ_mem U_in, _⟩,
  apply finite.subset hU,
  rintros i ⟨⟨y', x'⟩, ⟨⟨-, H⟩, ⟨-, H'⟩⟩⟩,
  exact ⟨x', H, H'⟩
end
