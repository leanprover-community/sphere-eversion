import topology.locally_finite

open function set

lemma locally_finite.smul_left {ι : Type*} {α : Type*} [topological_space α] {M : Type*}
  {R : Type*} [semiring R] [add_comm_monoid M] [module R M] [no_zero_smul_divisors R M]
  {s : ι → α → R} (h : locally_finite $ λ i, support $ s i) (f : ι → α → M) :
  locally_finite (λ i, support $ s i • f i) :=
begin
  apply h.subset (λ i, _),
  rw support_smul,
  exact inter_subset_left _ _
end

lemma locally_finite.smul_right {ι : Type*} {α : Type*} [topological_space α] {M : Type*}
  {R : Type*} [semiring R] [add_comm_monoid M] [module R M] [no_zero_smul_divisors R M]
   {f : ι → α → M} (h : locally_finite $ λ i, support $ f i) (s : ι → α → R) :
  locally_finite (λ i, support $ s i • f i) :=
begin
  apply h.subset (λ i, _),
  rw support_smul,
  exact inter_subset_right _ _
end

section
variables {ι X : Type*} [topological_space X]

@[to_additive]
lemma locally_finite.exists_finset_mul_support_eq {M : Type*} [comm_monoid M] {ρ : ι → X → M}
  (hρ : locally_finite (λ i, mul_support $ ρ i)) (x₀ : X) :
  ∃ I : finset ι, mul_support (λ i, ρ i x₀) = I :=
begin
  use (hρ.point_finite x₀).to_finset,
  rw [finite.coe_to_finset],
  refl
end

end

open_locale topological_space
open filter

lemma locally_finite.eventually_subset {ι X : Type*} [topological_space X] {s : ι → set X}
(hs : locally_finite s) (hs' : ∀ i, is_closed (s i)) (x : X) :
∀ᶠ y in 𝓝 x, {i | y ∈ s i} ⊆ {i | x ∈ s i} :=
begin
  apply mem_of_superset (hs.Inter_compl_mem_nhds hs' x),
  intros y hy i hi,
  simp only [mem_Inter, mem_compl_iff] at hy,
  exact not_imp_not.mp (hy i) hi
end
