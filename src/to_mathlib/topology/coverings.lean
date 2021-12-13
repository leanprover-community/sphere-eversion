import topology.paracompact


open set
open_locale topological_space

-- I think that any open set in a finite dimensional real vector space satisfies the assumptions below.
variables {X : Type*} [topological_space X] [locally_compact_space X] [sigma_compact_space X]
  [t2_space X]

lemma foo {P : set X → Prop} (hP : antitone P) (hX : ∀ x : X, ∃ U ∈ 𝓝 x, P U) :
∃ (u : ℕ → set X) (v : ℕ → set X), ∀ n,
  is_compact (u n) ∧ is_open (v n) ∧ P (v n) ∧
  u n ⊆ v n ∧ locally_finite v ∧ (⋃ n, u n) = univ :=
begin
  -- We start with stealing the beginning of 
  -- refinement_of_locally_compact_sigma_compact_of_nhds_basis_set
  -- The proof of that lemma should be read to see what are the technical reasons 
  -- alluded to below.
  classical,
  -- For technical reasons we prepend two empty sets to the sequence `compact_exhaustion.choice X`
  set K' : compact_exhaustion X := compact_exhaustion.choice X,
  set K : compact_exhaustion X := K'.shiftr.shiftr,
  set Kdiff := λ n, K (n + 1) \ interior (K n),
  -- Now we restate some properties of `compact_exhaustion` for `K`/`Kdiff`
  have hKcov : ∀ x, x ∈ Kdiff (K'.find x + 1),
  { intro x,
    simpa only [K'.find_shiftr]
      using diff_subset_diff_right interior_subset (K'.shiftr.mem_diff_shiftr_find x) },
  have Kdiffc : ∀ n, is_compact (Kdiff n),
    from λ n, (K.is_compact _).diff is_open_interior,
  have Kdiff_nhds : ∀ n x,  x ∈ Kdiff (n + 1) → (K n)ᶜ ∈ 𝓝 (x : X),
  { rintros n x ⟨hx, hx'⟩,
    exact is_open.mem_nhds (K.is_closed n).is_open_compl 
      (λ hxKn, hx' $ K.subset_interior_succ _ hxKn) },
  
  /- Let's cleanup assumption hX a bit -/
  obtain ⟨V, V_op, V_nhds, hPV⟩ : 
    ∃ V : X → set X, (∀ x, is_open (V x)) ∧ (∀ x, V x ∈ 𝓝 x) ∧ ∀ x, P (V x),
  { choose V' V'_nhds hPV' using hX,
    exact ⟨λ x, interior (V' x), λ x, is_open_interior, λ x, interior_mem_nhds.mpr (V'_nhds x),
           λ x, hP interior_subset (hPV' x)⟩ },
  /-
  For every `n`, every `x` in `Kdiff n`, consider `W x ∩ (K n)ᶜ`. 
  This is an open neighborhood of `x` which doesn't intersect `K n`.
  Because `X` is locally compact, we get a compact neighborhood
  `C x ⊆ W x ∩ (K n)ᶜ`. The interior of all `C x` cover the compact set
  `Kdiff n` so we get a finite subcover indexed by some finite subset of
  `s n ⊆ Kdiff n`. Now we need to gather the `C x` for `x ∈ ⋃ n, s n` to be
  the `u` sequence and the `V x ∩ (K n)ᶜ` to be the `v` sequence. 
  I don't know how to tell Lean about this gathering, maybe using some 
  encodable/denumerable stuff?

  Then local finiteness should be as in 
  refinement_of_locally_compact_sigma_compact_of_nhds_basis_set
  -/
  
  sorry
end
