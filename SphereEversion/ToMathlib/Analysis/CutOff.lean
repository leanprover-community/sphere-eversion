import Mathlib.Geometry.Manifold.PartitionOfUnity

/-! results about smooth cut-off functions: move to PartitionOfUnity -/
open Set Filter

open scoped Manifold Topology

-- this is basically `exists_smooth_zero_one_of_closed` applied to the normed space E
-- only difference is that one has bundled maps, and this is unbundled
-- unsure if that's worth a lemma; shouldn't need specialisation to normed spaces...
theorem exists_contDiff_zero_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {s t : Set E} (hs : IsClosed s) (ht : IsClosed t) (hd : Disjoint s t) :
    ∃ f : E → ℝ, ContDiff ℝ ∞ f ∧ EqOn f 0 s ∧ EqOn f 1 t ∧ ∀ x, f x ∈ Icc (0 : ℝ) 1 :=
  let ⟨f, hfs, hft, hf01⟩ := exists_smooth_zero_one_of_closed 𝓘(ℝ, E) hs ht hd
  ⟨f, f.smooth.contDiff, hfs, hft, hf01⟩

-- variant of the above: with f being 0 resp 1 in nhds of s and t
-- add! this version of exists_smooth_zero_one_of_closed to mathlib!
theorem exists_contDiff_zero_one_nhds {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {s t : Set E} (hs : IsClosed s) (ht : IsClosed t) (hd : Disjoint s t) :
    ∃ f : E → ℝ, ContDiff ℝ ∞ f ∧ (∀ᶠ x in 𝓝ˢ s, f x = 0) ∧ (∀ᶠ x in 𝓝ˢ t, f x = 1) ∧
      ∀ x, f x ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨u, u_op, hsu, hut⟩ := normal_exists_closure_subset hs ht.isOpen_compl
    (subset_compl_iff_disjoint_left.mpr hd.symm)
  obtain ⟨v, v_op, htv, hvu⟩ := normal_exists_closure_subset ht isClosed_closure.isOpen_compl
    (subset_compl_comm.mp hut)
  obtain ⟨f, hfsmooth, hfu, hfv, hf⟩ := exists_contDiff_zero_one isClosed_closure isClosed_closure
    (subset_compl_iff_disjoint_left.mp hvu)
  refine ⟨f, hfsmooth, ?_, ?_, hf⟩
  · exact eventually_of_mem (mem_of_superset (u_op.mem_nhdsSet.mpr hsu) subset_closure) hfu
  · exact eventually_of_mem (mem_of_superset (v_op.mem_nhdsSet.mpr htv) subset_closure) hfv

-- given s,t with s ⊆ interior t, construct a cutoff function f : E → [0,1] with
-- f = 1 in a nhds of s and supp f ⊆ t
-- generalise to manifolds, then upstream to PartitionOfUnity (maybe split those out)
theorem exists_contDiff_one_nhds_of_interior {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {s t : Set E} (hs : IsClosed s) (hd : s ⊆ interior t) :
    ∃ f : E → ℝ, ContDiff ℝ ∞ f ∧ (∀ᶠ x in 𝓝ˢ s, f x = 1) ∧ (∀ x, x ∉ t → f x = 0) ∧
      ∀ x, f x ∈ Icc (0 : ℝ) 1 := by
  rcases exists_contDiff_zero_one_nhds isOpen_interior.isClosed_compl hs
    (by rwa [← subset_compl_iff_disjoint_left, compl_compl]) with ⟨f, hfsmooth, h0, h1, hf⟩
  refine ⟨f, hfsmooth, h1, fun x hx ↦ ?_, hf⟩
  exact h0.self_of_nhdsSet _ fun hx' ↦ hx <| interior_subset hx'
