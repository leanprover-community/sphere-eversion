import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Topology.EMetricSpace.Paracompact
import SphereEversion.ToMathlib.Topology.NhdsSet

open Set Filter

open scoped Manifold Topology

theorem exists_contDiff_zero_one {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {s t : Set E} (hs : IsClosed s) (ht : IsClosed t) (hd : Disjoint s t) :
    ∃ f : E → ℝ, ContDiff ℝ ⊤ f ∧ EqOn f 0 s ∧ EqOn f 1 t ∧ ∀ x, f x ∈ Icc (0 : ℝ) 1 :=
  let ⟨f, hfs, hft, hf01⟩ := exists_smooth_zero_one_of_closed 𝓘(ℝ, E) hs ht hd
  ⟨f, f.smooth.contDiff, hfs, hft, hf01⟩

theorem exists_contDiff_zero_one_nhds {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {s t : Set E} (hs : IsClosed s) (ht : IsClosed t) (hd : Disjoint s t) :
    ∃ f : E → ℝ, ContDiff ℝ ⊤ f ∧ (∀ᶠ x in 𝓝ˢ s, f x = 0) ∧ (∀ᶠ x in 𝓝ˢ t, f x = 1) ∧
      ∀ x, f x ∈ Icc (0 : ℝ) 1 := by
  rcases normal_exists_closure_subset hs ht.isOpen_compl
      (subset_compl_iff_disjoint_left.mpr hd.symm)
    with ⟨u, u_op, hsu, hut⟩
  have hcu : IsClosed (closure u) := isClosed_closure
  rcases normal_exists_closure_subset ht hcu.isOpen_compl (subset_compl_comm.mp hut) with
    ⟨v, v_op, htv, hvu⟩
  have hcv : IsClosed (closure v) := isClosed_closure
  rcases exists_contDiff_zero_one hcu hcv (subset_compl_iff_disjoint_left.mp hvu) with
    ⟨f, hfsmooth, hfu, hfv, hf⟩
  refine' ⟨f, hfsmooth, _, _, hf⟩
  apply eventually_of_mem (mem_of_superset (u_op.mem_nhdsSet.mpr hsu) subset_closure) hfu
  apply eventually_of_mem (mem_of_superset (v_op.mem_nhdsSet.mpr htv) subset_closure) hfv

theorem exists_contDiff_one_nhds_of_interior {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {s t : Set E} (hs : IsClosed s) (hd : s ⊆ interior t) :
    ∃ f : E → ℝ, ContDiff ℝ ⊤ f ∧ (∀ᶠ x in 𝓝ˢ s, f x = 1) ∧ (∀ x, x ∉ t → f x = 0) ∧
      ∀ x, f x ∈ Icc (0 : ℝ) 1 := by
  have : IsClosed (interior t)ᶜ := isOpen_interior.isClosed_compl
  rcases exists_contDiff_zero_one_nhds this hs
    (by rwa [← subset_compl_iff_disjoint_left, compl_compl]) with ⟨f, hfsmooth, h0, h1, hf⟩
  refine ⟨f, hfsmooth, h1, fun x hx ↦ ?_, hf⟩
  exact h0.self_of_nhdsSet _ fun hx' ↦ hx <| interior_subset hx'
