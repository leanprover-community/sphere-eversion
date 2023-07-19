import Mathlib.Geometry.Manifold.ContMDiff

open scoped Topology Filter Manifold BigOperators

open Set Function Filter

section

variable {ι : Type _} {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type _}
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type _} [TopologicalSpace M]
  [ChartedSpace H M] {s : Set M} {F : Type _} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem contMDiffWithinAt_of_not_mem {f : M → F} {x : M} (hx : x ∉ tsupport f) (n : ℕ∞)
    (s : Set M) : ContMDiffWithinAt I 𝓘(ℝ, F) n f s x :=
  (contMDiffWithinAt_const :
        ContMDiffWithinAt I 𝓘(ℝ, F) n (fun _ => (0 : F)) s x).congr_of_eventuallyEq
    (eventually_nhdsWithin_of_eventually_nhds <| not_mem_tsupport_iff_eventuallyEq.mp hx)
    (image_eq_zero_of_nmem_tsupport hx)

theorem contMDiffAt_of_not_mem {f : M → F} {x : M} (hx : x ∉ tsupport f) (n : ℕ∞) :
    ContMDiffAt I 𝓘(ℝ, F) n f x :=
  contMDiffWithinAt_of_not_mem hx n univ

end

