import Mathbin.Geometry.Manifold.Algebra.LieGroup

open scoped Topology Filter Manifold BigOperators

open Set Function Filter

section

variable {ι : Type _} {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type _}
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type _} [TopologicalSpace M]
  [ChartedSpace H M] {s : Set M} {F : Type _} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem ContMDiffWithinAt.sum {ι : Type _} {f : ι → M → F} {J : Finset ι} {n : ℕ∞} {s : Set M}
    {x₀ : M} (h : ∀ i ∈ J, ContMDiffWithinAt I 𝓘(ℝ, F) n (f i) s x₀) :
    ContMDiffWithinAt I 𝓘(ℝ, F) n (fun x => ∑ i in J, f i x) s x₀ := by
  classical
  induction' J using Finset.induction_on with i K iK IH
  · simp [contMDiffWithinAt_const]
  · simp only [iK, Finset.sum_insert, not_false_iff]
    exact (h _ (Finset.mem_insert_self i K)).add (IH fun j hj => h _ <| Finset.mem_insert_of_mem hj)

theorem ContMDiffAt.sum {ι : Type _} {f : ι → M → F} {J : Finset ι} {n : ℕ∞} {x₀ : M}
    (h : ∀ i ∈ J, ContMDiffAt I 𝓘(ℝ, F) n (f i) x₀) :
    ContMDiffAt I 𝓘(ℝ, F) n (fun x => ∑ i in J, f i x) x₀ :=
  by
  simp only [← contMDiffWithinAt_univ] at *
  exact ContMDiffWithinAt.sum h

theorem ContMDiff.sum {ι : Type _} {f : ι → M → F} {J : Finset ι} {n : ℕ∞}
    (h : ∀ i ∈ J, ContMDiff I 𝓘(ℝ, F) n (f i)) : ContMDiff I 𝓘(ℝ, F) n fun x => ∑ i in J, f i x :=
  fun x => ContMDiffAt.sum fun j hj => h j hj x

theorem contMDiffWithinAt_finsum {ι : Type _} {f : ι → M → F}
    (lf : LocallyFinite fun i => support <| f i) {n : ℕ∞} {s : Set M} {x₀ : M}
    (h : ∀ i, ContMDiffWithinAt I 𝓘(ℝ, F) n (f i) s x₀) :
    ContMDiffWithinAt I 𝓘(ℝ, F) n (fun x => ∑ᶠ i, f i x) s x₀ :=
  let ⟨I, hI⟩ := finsum_eventually_eq_sum lf x₀
  ContMDiffWithinAt.congr_of_eventuallyEq (ContMDiffWithinAt.sum fun i hi => h i)
    (eventually_nhdsWithin_of_eventually_nhds hI) hI.self_of_nhds

theorem contMDiffAt_finsum {ι : Type _} {f : ι → M → F} (lf : LocallyFinite fun i => support <| f i)
    {n : ℕ∞} {x₀ : M} (h : ∀ i, ContMDiffAt I 𝓘(ℝ, F) n (f i) x₀) :
    ContMDiffAt I 𝓘(ℝ, F) n (fun x => ∑ᶠ i, f i x) x₀ :=
  contMDiffWithinAt_finsum lf h

end

