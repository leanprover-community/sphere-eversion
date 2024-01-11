import Mathlib.Geometry.Manifold.ContMDiff.Product

open Set Function Filter

open scoped Manifold Topology

noncomputable section

section SmoothManifoldWithCorners

open SmoothManifoldWithCorners

variable {𝕜 : Type _} [NontriviallyNormedField 𝕜] {E : Type _} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {E' : Type _} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {F : Type _}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {F' : Type _} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {H : Type _} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {H' : Type _} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {G : Type _} [TopologicalSpace G] {J : ModelWithCorners 𝕜 F G}
  {G' : Type _} [TopologicalSpace G'] {J' : ModelWithCorners 𝕜 F' G'} {M : Type _}
  [TopologicalSpace M] [ChartedSpace H M] {M' : Type _} [TopologicalSpace M'] [ChartedSpace H' M']
  {N : Type _} [TopologicalSpace N] [ChartedSpace G N] {N' : Type _} [TopologicalSpace N']
  [ChartedSpace G' N'] {F'' : Type _} [NormedAddCommGroup F''] [NormedSpace 𝕜 F''] {E'' : Type _}
  [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] {H'' : Type _} [TopologicalSpace H'']
  {I'' : ModelWithCorners 𝕜 E'' H''} {M'' : Type _} [TopologicalSpace M''] [ChartedSpace H'' M'']
  {e : PartialHomeomorph M H}

variable {f : M → M'} {m n : ℕ∞} {s : Set M} {x x' : M}

theorem contMDiff_prod {f : M → M' × N'} :
    ContMDiff I (I'.prod J') n f ↔
      (ContMDiff I I' n fun x ↦ (f x).1) ∧ ContMDiff I J' n fun x ↦ (f x).2 :=
  ⟨fun h ↦ ⟨h.fst, h.snd⟩, fun h ↦ h.1.prod_mk h.2⟩

theorem contMDiffAt_prod {f : M → M' × N'} {x : M} :
    ContMDiffAt I (I'.prod J') n f x ↔
      ContMDiffAt I I' n (fun x ↦ (f x).1) x ∧ ContMDiffAt I J' n (fun x ↦ (f x).2) x :=
  ⟨fun h ↦ ⟨h.fst, h.snd⟩, fun h ↦ h.1.prod_mk h.2⟩

theorem smooth_prod {f : M → M' × N'} :
    Smooth I (I'.prod J') f ↔ (Smooth I I' fun x ↦ (f x).1) ∧ Smooth I J' fun x ↦ (f x).2 :=
  contMDiff_prod

theorem smoothAt_prod {f : M → M' × N'} {x : M} :
    SmoothAt I (I'.prod J') f x ↔
      SmoothAt I I' (fun x ↦ (f x).1) x ∧ SmoothAt I J' (fun x ↦ (f x).2) x :=
  contMDiffAt_prod

theorem ContMDiffWithinAt.congr_of_eventuallyEq_insert {f f' : M → M'}
    (hf : ContMDiffWithinAt I I' n f s x) (h : f' =ᶠ[𝓝[Insert.insert x s] x] f) :
    ContMDiffWithinAt I I' n f' s x :=
  hf.congr_of_eventuallyEq (h.filter_mono <| nhdsWithin_mono x <| subset_insert x s) <|
    h.self_of_nhdsWithin (mem_insert x s)

end SmoothManifoldWithCorners
