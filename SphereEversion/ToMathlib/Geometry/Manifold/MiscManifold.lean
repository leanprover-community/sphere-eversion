import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import Mathlib.Geometry.Manifold.Notation

open Set Function Filter

open scoped Manifold Topology ContDiff

noncomputable section

section IsManifold

open IsManifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners 𝕜 F G}
  {G' : Type*} [TopologicalSpace G'] {J' : ModelWithCorners 𝕜 F' G'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {N' : Type*} [TopologicalSpace N'] [ChartedSpace G' N']
  {F'' : Type*} [NormedAddCommGroup F''] [NormedSpace 𝕜 F'']
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''}
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H'' M'']
  {e : OpenPartialHomeomorph M H} {f : M → M'} {m n : WithTop ℕ∞} {s : Set M} {x x' : M}

theorem contMDiff_prod {f : M → M' × N'} :
    ContMDiff I (I'.prod J') n f ↔
      (CMDiff n fun x ↦ (f x).1) ∧ CMDiff n fun x ↦ (f x).2 :=
  ⟨fun h ↦ ⟨h.fst, h.snd⟩, fun h ↦ h.1.prodMk h.2⟩

theorem contMDiffAt_prod {f : M → M' × N'} {x : M} :
    ContMDiffAt I (I'.prod J') n f x ↔
      CMDiffAt n (fun x ↦ (f x).1) x ∧ CMDiffAt n (fun x ↦ (f x).2) x :=
  ⟨fun h ↦ ⟨h.fst, h.snd⟩, fun h ↦ h.1.prodMk h.2⟩

end IsManifold
