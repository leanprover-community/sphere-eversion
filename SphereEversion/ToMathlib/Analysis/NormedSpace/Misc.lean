import Mathlib.Analysis.InnerProductSpace.EuclideanDist

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

open Set Metric
open scoped ContDiff

noncomputable section

variable [FiniteDimensional ℝ F] (c : F) (r : ℝ)

theorem PartialHomeomorph.exists_contDiff_source_univ_target_subset_ball :
    ∃ f : PartialHomeomorph F F, ContDiff ℝ ∞ f ∧ ContDiffOn ℝ ∞ f.symm f.target ∧
      f.source = univ ∧ (0 < r → f.target ⊆ ball c r) ∧ f 0 = c := by
  by_cases hr : 0 < r
  · let e := toEuclidean (E := F)
    let e' := e.toHomeomorph
    rcases Euclidean.nhds_basis_ball.mem_iff.1 (ball_mem_nhds c hr) with ⟨ε, ε₀, hε⟩
    set f := (e'.transPartialHomeomorph (.univBall (e c) ε)).transHomeomorph e'.symm
    have hf : f.target = Euclidean.ball c ε := by
      rw [transHomeomorph_target, Homeomorph.transPartialHomeomorph_target, univBall_target _ ε₀]
      rfl
    refine ⟨f, ?_, ?_, ?_, fun _ ↦ by rwa [hf], by simp [e, e', f]⟩
    · exact e.symm.contDiff.comp <| contDiff_univBall.comp e.contDiff
    · exact e.symm.contDiff.comp_contDiffOn <| contDiffOn_univBall_symm.comp
        e.contDiff.contDiffOn hf.subset
    · rw [transHomeomorph_source, Homeomorph.transPartialHomeomorph_source, univBall_source]; rfl
  · use (IsometryEquiv.vaddConst c).toHomeomorph.toPartialHomeomorph,
      contDiff_id.add contDiff_const, contDiffOn_id.sub contDiffOn_const
    simp [hr]

/-- A variant of `InnerProductSpace.diffeomorphToNhd` which provides a function satisfying the
weaker condition `range_diffeomorph_to_nhd_subset_ball` but which applies to any `NormedSpace`.

In fact one could demand this stronger property but it would be more work and we don't need it. -/
def diffeomorphToNhd (c : F) (r : ℝ) : PartialHomeomorph F F :=
  (PartialHomeomorph.exists_contDiff_source_univ_target_subset_ball c r).choose

@[simp]
theorem diffeomorphToNhd_source : (diffeomorphToNhd c r).source = univ :=
  (PartialHomeomorph.exists_contDiff_source_univ_target_subset_ball c r).choose_spec.2.2.1

@[simp]
theorem diffeomorphToNhd_apply_zero : diffeomorphToNhd c r 0 = c :=
  (PartialHomeomorph.exists_contDiff_source_univ_target_subset_ball c r).choose_spec.2.2.2.2

variable {r} in
theorem target_diffeomorphToNhd_subset_ball (hr : 0 < r) :
    (diffeomorphToNhd c r).target ⊆ ball c r :=
  (PartialHomeomorph.exists_contDiff_source_univ_target_subset_ball c r).choose_spec.2.2.2.1 hr

variable {r} in
@[simp]
theorem range_diffeomorphToNhd_subset_ball (hr : 0 < r) :
    range (diffeomorphToNhd c r) ⊆ ball c r := by
  erw [← image_univ, ← diffeomorphToNhd_source c r, PartialEquiv.image_source_eq_target]
  exact target_diffeomorphToNhd_subset_ball c hr

@[simp]
theorem contDiff_diffeomorphToNhd {n : ℕ∞} :
    ContDiff ℝ n <| diffeomorphToNhd c r :=
  (PartialHomeomorph.exists_contDiff_source_univ_target_subset_ball c r).choose_spec.1.of_le
    (mod_cast le_top)

@[simp]
theorem contDiffOn_diffeomorphToNhd_inv {n : ℕ∞} :
    ContDiffOn ℝ n (diffeomorphToNhd c r).symm (diffeomorphToNhd c r).target :=
  (PartialHomeomorph.exists_contDiff_source_univ_target_subset_ball c r).choose_spec.2.1.of_le
    (mod_cast le_top)
