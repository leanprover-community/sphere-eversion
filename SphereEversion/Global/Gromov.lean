import SphereEversion.Global.LocalisationData
import SphereEversion.Global.LocalizedConstruction
import SphereEversion.Global.ParametricityForFree
import SphereEversion.ToMathlib.Geometry.Manifold.Metrizable

/-!
# Gromov's theorem

We prove the h-principle for open and ample first order differential relations.
-/


noncomputable section

open Set Filter ModelWithCorners Metric

open scoped Topology Manifold ContDiff

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM]
  {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM} [Boundaryless IM]
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M] [IsManifold IM ∞ M]
  [T2Space M] [SigmaCompactSpace M]
  {EX : Type*} [NormedAddCommGroup EX] [NormedSpace ℝ EX] [FiniteDimensional ℝ EX]
  {HX : Type*} [TopologicalSpace HX] {IX : ModelWithCorners ℝ EX HX} [Boundaryless IX]
  -- note: X is a metric space
  {X : Type*}
  [MetricSpace X] [ChartedSpace HX X] [IsManifold IX ∞ X] [SigmaCompactSpace X]
  {R : RelMfld IM M IX X} {A : Set M} {δ : M → ℝ}

@[inherit_doc] local notation "J¹" => OneJetBundle IM M IX X

theorem RelMfld.Ample.satisfiesHPrinciple (hRample : R.Ample) (hRopen : IsOpen R) (hA : IsClosed A)
    (hδ_pos : ∀ x, 0 < δ x) (hδ_cont : Continuous δ) : R.SatisfiesHPrinciple A δ := by
  borelize EX
  letI := manifoldMetric IM M
  haveI := Manifold.locallyCompact_of_finiteDimensional (M := M) (I := IM)
  haveI := Manifold.locallyCompact_of_finiteDimensional (M := X) (I := IX)
  refine RelMfld.satisfiesHPrinciple_of_weak hA fun A hA 𝓕₀ h𝓕₀ ↦ ?_
  obtain (hM | hM) := isEmpty_or_nonempty M
  · refine ⟨emptyHtpyFormalSol R, ?_, ?_, ?_, ?_⟩ <;> intro
    all_goals try intro
    all_goals
      first
      | exact empty_htpy_formal_sol_eq
      | exact (IsEmpty.false ‹M›).elim
  obtain (hX | hX) := isEmpty_or_nonempty X
  · exfalso
    inhabit M
    exact (IsEmpty.false <| 𝓕₀.bs default).elim
  -- We now start the main proof under the assumption that `M` and `X` are nonempty.
  have cont : Continuous 𝓕₀.bs := 𝓕₀.contMDiff_bs.continuous
  rcases exists_stability_dist IM IX cont with ⟨ε, ε_pos, ε_cont, hε⟩
  let τ := fun x : M ↦ min (δ x) (ε x)
  have τ_pos : ∀ x, 0 < τ x := fun x ↦ lt_min (hδ_pos x) (ε_pos x)
  have τ_cont : Continuous τ := hδ_cont.min ε_cont
  let P₀ : ∀ x : M, Germ (𝓝 x) J¹ → Prop := fun x F ↦
    F.value.1.1 = x ∧
      F.value ∈ R ∧
        F.ContMDiffAt' IM ((IM.prod IX).prod 𝓘(ℝ, EM →L[ℝ] EX)) ∞ ∧
          RestrictGermPredicate (fun x F' ↦ F'.value = 𝓕₀ x) A x F ∧
            dist F.value.1.2 (𝓕₀.bs x) < τ x
  let P₁ : ∀ x : M, Germ (𝓝 x) J¹ → Prop := fun x F ↦ IsHolonomicGerm F
  let P₂ : ∀ p : ℝ × M, Germ (𝓝 p) J¹ → Prop := fun p F ↦
    F.ContMDiffAt' (𝓘(ℝ).prod IM) ((IM.prod IX).prod 𝓘(ℝ, EM →L[ℝ] EX)) ∞
  have hP₂ : ∀ (a b : ℝ) (p : ℝ × M) (f : ℝ × M → J¹),
      P₂ (a * p.1 + b, p.2) f → P₂ p fun p : ℝ × M ↦ f (a * p.1 + b, p.2) := by
    rintro a b ⟨t, x⟩ f h
    change ContMDiffAt _ _ _ (f ∘ fun p : ℝ × M ↦ (a * p.1 + b, p.2)) (t, x)
    change ContMDiffAt _ _ _ f ((fun p : ℝ × M ↦ (a * p.1 + b, p.2)) (t, x)) at h
    have : CMDiffAt ∞ (fun p : ℝ × M ↦ (a * p.1 + b, p.2)) (t, x) :=
      haveI h₁ : CMDiffAt ∞ (fun t ↦ a * t + b) t :=
        contMDiffAt_iff_contDiffAt.mpr
          (((contDiffAt_id : ContDiffAt ℝ ∞ id t).const_smul a).add contDiffAt_const)
      h₁.prodMap contMDiffAt_id
    exact h.comp (t, x) this
  have init : ∀ x : M, P₀ x (𝓕₀ : M → J¹) := by
    refine fun x ↦ ⟨rfl, 𝓕₀.is_sol x, 𝓕₀.contMDiff x, ?_, ?_⟩
    · revert x
      exact forall_restrictGermPredicate_of_forall fun x ↦ rfl
    · erw [dist_self]
      exact τ_pos x
  have hP₂' : ∀ (t : ℝ) (x : M) (f : M → J¹), P₀ x f → P₂ (t, x) fun p : ℝ × M ↦ f p.2 :=
    fun t x f hf ↦ ContMDiffAt.comp (t, x) hf.2.2.1 contMDiffAt_snd
  have ind : ∀ m : M, ∃ V ∈ 𝓝 m, ∀ K₁ ⊆ V, ∀ K₀ ⊆ interior K₁, IsCompact K₀ → IsCompact K₁ →
      ∀ (C : Set M) (f : M → J¹), IsClosed C →
      (∀ x, P₀ x f) → (∀ᶠ x in 𝓝ˢ C, P₁ x f) →
        ∃ F : ℝ → M → J¹, (∀ t x, P₀ x (F t)) ∧
                          (∀ᶠ x in 𝓝ˢ (C ∪ K₀), P₁ x (F 1)) ∧
                          (∀ (p : ℝ × M), P₂ p ↿F) ∧
                          (∀ t, ∀ x ∉ K₁, F t x = f x) ∧
                          (∀ᶠ t in 𝓝ˢ (Iic 0), F t = f) ∧
                          ∀ᶠ t in 𝓝ˢ (Ici 1), F t = F 1 := by
    intro m
    rcases hε m with ⟨φ, ψ, ⟨e, rfl⟩, hφψ⟩
    have : φ '' ball e 1 ∈ 𝓝 (φ e) := by
      rw [← φ.isOpenEmbedding.map_nhds_eq]
      exact image_mem_map (ball_mem_nhds e zero_lt_one)
    use φ '' (ball e 1), this
    intro K₁ hK₁ K₀ K₀K₁ K₀_cpct K₁_cpct C f C_closed P₀f fC
    have K₁φ : K₁ ⊆ range φ := SurjOn.subset_range hK₁
    have K₀φ : K₀ ⊆ range φ := K₀K₁.trans interior_subset |>.trans K₁φ
    replace K₀_cpct : IsCompact (φ ⁻¹' K₀) :=
      φ.isOpenEmbedding.toIsInducing.isCompact_preimage' K₀_cpct K₀φ
    replace K₁_cpct : IsCompact (φ ⁻¹' K₁) :=
      φ.isOpenEmbedding.toIsInducing.isCompact_preimage' K₁_cpct K₁φ
    have K₀K₁' : φ ⁻¹' K₀ ⊆ interior (φ ⁻¹' K₁) := by
      rw [← φ.isOpenMap.preimage_interior_eq_interior_preimage φ.continuous]
      gcongr
    simp only [P₀, forall_and] at P₀f
    rcases P₀f with ⟨hf_sec, hf_sol, hf_smooth, hf_A, hf_dist⟩
    rw [forall_restrictGermPredicate_iff] at hf_A
    let F : FormalSol R := mkFormalSol f hf_sec hf_sol hf_smooth
    have hFAC : ∀ᶠ x near A ∪ C, F.IsHolonomicAt x := by
      rw [Eventually.union_nhdsSet]
      refine ⟨(hf_A.and h𝓕₀).eventually_nhdsSet.mono fun x hx ↦ ?_, fC⟩
      rw [eventually_and] at hx
      refine hx.2.self_of_nhds.congr (hx.1.mono fun x' hx' ↦ ?_)
      simp only [FormalSol.toOneJetSec_coe, mkFormalSol_apply, F]
      exact hx'.symm
    have hFφψ : F.bs '' (range φ) ⊆ range ψ := by
      rw [← range_comp]
      apply hφψ
      intro x
      calc
        dist (F.bs x) (𝓕₀.bs x) = dist (f x).1.2 (𝓕₀.bs x) := by simp only [F, mkFormalSol_bs_apply]
        _ < τ x := (hf_dist x)
        _ ≤ ε x := min_le_right _ _
    let η : M → ℝ := fun x ↦ τ x - dist (f x).1.2 (𝓕₀.bs x)
    have η_pos : ∀ x, 0 < η x := fun x ↦ sub_pos.mpr (hf_dist x)
    have η_cont : Continuous η := by
      have : ContMDiff IM ((IM.prod IX).prod 𝓘(ℝ, EM →L[ℝ] EX)) ∞ f := fun x ↦ hf_smooth x
      apply τ_cont.sub
      exact (oneJetBundle_proj_continuous.comp this.continuous).snd.dist 𝓕₀.contMDiff_bs.continuous
    rcases φ.improve_formalSol ψ hRample hRopen (hA.union C_closed) η_pos η_cont hFφψ hFAC K₀_cpct
        K₁_cpct K₀K₁' with
      ⟨F', hF'₀, hF'₁, hF'AC, hF'K₁, hF'η, hF'hol⟩
    refine ⟨fun t x ↦ F' t x, ?_, ?_, ?_, ?_, ?_, ?_⟩; all_goals beta_reduce
    · refine fun t x ↦ ⟨rfl, F'.is_sol, (F' t).contMDiff x, ?_, ?_⟩
      · revert x
        rw [forall_restrictGermPredicate_iff]
        rw [Eventually.union_nhdsSet] at hF'AC
        apply (hF'AC.1.and hf_A).mono
        rintro x ⟨hx, hx'⟩
        change F' t x = _
        rw [hx t, ← hx', mkFormalSol_apply]
        rfl
      · calc
          dist (F' t x).1.2 (𝓕₀.bs x) ≤ dist (F' t x).1.2 (F.bs x) + dist (F.bs x) (𝓕₀.bs x) :=
            dist_triangle _ _ _
          _ < η x + dist (F.bs x) (𝓕₀.bs x) := (add_lt_add_left (hF'η t x) _)
          _ = τ x := by simp [F, η]
    · rw [union_assoc, Eventually.union_nhdsSet, image_preimage_eq_of_subset K₀φ] at hF'hol
      exact hF'hol.2
    · exact F'.contMDiff
    · intro t x hx
      replace hx : x ∉ φ '' (φ ⁻¹' K₁) := by rwa [image_preimage_eq_of_subset K₁φ]
      simpa [F] using hF'K₁ t x hx
    · apply hF'₀.mono fun x hx ↦ ?_
      erw [hx]
      ext1 y
      simp [F]
    · exact hF'₁.mono (fun _ hx ↦ DFunLike.ext'_iff.mp hx)
  rcases inductive_htpy_construction P₀ P₁ P₂ hP₂ hP₂' init ind with ⟨F, hF₀, hFP₀, hFP₁, hFP₂⟩
  simp only [P₀, forall_and] at hFP₀
  rcases hFP₀ with ⟨hF_sec, hF_sol, _hF_smooth, hF_A, hF_dist⟩
  refine ⟨mkHtpyFormalSol F hF_sec hF_sol hFP₂, ?_, hFP₁, ?_, ?_⟩
  · intro x
    rw [mkHtpyFormalSol_apply, hF₀]
  · intro x hx t
    rw [mkHtpyFormalSol_apply]
    exact (forall_restrictGermPredicate_iff.mp <| hF_A t).self_of_nhdsSet x hx
  · intro t x
    change dist (mkHtpyFormalSol F hF_sec hF_sol hFP₂ t x).1.2 (𝓕₀.bs x) ≤ δ x
    rw [mkHtpyFormalSol_apply]
    exact (hF_dist t x).le.trans (min_le_left _ _)

variable {EP : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP] [FiniteDimensional ℝ EP]
  {HP : Type*} [TopologicalSpace HP] {IP : ModelWithCorners ℝ EP HP} [Boundaryless IP]
  {P : Type*} [TopologicalSpace P] [ChartedSpace HP P] [IsManifold IP ∞ P]
  [SigmaCompactSpace P] [T2Space P] {C : Set (P × M)}

/-
We now deduce the parametric case from the unparametric one using
`RelMfld.satisfiesHPrinciple.satisfiesHPrincipleWith` which reduces the parametric
`h`-principle to the non-parametric one for a different relation and `RelMfld.Ample.relativize`
which ensures the ampleness assumption survives this reduction.
-/
/-- **Gromov's Theorem** -/
theorem RelMfld.Ample.satisfiesHPrincipleWith (hRample : R.Ample) (hRopen : IsOpen R)
    (hC : IsClosed C) (hδ_pos : ∀ x, 0 < δ x) (hδ_cont : Continuous δ) :
    R.SatisfiesHPrincipleWith IP C δ := by
  have hδ_pos' : ∀ x : P × M, 0 < δ x.2 := fun x : P × M ↦ hδ_pos x.snd
  have hδ_cont' : Continuous fun x : P × M ↦ δ x.2 := hδ_cont.comp continuous_snd
  have is_op : IsOpen (RelMfld.relativize IP P R) := R.isOpen_relativize hRopen
  apply RelMfld.SatisfiesHPrinciple.satisfiesHPrincipleWith
  exact (hRample.relativize IP P).satisfiesHPrinciple is_op hC hδ_pos' hδ_cont'

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  [IsManifold I' ∞ M'] [SigmaCompactSpace M'] [T2Space M']

/-
Since every (σ-compact) manifold is metrizable, the metric space assumption can be removed.
-/
/-- Gromov's Theorem without metric space assumption -/
theorem RelMfld.Ample.satisfiesHPrincipleWith' {R : RelMfld IM M I' M'} (hRample : R.Ample)
    (hRopen : IsOpen R) (hC : IsClosed C) (hδ_pos : ∀ x, 0 < δ x) (hδ_cont : Continuous δ) :
    letI := manifoldMetric I' M'
    R.SatisfiesHPrincipleWith IP C δ := by
  letI := manifoldMetric I' M'
  apply RelMfld.Ample.satisfiesHPrincipleWith <;> assumption
