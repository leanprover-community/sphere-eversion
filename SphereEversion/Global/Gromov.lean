import Project.ToMathlib.Data.Set.Prod
import Project.ToMathlib.Data.Nat.Basic
import Project.ToMathlib.Geometry.Manifold.Metrizable
import Project.ToMathlib.Topology.Constructions
import Project.ToMathlib.Logic.Basic
import Project.InductiveConstructions
import Project.Global.ParametricityForFree
import Project.Global.LocalizedConstruction
import Project.Global.LocalisationData

/-!
# Gromov's theorem

We prove the h-principle for open and ample first order differential relations.
-/


noncomputable section

open Set Filter ModelWithCorners Metric

open scoped Topology Manifold

variable {EM : Type _} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM]
  {HM : Type _} [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM} [Boundaryless IM] {M : Type _}
  [TopologicalSpace M] [ChartedSpace HM M] [SmoothManifoldWithCorners IM M] [T2Space M]
  [SigmaCompactSpace M] {EX : Type _} [NormedAddCommGroup EX] [NormedSpace ℝ EX]
  [FiniteDimensional ℝ EX] {HX : Type _} [TopologicalSpace HX] {IX : ModelWithCorners ℝ EX HX}
  [ModelWithCorners.Boundaryless IX]
  -- note: X is a metric space
  {X : Type _}
  [MetricSpace X] [ChartedSpace HX X] [SmoothManifoldWithCorners IX X] [SigmaCompactSpace X]
  {R : RelMfld IM M IX X} {A : Set M} {δ : M → ℝ}

/- ./././Mathport/Syntax/Translate/Basic.lean:334:40: warning: unsupported option trace.filter_inst_type -/
set_option trace.filter_inst_type true

local notation "J¹" => OneJetBundle IM M IX X

/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (x «expr ∉ » U i) -/
theorem RelMfld.Ample.satisfiesHPrinciple (hRample : R.Ample) (hRopen : IsOpen R) (hA : IsClosed A)
    (hδ_pos : ∀ x, 0 < δ x) (hδ_cont : Continuous δ) : R.SatisfiesHPrinciple A δ :=
  by
  borelize EX
  haveI := locally_compact_manifold IM M
  haveI := locally_compact_manifold IX X
  refine' RelMfld.satisfiesHPrinciple_of_weak hA _
  clear! A
  intro A hA 𝓕₀ h𝓕₀
  cases' isEmpty_or_nonempty M with hM hM
  · refine' ⟨emptyHtpyFormalSol R, _, _, _, _⟩
    all_goals try apply eventually_of_forall _
    all_goals try intro
    all_goals try intro
    all_goals
      first
      | apply empty_htpy_formal_sol_eq
      | apply (IsEmpty.false ‹M›).elim
  cases' isEmpty_or_nonempty X with hX hX
  · exfalso
    inhabit M
    exact (IsEmpty.false <| 𝓕₀.bs default).elim
  -- We now start the main proof under the assumption that `M` and `X` are nonempty.
  have cont : Continuous 𝓕₀.bs := 𝓕₀.smooth_bs.continuous
  let L : LocalisationData IM IX 𝓕₀.bs := stdLocalisationData EM IM EX IX Cont
  let K : IndexType L.N → Set M := fun i => L.φ i '' closed_ball (0 : EM) 1
  let U : IndexType L.N → Set M := fun i => range (L.φ i)
  have K_cover : (⋃ i, K i) = univ :=
    eq_univ_of_subset (Union_mono fun i => image_subset _ ball_subset_closed_ball) L.h₁
  let τ := fun x : M => min (δ x) (L.ε x)
  have τ_pos : ∀ x, 0 < τ x := fun x => lt_min (hδ_pos x) (L.ε_pos x)
  have τ_cont : Continuous τ := hδ_cont.min L.ε_cont
  have := fun (x : M) (F' : germ (𝓝 x) J¹) => F'.value = 𝓕₀ x
  let P₀ : ∀ x : M, germ (𝓝 x) J¹ → Prop := fun x F =>
    F.value.1.1 = x ∧
      F.value ∈ R ∧
        F.ContMdiffAt' IM ((IM.prod IX).Prod 𝓘(ℝ, EM →L[ℝ] EX)) ∞ ∧
          RestrictGermPredicate (fun x F' => F'.value = 𝓕₀ x) A x F ∧
            dist F.value.1.2 (𝓕₀.bs x) < τ x
  let P₁ : ∀ x : M, germ (𝓝 x) J¹ → Prop := fun x F => IsHolonomicGerm F
  let P₂ : ∀ p : ℝ × M, germ (𝓝 p) J¹ → Prop := fun p F =>
    F.ContMdiffAt' (𝓘(ℝ).Prod IM) ((IM.prod IX).Prod 𝓘(ℝ, EM →L[ℝ] EX)) ∞
  have hP₂ :
    ∀ (a b : ℝ) (p : ℝ × M) (f : ℝ × M → OneJetBundle IM M IX X),
      P₂ (a * p.1 + b, p.2) f → P₂ p fun p : ℝ × M => f (a * p.1 + b, p.2) :=
    by
    rintro a b ⟨t, x⟩ f h
    change ContMDiffAt _ _ _ (f ∘ fun p : ℝ × M => (a * p.1 + b, p.2)) (t, x)
    change ContMDiffAt _ _ _ f ((fun p : ℝ × M => (a * p.1 + b, p.2)) (t, x)) at h 
    have :
      ContMDiffAt (𝓘(ℝ, ℝ).Prod IM) (𝓘(ℝ, ℝ).Prod IM) ∞ (fun p : ℝ × M => (a * p.1 + b, p.2))
        (t, x) :=
      haveI h₁ : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun t => a * t + b) t :=
        cont_mdiff_at_iff_cont_diff_at.mpr
          (((contDiffAt_id : ContDiffAt ℝ ∞ id t).const_smul a).add contDiffAt_const)
      h₁.prod_map contMDiffAt_id
    exact h.comp (t, x) this
  have init : ∀ x : M, P₀ x (𝓕₀ : M → J¹) :=
    by
    refine' fun x => ⟨rfl, 𝓕₀.is_sol x, 𝓕₀.smooth x, _, _⟩
    · revert x
      exact forall_restrictGermPredicate_of_forall fun x => rfl
    · erw [dist_self]
      exact τ_pos x
  have ind :
    ∀ (i : IndexType L.N) (f : M → J¹),
      (∀ x, P₀ x f) →
        (∀ᶠ x near ⋃ j < i, K j, P₁ x f) →
          ∃ F : ℝ → M → J¹,
            (∀ t, ∀ x, P₀ x <| F t) ∧
              (∀ᶠ x near ⋃ j ≤ i, K j, P₁ x <| F 1) ∧
                (∀ p, P₂ p ↿F) ∧
                  (∀ t, ∀ (x) (_ : x ∉ U i), F t x = f x) ∧
                    (∀ᶠ t near Iic 0, F t = f) ∧ ∀ᶠ t near Ici 1, F t = F 1 :=
    by
    intro i f hf₀ hf₁
    let K₀ : Set EM := closed_ball 0 1
    have hK₀ : IsCompact K₀ := is_compact_closed_ball 0 1
    let K₁ : Set EM := closed_ball 0 2
    have hK₁ : IsCompact K₁ := is_compact_closed_ball 0 2
    have hK₀K₁ : K₀ ⊆ interior K₁ := by
      dsimp [K₀, K₁]
      rw [interior_closedBall (0 : EM) (by norm_num : (2 : ℝ) ≠ 0)]
      exact closed_ball_subset_ball (by norm_num)
    let C := ⋃ j < i, L.φ j '' closed_ball 0 1
    have hC :
      IsClosed C :=-- TODO: rewrite localization_data.is_closed_Union to match this.
        isClosed_biUnion
        (finite_Iio _) fun j hj => (hK₀.image <| (L.φ j).Continuous).IsClosed
    simp only [P₀, forall_and] at hf₀ 
    rcases hf₀ with ⟨hf_sec, hf_sol, hf_smooth, hf_A, hf_dist⟩
    rw [forall_restrictGermPredicate_iff] at hf_A 
    let F : FormalSol R := mkFormalSol f hf_sec hf_sol hf_smooth
    have hFAC : ∀ᶠ x near A ∪ C, F.is_holonomic_at x :=
      by
      rw [eventually_nhds_set_union]
      refine' ⟨_, hf₁⟩
      apply (hf_A.and h𝓕₀).eventually_nhdsSet.mono fun x hx => _
      rw [eventually_and] at hx 
      apply hx.2.self_of_nhds.congr
      apply hx.1.mono fun x' hx' => _
      simp [F]
      exact hx'.symm
    have hFφψ : F.bs '' (range <| L.φ i) ⊆ range (L.ψj i) :=
      by
      rw [← range_comp]
      apply L.ε_spec
      intro x
      calc
        dist (F.bs x) (𝓕₀.bs x) = dist (f x).1.2 (𝓕₀.bs x) := by simp only [F, mkFormalSol_bs_apply]
        _ < τ x := (hf_dist x)
        _ ≤ L.ε x := min_le_right _ _
    let η : M → ℝ := fun x => τ x - dist (f x).1.2 (𝓕₀.bs x)
    have η_pos : ∀ x, 0 < η x := fun x => sub_pos.mpr (hf_dist x)
    have η_cont : Continuous η :=
      by
      have : ContMDiff IM ((IM.prod IX).Prod 𝓘(ℝ, EM →L[ℝ] EX)) ∞ f := fun x => hf_smooth x
      apply τ_cont.sub
      exact (one_jet_bundle_proj_continuous.comp this.continuous).snd.dist 𝓕₀.smooth_bs.continuous
    rcases(L.φ i).improve_formalSol (L.ψj i) hRample hRopen (hA.union hC) η_pos η_cont hFφψ hFAC hK₀
        hK₁ hK₀K₁ with
      ⟨F', hF'₀, hF'₁, hF'AC, hF'K₁, hF'η, hF'hol⟩
    refine' ⟨fun t x => F' t x, _, _, _, _, _, _⟩
    · refine' fun t x => ⟨rfl, F'.is_sol, (F' t).smooth x, _, _⟩
      · revert x
        rw [forall_restrictGermPredicate_iff]
        rw [eventually_nhds_set_union] at hF'AC 
        apply (hF'AC.1.And hf_A).mono
        rintro x ⟨hx, hx'⟩
        change F' t x = _
        rw [hx t, ← hx', mkFormalSol_apply]
        rfl
      ·
        calc
          dist (F' t x).1.2 (𝓕₀.bs x) ≤ dist (F' t x).1.2 (F.bs x) + dist (F.bs x) (𝓕₀.bs x) :=
            dist_triangle _ _ _
          _ < η x + dist (F.bs x) (𝓕₀.bs x) := (add_lt_add_right (hF'η t x) _)
          _ = τ x := by simp [η]
    · rw [union_assoc, eventually_nhds_set_union] at hF'hol 
      replace hF'hol := hF'hol.2
      simp_rw [← L.Union_succ'] at hF'hol 
      exact hF'hol
    · exact F'.smooth
    · intro t x hx
      rw [hF'K₁ t x ((mem_range_of_mem_image _ _).mt hx)]
      simp [F]
    · apply hF'₀.mono fun x hx => _
      erw [hx]
      ext1 y
      simp [F]
    · apply hF'₁.mono fun x hx => _
      rw [hx]
  rcases inductive_htpy_construction P₀ P₁ P₂ hP₂ L.lf_φ K_cover init (𝓕₀.smooth.comp contMDiff_snd)
      ind with
    ⟨F, hF₀, hFP₀, hFP₁, hFP₂⟩
  simp only [P₀, forall₂_and_distrib] at hFP₀ 
  rcases hFP₀ with ⟨hF_sec, hF_sol, hF_smooth, hF_A, hF_dist⟩
  refine' ⟨mkHtpyFormalSol F hF_sec hF_sol hFP₂, _, _, _, _⟩
  · intro x
    rw [mkHtpyFormalSol_apply, hF₀]
  · exact hFP₁
  · intro x hx t
    rw [mkHtpyFormalSol_apply]
    exact (forall_restrict_germ_predicate_iff.mp <| hF_A t).on_set x hx
  · intro t x
    change dist (mkHtpyFormalSol F hF_sec hF_sol hFP₂ t x).1.2 (𝓕₀.bs x) ≤ δ x
    rw [mkHtpyFormalSol_apply]
    exact (hF_dist t x).le.trans (min_le_left _ _)

variable {EP : Type _} [NormedAddCommGroup EP] [NormedSpace ℝ EP] [FiniteDimensional ℝ EP]
  {HP : Type _} [TopologicalSpace HP] {IP : ModelWithCorners ℝ EP HP} [Boundaryless IP] {P : Type _}
  [TopologicalSpace P] [ChartedSpace HP P] [SmoothManifoldWithCorners IP P] [SigmaCompactSpace P]
  [T2Space P] {C : Set (P × M)}

/-
We now deduce the parametric case from the unparametric one using
`rel_mfld.satisfies_h_principle.satisfies_h_principle_with` which reduces the parametric
`h`-principle to the non-parametric one for a different relation and `rel_mafld.ample.relativize`
which ensures the ampleness assumption survives this reduction.
-/
/-- **Gromov's Theorem** -/
theorem RelMfld.Ample.satisfiesHPrincipleWith (hRample : R.Ample) (hRopen : IsOpen R)
    (hC : IsClosed C) (hδ_pos : ∀ x, 0 < δ x) (hδ_cont : Continuous δ) :
    R.SatisfiesHPrincipleWith IP C δ :=
  by
  have hδ_pos' : ∀ x : P × M, 0 < δ x.2 := fun x : P × M => hδ_pos x.snd
  have hδ_cont' : Continuous fun x : P × M => δ x.2 := hδ_cont.comp continuous_snd
  have is_op : IsOpen (RelMfld.relativize IP P R) := R.is_open_relativize hRopen
  apply RelMfld.SatisfiesHPrinciple.satisfiesHPrincipleWith
  exact (hRample.relativize IP P).SatisfiesHPrinciple is_op hC hδ_pos' hδ_cont'

variable {E' : Type _} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type _} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  [ModelWithCorners.Boundaryless I'] {M' : Type _} [TopologicalSpace M'] [ChartedSpace H' M']
  [SmoothManifoldWithCorners I' M'] [SigmaCompactSpace M'] [T2Space M']

/-
Since every (sigma-compact) manifold is metrizable, the metric space assumption can be removed.
-/
/-- Gromov's Theorem without metric space assumption -/
theorem RelMfld.Ample.satisfies_h_principle_with' {R : RelMfld IM M I' M'} (hRample : R.Ample)
    (hRopen : IsOpen R) (hC : IsClosed C) (hδ_pos : ∀ x, 0 < δ x) (hδ_cont : Continuous δ) :
    letI := manifoldMetric I' M'
    R.satisfies_h_principle_with IP C δ :=
  by apply RelMfld.Ample.satisfiesHPrincipleWith <;> assumption

