import SphereEversion.ToMathlib.Data.Set.Prod
import SphereEversion.ToMathlib.Data.Nat.Basic
import SphereEversion.ToMathlib.Geometry.Manifold.Metrizable
import SphereEversion.ToMathlib.Logic.Basic
import SphereEversion.InductiveConstructions
import SphereEversion.Global.ParametricityForFree
import SphereEversion.Global.LocalizedConstruction
import SphereEversion.Global.LocalisationData

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

local notation "J¹" => OneJetBundle IM M IX X


-- TODO: cleanup the following awful mess
lemma OpenEmbedding.homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : OpenEmbedding f) : Homeomorph X (range f) where
  toFun := rangeFactorization f
  invFun := Function.surjInv surjective_onto_range
  left_inv  := by
    apply Function.leftInverse_surjInv
    exact ⟨fun  x x' h ↦  hf.inj <| by simpa [rangeFactorization] using h,  surjective_onto_range⟩
  right_inv := Function.rightInverse_surjInv surjective_onto_range
  continuous_toFun := continuous_induced_rng.mpr hf.continuous
  continuous_invFun := by
    dsimp
    refine continuous_def.mpr ?_
    intro U U_op
    rw [← image_eq_preimage_of_inverse]
    swap
    apply Function.leftInverse_surjInv
    exact ⟨fun  x x' h ↦  hf.inj <| by simpa [rangeFactorization] using h,  surjective_onto_range⟩
    rw [isOpen_induced_iff]
    use f '' U, hf.isOpenMap U U_op
    ext ⟨y, x, rfl⟩
    apply exists_congr
    intro x'
    apply and_congr Iff.rfl
    conv_lhs => rw [← rangeFactorization_eq (f := f)]
    erw [Subtype.val_inj]
    rfl
    exact Function.rightInverse_surjInv surjective_onto_range



lemma OpenEmbedding.isCompact_preimage {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : OpenEmbedding f) {K : Set Y} (K_cpct: IsCompact K) (Kf : K ⊆ range f) :
    IsCompact (f ⁻¹' K) := by

  let K' : Set (range f) := {x | (x : Y) ∈ K}
  have K'_cpct : IsCompact K':= by
    refine Subtype.isCompact_iff.mpr ?_
    convert K_cpct
    change Subtype.val '' (Subtype.val ⁻¹' K) = K
    sorry
  convert hf.homeomorph.isCompact_preimage.mpr K'_cpct
  ext x
  change f x ∈ K ↔ ↑(hf.homeomorph x) ∈ K
  unfold OpenEmbedding.homeomorph
  simp only [Homeomorph.homeomorph_mk_coe, Equiv.coe_fn_mk, rangeFactorization_coe]


theorem RelMfld.Ample.satisfiesHPrinciple' (hRample : R.Ample) (hRopen : IsOpen R) (hA : IsClosed A)
    (hδ_pos : ∀ x, 0 < δ x) (hδ_cont : Continuous δ) : R.SatisfiesHPrinciple A δ := by
borelize EX
letI := manifoldMetric IM M
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
rcases exists_stability_dist IM IX cont with ⟨ε, ε_pos, ε_cont, hε⟩
let τ := fun x : M ↦ min (δ x) (ε x)
have τ_pos : ∀ x, 0 < τ x := fun x ↦ lt_min (hδ_pos x) (ε_pos x)
have τ_cont : Continuous τ := hδ_cont.min ε_cont
have := fun (x : M) (F' : Germ (𝓝 x) J¹) ↦ F'.value = 𝓕₀ x
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
  sorry/- rintro a b ⟨t, x⟩ f h
  change ContMDiffAt _ _ _ (f ∘ fun p : ℝ × M ↦ (a * p.1 + b, p.2)) (t, x)
  change ContMDiffAt _ _ _ f ((fun p : ℝ × M ↦ (a * p.1 + b, p.2)) (t, x)) at h
  have :
    ContMDiffAt (𝓘(ℝ, ℝ).prod IM) (𝓘(ℝ, ℝ).prod IM) ∞ (fun p : ℝ × M ↦ (a * p.1 + b, p.2))
      (t, x) :=
    haveI h₁ : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun t ↦ a * t + b) t :=
      contMDiffAt_iff_contDiffAt.mpr
        (((contDiffAt_id : ContDiffAt ℝ ∞ id t).const_smul a).add contDiffAt_const)
    h₁.prod_map contMDiffAt_id
  exact h.comp (t, x) this -/
have init : ∀ x : M, P₀ x (𝓕₀ : M → J¹) :=
  by
  refine' fun x ↦ ⟨rfl, 𝓕₀.is_sol x, 𝓕₀.smooth x, _, _⟩
  · revert x
    exact forall_restrictGermPredicate_of_forall fun x ↦ rfl
  · erw [dist_self]
    exact τ_pos x
have hP₂' : ∀ (t : ℝ) (x : M) (f : M → J¹), P₀ x f → P₂ (t, x) fun p : ℝ × M ↦ f p.2 :=
  sorry

have ind : ∀ m : M,
  ∃ V ∈ 𝓝 m, ∀ K₁ ⊆ V, ∀ K₀ ⊆ interior K₁, IsCompact K₀ → IsCompact K₁ → ∀ (C : Set M) (f : M → J¹),
    IsClosed C → (∀ x, P₀ x f) → (∀ᶠ x in 𝓝ˢ C, P₁ x f) →
      ∃ F : ℝ → M → J¹, (∀ t x, P₀ x (F t)) ∧
                        (∀ᶠ x in 𝓝ˢ (C ∪ K₀), P₁ x (F 1)) ∧
                        (∀ (p : ℝ × M), P₂ p ↿F) ∧
                        (∀ t, ∀ x ∉ K₁, F t x = f x) ∧
                        (∀ᶠ t in 𝓝ˢ (Iic 0), F t = f) ∧
                         ∀ᶠ t in 𝓝ˢ (Ici 1), F t = F 1 := by
  intro m
  rcases hε m with ⟨φ, ψ, ⟨e, rfl⟩, hφψ⟩
  have : φ '' ball e 1 ∈ 𝓝 (φ e) := by
    rw [← φ.openEmbedding.map_nhds_eq]
    exact image_mem_map (ball_mem_nhds e zero_lt_one)
  use φ '' (ball e 1), this ; clear this
  intro K₁ hK₁ K₀ K₀K₁ K₀_cpct K₁_cpct C f C_closed P₀f fC
  replace K₀_cpct : IsCompact (φ ⁻¹' K₀) := by
    have := φ.openEmbedding
    refine isCompact_of_isClosed_isBounded ?hc ?hb
    sorry
  replace K₁_cpct : IsCompact (φ ⁻¹' K₁) := sorry
  have K₀K₁' : φ ⁻¹' K₀ ⊆ interior (φ ⁻¹' K₁) := sorry
  sorry/- simp only [P₀, forall_and] at P₀f
  rcases P₀f with ⟨hf_sec, hf_sol, hf_smooth, hf_A, hf_dist⟩
  rw [forall_restrictGermPredicate_iff] at hf_A
  let F : FormalSol R := mkFormalSol f hf_sec hf_sol hf_smooth
  have hFAC : ∀ᶠ x near A ∪ C, F.IsHolonomicAt x :=
    by
    rw [eventually_nhdsSet_union]
    refine' ⟨_, fC⟩
    apply (hf_A.and h𝓕₀).eventually_nhdsSet.mono fun x hx ↦ ?_
    rw [eventually_and] at hx
    apply hx.2.self_of_nhds.congr
    apply hx.1.mono fun x' hx' ↦ ?_
    simp [F]
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
  have η_cont : Continuous η :=
    by
    have : ContMDiff IM ((IM.prod IX).prod 𝓘(ℝ, EM →L[ℝ] EX)) ∞ f := fun x ↦ hf_smooth x
    apply τ_cont.sub
    exact (one_jet_bundle_proj_continuous.comp this.continuous).snd.dist 𝓕₀.smooth_bs.continuous
  rcases φ.improve_formalSol ψ hRample hRopen (hA.union C_closed) η_pos η_cont hFφψ hFAC K₀_cpct
      K₁_cpct K₀K₁' with
    ⟨F', hF'₀, hF'₁, hF'AC, hF'K₁, hF'η, hF'hol⟩
  refine' ⟨fun t x ↦ F' t x, _, _, _, _, _, _⟩ ; all_goals beta_reduce
  · refine' fun t x ↦ ⟨rfl, F'.is_sol, (F' t).smooth x, _, _⟩
    · revert x
      rw [forall_restrictGermPredicate_iff]
      rw [eventually_nhdsSet_union] at hF'AC
      apply (hF'AC.1.and hf_A).mono
      rintro x ⟨hx, hx'⟩
      change F' t x = _
      rw [hx t, ← hx', mkFormalSol_apply]
      rfl
    · calc
        dist (F' t x).1.2 (𝓕₀.bs x) ≤ dist (F' t x).1.2 (F.bs x) + dist (F.bs x) (𝓕₀.bs x) :=
          dist_triangle _ _ _
        _ < η x + dist (F.bs x) (𝓕₀.bs x) := (add_lt_add_right (hF'η t x) _)
        _ = τ x := by simp [η]
  · have : K₀ ⊆ range φ := K₀K₁.trans interior_subset |>.trans <| SurjOn.subset_range hK₁
    rw [union_assoc, eventually_nhdsSet_union, image_preimage_eq_of_subset this] at hF'hol
    exact hF'hol.2
  · exact F'.smooth
  · intro t x hx
    replace hx : x ∉ φ '' (φ ⁻¹' K₁) := by
      rwa [image_preimage_eq_of_subset (SurjOn.subset_range hK₁)]
    simpa using hF'K₁ t x hx
  · apply hF'₀.mono fun x hx ↦ ?_
    erw [hx]
    ext1 y
    simp [F]
  · apply hF'₁.mono fun x hx ↦ ?_
    rw [hx] -/

/- rcases inductive_htpy_construction' P₀ P₁ P₂ hP₂ hP₂' init ind with ⟨F, hF₀, hFP₀, hFP₁, hFP₂⟩
simp only [P₀, forall₂_and_distrib] at hFP₀
rcases hFP₀ with ⟨hF_sec, hF_sol, _hF_smooth, hF_A, hF_dist⟩
refine' ⟨mkHtpyFormalSol F hF_sec hF_sol hFP₂, _, _, _, _⟩
· intro x
  rw [mkHtpyFormalSol_apply, hF₀]
· exact hFP₁
· intro x hx t
  rw [mkHtpyFormalSol_apply]
  exact (forall_restrictGermPredicate_iff.mp <| hF_A t).on_set x hx
· intro t x
  change dist (mkHtpyFormalSol F hF_sec hF_sol hFP₂ t x).1.2 (𝓕₀.bs x) ≤ δ x
  rw [mkHtpyFormalSol_apply]
  exact (hF_dist t x).le.trans (min_le_left _ _) -/

theorem RelMfld.Ample.satisfiesHPrinciple (hRample : R.Ample) (hRopen : IsOpen R) (hA : IsClosed A)
    (hδ_pos : ∀ x, 0 < δ x) (hδ_cont : Continuous δ) : R.SatisfiesHPrinciple A δ := by
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
  let L : LocalisationData IM IX 𝓕₀.bs := stdLocalisationData EM IM EX IX cont
  let K : IndexType L.N → Set M := fun i ↦ L.φ i '' closedBall (0 : EM) 1
  let U : IndexType L.N → Set M := fun i ↦ range (L.φ i)
  have K_cover : (⋃ i, K i) = univ :=
    eq_univ_of_subset (iUnion_mono fun i ↦ image_subset _ ball_subset_closedBall) L.h₁
  let τ := fun x : M ↦ min (δ x) (L.ε x)
  have τ_pos : ∀ x, 0 < τ x := fun x ↦ lt_min (hδ_pos x) (L.ε_pos x)
  have τ_cont : Continuous τ := hδ_cont.min L.ε_cont
  have := fun (x : M) (F' : Germ (𝓝 x) J¹) ↦ F'.value = 𝓕₀ x
  let P₀ : ∀ x : M, Germ (𝓝 x) J¹ → Prop := fun x F ↦
    F.value.1.1 = x ∧
      F.value ∈ R ∧
        F.ContMDiffAt' IM ((IM.prod IX).prod 𝓘(ℝ, EM →L[ℝ] EX)) ∞ ∧
          RestrictGermPredicate (fun x F' ↦ F'.value = 𝓕₀ x) A x F ∧
            dist F.value.1.2 (𝓕₀.bs x) < τ x
  let P₁ : ∀ x : M, Germ (𝓝 x) J¹ → Prop := fun x F ↦ IsHolonomicGerm F
  let P₂ : ∀ p : ℝ × M, Germ (𝓝 p) J¹ → Prop := fun p F ↦
    F.ContMDiffAt' (𝓘(ℝ).prod IM) ((IM.prod IX).prod 𝓘(ℝ, EM →L[ℝ] EX)) ∞
  have hP₂ :
    ∀ (a b : ℝ) (p : ℝ × M) (f : ℝ × M → OneJetBundle IM M IX X),
      P₂ (a * p.1 + b, p.2) f → P₂ p fun p : ℝ × M ↦ f (a * p.1 + b, p.2) :=
    by
    rintro a b ⟨t, x⟩ f h
    change ContMDiffAt _ _ _ (f ∘ fun p : ℝ × M ↦ (a * p.1 + b, p.2)) (t, x)
    change ContMDiffAt _ _ _ f ((fun p : ℝ × M ↦ (a * p.1 + b, p.2)) (t, x)) at h
    have :
      ContMDiffAt (𝓘(ℝ, ℝ).prod IM) (𝓘(ℝ, ℝ).prod IM) ∞ (fun p : ℝ × M ↦ (a * p.1 + b, p.2))
        (t, x) :=
      haveI h₁ : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun t ↦ a * t + b) t :=
        contMDiffAt_iff_contDiffAt.mpr
          (((contDiffAt_id : ContDiffAt ℝ ∞ id t).const_smul a).add contDiffAt_const)
      h₁.prod_map contMDiffAt_id
    exact h.comp (t, x) this
  have init : ∀ x : M, P₀ x (𝓕₀ : M → J¹) :=
    by
    refine' fun x ↦ ⟨rfl, 𝓕₀.is_sol x, 𝓕₀.smooth x, _, _⟩
    · revert x
      exact forall_restrictGermPredicate_of_forall fun x ↦ rfl
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
                  (∀ t, ∀ x ∉ U i, F t x = f x) ∧
                    (∀ᶠ t near Iic 0, F t = f) ∧ ∀ᶠ t near Ici 1, F t = F 1 :=
    by
    intro i f hf₀ hf₁
    let K₀ : Set EM := closedBall 0 1
    have hK₀ : IsCompact K₀ := isCompact_closedBall 0 1
    let K₁ : Set EM := closedBall 0 2
    have hK₁ : IsCompact K₁ := isCompact_closedBall 0 2
    have hK₀K₁ : K₀ ⊆ interior K₁ := by
      dsimp [K₀, K₁]
      rw [interior_closedBall (0 : EM) (by norm_num : (2 : ℝ) ≠ 0)]
      exact closedBall_subset_ball (by norm_num)
    let C := ⋃ j < i, L.φ j '' closedBall 0 1
    have hC :
      IsClosed C :=-- TODO: rewrite localization_data.is_closed_Union to match this.
        (finite_Iio _).isClosed_biUnion fun j _hj ↦ (hK₀.image <| (L.φ j).continuous).isClosed
    simp only [P₀, forall_and] at hf₀
    rcases hf₀ with ⟨hf_sec, hf_sol, hf_smooth, hf_A, hf_dist⟩
    rw [forall_restrictGermPredicate_iff] at hf_A
    let F : FormalSol R := mkFormalSol f hf_sec hf_sol hf_smooth
    have hFAC : ∀ᶠ x near A ∪ C, F.IsHolonomicAt x :=
      by
      rw [eventually_nhdsSet_union]
      refine' ⟨_, hf₁⟩
      apply (hf_A.and h𝓕₀).eventually_nhdsSet.mono fun x hx ↦ ?_
      rw [eventually_and] at hx
      apply hx.2.self_of_nhds.congr
      apply hx.1.mono fun x' hx' ↦ ?_
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
    let η : M → ℝ := fun x ↦ τ x - dist (f x).1.2 (𝓕₀.bs x)
    have η_pos : ∀ x, 0 < η x := fun x ↦ sub_pos.mpr (hf_dist x)
    have η_cont : Continuous η :=
      by
      have : ContMDiff IM ((IM.prod IX).prod 𝓘(ℝ, EM →L[ℝ] EX)) ∞ f := fun x ↦ hf_smooth x
      apply τ_cont.sub
      exact (one_jet_bundle_proj_continuous.comp this.continuous).snd.dist 𝓕₀.smooth_bs.continuous
    rcases(L.φ i).improve_formalSol (L.ψj i) hRample hRopen (hA.union hC) η_pos η_cont hFφψ hFAC hK₀
        hK₁ hK₀K₁ with
      ⟨F', hF'₀, hF'₁, hF'AC, hF'K₁, hF'η, hF'hol⟩
    refine' ⟨fun t x ↦ F' t x, _, _, _, _, _, _⟩ ; all_goals beta_reduce
    · refine' fun t x ↦ ⟨rfl, F'.is_sol, (F' t).smooth x, _, _⟩
      · revert x
        rw [forall_restrictGermPredicate_iff]
        rw [eventually_nhdsSet_union] at hF'AC
        apply (hF'AC.1.and hf_A).mono
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
    · rw [union_assoc, eventually_nhdsSet_union] at hF'hol
      replace hF'hol := hF'hol.2
      simp_rw [← L.iUnion_succ'] at hF'hol
      exact hF'hol
    · exact F'.smooth
    · intro t x hx
      rw [hF'K₁ t x ((mem_range_of_mem_image _ _).mt hx)]
      simp [F]
    · apply hF'₀.mono fun x hx ↦ ?_
      erw [hx]
      ext1 y
      simp [F]
    · apply hF'₁.mono fun x hx ↦ ?_
      rw [hx]
  rcases inductive_htpy_construction P₀ P₁ P₂ hP₂ L.lf_φ K_cover init (𝓕₀.smooth.comp contMDiff_snd)
      ind with
    ⟨F, hF₀, hFP₀, hFP₁, hFP₂⟩
  simp only [P₀, forall₂_and_distrib] at hFP₀
  rcases hFP₀ with ⟨hF_sec, hF_sol, _hF_smooth, hF_A, hF_dist⟩
  refine' ⟨mkHtpyFormalSol F hF_sec hF_sol hFP₂, _, _, _, _⟩
  · intro x
    rw [mkHtpyFormalSol_apply, hF₀]
  · exact hFP₁
  · intro x hx t
    rw [mkHtpyFormalSol_apply]
    exact (forall_restrictGermPredicate_iff.mp <| hF_A t).on_set x hx
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
    R.SatisfiesHPrincipleWith IP C δ := by
  have hδ_pos' : ∀ x : P × M, 0 < δ x.2 := fun x : P × M ↦ hδ_pos x.snd
  have hδ_cont' : Continuous fun x : P × M ↦ δ x.2 := hδ_cont.comp continuous_snd
  have is_op : IsOpen (RelMfld.relativize IP P R) := R.isOpen_relativize hRopen
  apply RelMfld.SatisfiesHPrinciple.satisfiesHPrincipleWith
  exact (hRample.relativize IP P).satisfiesHPrinciple is_op hC hδ_pos' hδ_cont'

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
    R.SatisfiesHPrincipleWith IP C δ := by
  letI := manifoldMetric I' M'
  apply RelMfld.Ample.satisfiesHPrincipleWith <;> assumption
