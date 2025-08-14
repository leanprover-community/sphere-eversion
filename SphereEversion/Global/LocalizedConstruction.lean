import SphereEversion.Global.Localisation
import SphereEversion.Local.HPrinciple

noncomputable section

open Set Filter ModelWithCorners Metric

open scoped Topology Manifold ContDiff

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM]
  {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M] [IsManifold IM ∞ M]
  [T2Space M]
  {EX : Type*} [NormedAddCommGroup EX] [NormedSpace ℝ EX] [FiniteDimensional ℝ EX]
  {HX : Type*} [TopologicalSpace HX] {IX : ModelWithCorners ℝ EX HX}
  {X : Type*} [MetricSpace X] [ChartedSpace HX X] [IsManifold IX ∞ X]

theorem OpenSmoothEmbedding.improve_formalSol (φ : OpenSmoothEmbedding 𝓘(ℝ, EM) EM IM M)
    (ψ : OpenSmoothEmbedding 𝓘(ℝ, EX) EX IX X) {R : RelMfld IM M IX X} (hRample : R.Ample)
    (hRopen : IsOpen R) {C : Set M} (hC : IsClosed C) {δ : M → ℝ} (hδ_pos : ∀ x, 0 < δ x)
    (hδ_cont : Continuous δ) {F : FormalSol R} (hFφψ : F.bs '' range φ ⊆ range ψ)
    (hFC : ∀ᶠ x near C, F.IsHolonomicAt x) {K₀ K₁ : Set EM} (hK₀ : IsCompact K₀)
    (hK₁ : IsCompact K₁) (hK₀K₁ : K₀ ⊆ interior K₁) :
    ∃ F' : HtpyFormalSol R,
      (∀ᶠ t near Iic (0 : ℝ), F' t = F) ∧
        (∀ᶠ t near Ici (1 : ℝ), F' t = F' 1) ∧
          (∀ᶠ x near C, ∀ t, F' t x = F x) ∧
            (∀ t, ∀ x ∉ φ '' K₁, F' t x = F x) ∧
              (∀ t x, dist ((F' t).bs x) (F.bs x) < δ x) ∧
                ∀ᶠ x near C ∪ φ '' K₀, (F' 1).IsHolonomicAt x := by
  let Rloc : RelLoc EM EX := (R.localize φ ψ).relLoc
  have hRloc_op : IsOpen Rloc :=
    isOpen_of_isOpen _ (hRopen.preimage <| OneJetBundle.continuous_transfer _ _)
  have hRloc_ample : Rloc.IsAmple := ample_of_ample _ (hRample.localize _ _)
  -- TODO: try to be consistent about how to state the hFφψ condition
  replace hFφψ : range (F.bs ∘ φ) ⊆ range ψ := by
    rw [range_comp]
    exact hFφψ
  let p : ChartPair IM M IX X :=
    { φ
      ψ
      K₁
      hK₁ }
  rcases p.dist_update' hδ_pos hδ_cont hFφψ with ⟨τ, τ_pos, hτ⟩
  let 𝓕 := F.localize p hFφψ
  let L : Landscape EM :=
    { C := φ ⁻¹' C
      K₀
      K₁
      hC := hC.preimage φ.continuous
      hK₀
      hK₁
      h₀₁ := hK₀K₁ }
  have h𝓕C : ∀ᶠ x : EM near L.C, 𝓕.IsHolonomicAt x := by
    rw [eventually_nhdsSet_iff_forall] at hFC ⊢
    intro e he
    rw [φ.isInducing.nhds_eq_comap, eventually_comap]
    apply (hFC _ he).mono
    rintro x hx e rfl
    exact F.isHolonomicLocalize p hFφψ e hx
  rcases 𝓕.improve_htpy' hRloc_op hRloc_ample L τ_pos h𝓕C with
    ⟨𝓕', h𝓕't0, h𝓕't1, h𝓕'relC, h𝓕'relK₁, h𝓕'dist, h𝓕'hol⟩
  have hcompat : p.compat' F 𝓕' := ⟨hFφψ, h𝓕'relK₁⟩
  let F' : HtpyFormalSol R := p.mkHtpy F 𝓕'
  have hF'relK₁ : ∀ t, ∀ x ∉ φ '' K₁, F' t x = F x := by apply p.mkHtpy_eq_of_not_mem
  have hF't0 : ∀ᶠ t : ℝ near Iic 0, F' t = F := by
    apply h𝓕't0.mono
    rintro t ht
    exact p.mkHtpy_eq_of_forall hcompat ht
  have hF't1 : ∀ᶠ t : ℝ near Ici 1, F' t = F' 1 := h𝓕't1.mono fun t ↦ p.mkHtpy_congr _
  refine ⟨F', hF't0, hF't1, ?_, hF'relK₁, ?_, ?_⟩
  · apply φ.forall_near hK₁ h𝓕'relC (Eventually.of_forall fun x hx t ↦ hF'relK₁ t x hx)
    · intro e he t
      rw [p.mkHtpy_eq_of_eq _ _ hcompat]
      exact he t
  · intro t x
    rcases Classical.em (x ∈ φ '' K₁) with (⟨e, he, rfl⟩ | hx)
    · by_cases ht : t ∈ (Icc 0 1 : Set ℝ)
      · exact hτ hcompat e he t ht (h𝓕'dist e t)
      · rw [mem_Icc, not_and_or, not_le, not_le] at ht
        obtain (ht | ht) := ht
        · erw [hF't0.self_of_nhdsSet t ht.le, dist_self]
          apply hδ_pos
        · rw [hF't1.self_of_nhdsSet t ht.le]
          exact hτ hcompat e he 1 (right_mem_Icc.mpr zero_le_one) (h𝓕'dist e 1)
    · change dist (F' t x).1.2 (F.bs x) < δ x
      erw [p.mkHtpy_eq_of_not_mem _ _ hx, dist_self]
      apply hδ_pos
  · have h𝓕'holC : ∀ᶠ x : EM near L.C, (𝓕' 1).IsHolonomicAt x := by
      apply (h𝓕'relC.eventually_nhdsSet.and h𝓕C).mono
      rintro x ⟨hx, hx'⟩
      exact JetSec.IsHolonomicAt.congr hx' (hx.mono fun x' hx' ↦ (hx' 1).symm)
    have : ∀ᶠ x near φ ⁻¹' C ∪ K₀, (𝓕' 1).IsHolonomicAt x := h𝓕'holC.union h𝓕'hol
    rw [← preimage_image_eq K₀ φ.injective, ← preimage_union] at this
    apply φ.forall_near hK₁ this
    · apply Filter.Eventually.union
      · apply hFC.mono
        intro x hx hx'
        apply hx.congr
        symm
        have : ∀ᶠ y in 𝓝 x, y ∈ (φ '' K₁)ᶜ :=
          isOpen_iff_mem_nhds.mp (hK₁.image φ.continuous).isClosed.isOpen_compl x hx'
        apply this.mono
        exact hF'relK₁ _
      · have : ∀ᶠ x near φ '' K₀, x ∈ p.φ '' K₁ := by
          suffices ∀ᶠ x near φ '' K₀, x ∈ interior (p.φ '' K₁) from this.mono interior_subset
          exact isOpen_interior.mem_nhdsSet.mpr
            ((image_mono hK₀K₁).trans (φ.isOpenMap.image_interior_subset K₁))
        exact this.mono (fun a hx hx' ↦ (hx' hx).elim)
    · exact fun _ ↦ (p.mkHtpy_isHolonomicAt_iff hcompat).mpr
