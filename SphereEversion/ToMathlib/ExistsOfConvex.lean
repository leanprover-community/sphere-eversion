import SphereEversion.ToMathlib.Partition
import Mathlib.Geometry.Manifold.Notation

noncomputable section

open scoped Topology Manifold ContDiff

open Set Function Filter

section

variable {ι : Type*}

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {H : Type*}
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

section

variable {F : Type*} [AddCommGroup F] [Module ℝ F]

theorem exists_of_convex {P : (Σ x : M, Germ (𝓝 x) F) → Prop}
    (hP : ∀ x : M, ReallyConvex (smoothGerm I x) {φ | P ⟨x, φ⟩})
    (hP' : ∀ x : M, ∃ f : M → F, ∀ᶠ x' in 𝓝 x, P ⟨x', f⟩) : ∃ f : M → F, ∀ x, P ⟨x, f⟩ := by
  replace hP' : ∀ x : M, ∃ f : M → F, ∃ U ∈ 𝓝 x, ∀ x' ∈ U, P ⟨x', f⟩ := by
    intro x
    rcases hP' x with ⟨f, hf⟩
    exact ⟨f, {x' | P ⟨x', ↑f⟩}, hf, fun _ ↦ id⟩
  choose φ U hU hφ using hP'
  rcases SmoothBumpCovering.exists_isSubordinate I isClosed_univ fun x _ ↦ hU x with ⟨ι, b, hb⟩
  let ρ := b.toSmoothPartitionOfUnity
  refine ⟨fun x : M ↦ ∑ᶠ i, ρ i x • φ (b.c i) x, fun x₀ ↦ ?_⟩
  let g : ι → Germ (𝓝 x₀) F := fun i ↦ φ (b.c i)
  have :
    (fun x : M ↦ ∑ᶠ i, ρ i x • φ (b.c i) x : Germ (𝓝 x₀) F) ∈
      reallyConvexHull (smoothGerm I x₀) (g '' ρ.fintsupport x₀) :=
    ρ.germ_combine_mem fun i x ↦ φ (b.c i) x
  simp_rw [reallyConvex_iff_hull] at hP
  apply hP x₀; clear hP
  have H : g '' (ρ.fintsupport x₀) ⊆ {φ : (𝓝 x₀).Germ F | P ⟨x₀, φ⟩} := by
    rintro _ ⟨i, hi, rfl⟩
    exact hφ _ _ (hb.toSmoothPartitionOfUnity  i <| (ρ.mem_fintsupport_iff _ i).mp hi)
  exact reallyConvexHull_mono H this

end

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {HG : Type*} [TopologicalSpace HG]
  (IG : ModelWithCorners ℝ G HG) {N : Type*} [TopologicalSpace N] [ChartedSpace HG N]
  [IsManifold IG ∞ N]

variable (I)

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] in
theorem reallyConvex_contMDiffAt (x : M) (n : ℕ∞) :
    ReallyConvex (smoothGerm I x) {φ : Germ (𝓝 x) F | φ.ContMDiffAt I n} := by
  classical
  rw [Nontrivial.reallyConvex_iff]
  rintro w _w_pos w_supp w_sum
  have : (support w).Finite := hasFiniteSupport_of_finsum_eq_one w_sum
  set fin_supp := this.toFinset with H
  have : (support fun i : (𝓝 x).Germ F ↦ w i • i) ⊆ fin_supp := by
    rw [Set.Finite.coe_toFinset]
    exact support_smul_subset_left w id
  rw [finsum_eq_sum_of_support_subset _ this]
  apply Filter.Germ.ContMDiffAt.sum fun φ hφ ↦ (smoothGerm.contMDiffAt _).smul (w_supp ?_)
  simpa [H] using hφ

theorem exists_contMDiff_of_convex {P : M → F → Prop} (hP : ∀ x, Convex ℝ {y | P x y}) {n : ℕ∞}
    (hP' : ∀ x : M, ∃ U ∈ 𝓝 x, ∃ f : M → F, CMDiff[U] n f ∧ ∀ x ∈ U, P x (f x)) :
    ∃ f : M → F, CMDiff n f ∧ ∀ x, P x (f x) := by
  let PP : (Σ x : M, Germ (𝓝 x) F) → Prop := fun p ↦ p.2.ContMDiffAt I n ∧ P p.1 p.2.value
  have hPP : ∀ x : M, ReallyConvex (smoothGerm I x) {φ | PP ⟨x, φ⟩} := fun x ↦ by
    apply ReallyConvex.inter
    · apply reallyConvex_contMDiffAt
    let v : Germ (𝓝 x) F →ₛₗ[smoothGerm.valueRingHom I x] F := Filter.Germ.valueₛₗ I x
    change ReallyConvex (smoothGerm I x) (v ⁻¹' {y | P x y})
    dsimp only [← smoothGerm.valueOrderRingHom_toRingHom] at v
    apply ReallyConvex.preimageₛₗ
    rw [reallyConvex_iff_convex]
    apply hP
  have hPP' : ∀ x, ∃ f : M → F, ∀ᶠ x' in 𝓝 x, PP ⟨x', f⟩ := fun x ↦ by
    rcases hP' x with ⟨U, U_in, f, hf, hf'⟩
    use f
    filter_upwards [eventually_mem_nhds_iff.mpr U_in] with y hy
    exact ⟨hf.contMDiffAt hy, hf' y (mem_of_mem_nhds hy)⟩
  rcases exists_of_convex hPP hPP' with ⟨f, hf⟩
  exact ⟨f, fun x ↦ (hf x).1, fun x ↦ (hf x).2⟩

theorem exists_contDiff_of_convex {P : E → F → Prop} (hP : ∀ x, Convex ℝ {y | P x y}) {n : ℕ∞}
    (hP' : ∀ x : E, ∃ U ∈ 𝓝 x, ∃ f : E → F, ContDiffOn ℝ n f U ∧ ∀ x ∈ U, P x (f x)) :
    ∃ f : E → F, ContDiff ℝ n f ∧ ∀ x, P x (f x) := by
  simp_rw [← contMDiff_iff_contDiff]
  simp_rw [← contMDiffOn_iff_contDiffOn] at hP' ⊢
  exact exists_contMDiff_of_convex _ hP hP'

end

section

variable {E₁ E₂ F : Type*}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

variable {H₁ M₁ H₂ M₂ : Type*}
  [TopologicalSpace H₁] (I₁ : ModelWithCorners ℝ E₁ H₁)
  [TopologicalSpace M₁] [ChartedSpace H₁ M₁] [IsManifold I₁ ∞ M₁]
  [TopologicalSpace H₂] (I₂ : ModelWithCorners ℝ E₂ H₂)
  [TopologicalSpace M₂] [ChartedSpace H₂ M₂] [IsManifold I₂ ∞ M₂]

@[inherit_doc] local notation "𝓒" => ContMDiff (I₁.prod I₂) 𝓘(ℝ, F)

@[inherit_doc] local notation "𝓒_on" => ContMDiffOn (I₁.prod I₂) 𝓘(ℝ, F)

omit [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E₂]
  [IsManifold I₁ ∞ M₁] [IsManifold I₂ ∞ M₂] in
theorem reallyConvex_contMDiffAtProd {x : M₁} (n : ℕ∞) :
    ReallyConvex (smoothGerm I₁ x) {φ : Germ (𝓝 x) (M₂ → F) | φ.ContMDiffAtProd I₁ I₂ n} := by
  classical
  rw [Nontrivial.reallyConvex_iff]
  rintro w _w_pos w_supp w_sum
  set fin_supp := (hasFiniteSupport_of_finsum_eq_one w_sum).toFinset with H
  have : (support fun i : (𝓝 x).Germ (M₂ → F) ↦ w i • i) ⊆ fin_supp := by
    rw [Set.Finite.coe_toFinset]
    exact support_smul_subset_left w id
  rw [finsum_eq_sum_of_support_subset _ this]
  apply Filter.Germ.ContMDiffAtProd.sum
  refine fun φ hφ ↦ (smoothGerm.contMDiffAt _).smul_prod (w_supp ?_)
  simpa [H] using hφ

omit [FiniteDimensional ℝ E₂] [IsManifold I₂ ∞ M₂] in
theorem exists_contMDiff_of_convex₂ {P : M₁ → (M₂ → F) → Prop} [SigmaCompactSpace M₁] [T2Space M₁]
    (hP : ∀ x, Convex ℝ {f | P x f}) {n : ℕ∞}
    (hP' : ∀ x : M₁, ∃ U ∈ 𝓝 x, ∃ f : M₁ → M₂ → F,
      𝓒_on n (uncurry f) (U ×ˢ (univ : Set M₂)) ∧ ∀ y ∈ U, P y (f y)) :
    ∃ f : M₁ → M₂ → F, 𝓒 n (uncurry f) ∧ ∀ x, P x (f x) := by
  let PP : (Σ x : M₁, Germ (𝓝 x) (M₂ → F)) → Prop := fun p ↦
    p.2.ContMDiffAtProd I₁ I₂ n ∧ P p.1 p.2.value
  have hPP : ∀ x : M₁, ReallyConvex (smoothGerm I₁ x) {φ | PP ⟨x, φ⟩} := fun x ↦ by
    apply ReallyConvex.inter
    · apply reallyConvex_contMDiffAtProd
    let v : Germ (𝓝 x) (M₂ → F) →ₛₗ[smoothGerm.valueRingHom I₁ x] M₂ → F := Filter.Germ.valueₛₗ I₁ x
    change ReallyConvex (smoothGerm I₁ x) (v ⁻¹' {y | P x y})
    dsimp only [← smoothGerm.valueOrderRingHom_toRingHom] at v
    apply ReallyConvex.preimageₛₗ
    rw [reallyConvex_iff_convex]
    apply hP
  have hPP' : ∀ x, ∃ f : M₁ → M₂ → F, ∀ᶠ x' in 𝓝 x, PP ⟨x', f⟩ := fun x ↦ by
    rcases hP' x with ⟨U, U_in, f, hf, hf'⟩
    use f
    filter_upwards [eventually_mem_nhds_iff.mpr U_in] with y hy
    exact ⟨fun z ↦ hf.contMDiffAt (prod_mem_nhds hy univ_mem), hf' y (mem_of_mem_nhds hy)⟩
  rcases exists_of_convex hPP hPP' with ⟨f, hf⟩
  exact ⟨f, fun ⟨x, y⟩ ↦ (hf x).1 y, fun x ↦ (hf x).2⟩

omit [FiniteDimensional ℝ E₂] in
theorem exists_contDiff_of_convex₂ {P : E₁ → (E₂ → F) → Prop} (hP : ∀ x, Convex ℝ {f | P x f})
    {n : ℕ∞}
    (hP' : ∀ x : E₁, ∃ U ∈ 𝓝 x, ∃ f : E₁ → E₂ → F,
      ContDiffOn ℝ n (uncurry f) (U ×ˢ (univ : Set E₂)) ∧ ∀ y ∈ U, P y (f y)) :
    ∃ f : E₁ → E₂ → F, ContDiff ℝ n (uncurry f) ∧ ∀ x, P x (f x) := by
  simp_rw [← contMDiffOn_iff_contDiffOn, modelWithCornersSelf_prod] at hP'
  simp_rw [← contMDiff_iff_contDiff, modelWithCornersSelf_prod]
  rw [← chartedSpaceSelf_prod] at hP' ⊢
  -- Why does `simp_rw` not succeed here?
  exact exists_contMDiff_of_convex₂ 𝓘(ℝ, E₁) 𝓘(ℝ, E₂) hP hP'

end

section

variable {ι : Type*}

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {H : Type*}
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

open TopologicalSpace

example {f : E → ℝ} (h : ∀ x : E, ∃ U ∈ 𝓝 x, ∃ ε : ℝ, ∀ x' ∈ U, 0 < ε ∧ ε ≤ f x') :
    ∃ f' : E → ℝ, ContDiff ℝ ∞ f' ∧ ∀ x, 0 < f' x ∧ f' x ≤ f x := by
  let P : E → ℝ → Prop := fun x t ↦ 0 < t ∧ t ≤ f x
  have hP : ∀ x, Convex ℝ {y | P x y} := fun x ↦ convex_Ioc _ _
  apply exists_contDiff_of_convex hP
  intro x
  rcases h x with ⟨U, U_in, ε, hU⟩
  exact ⟨U, U_in, fun _ ↦ ε, contDiffOn_const, hU⟩

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem convex_setOf_imp_eq (P : Prop) (y : F) : Convex ℝ {x : F | P → x = y} := by
  by_cases hP : P <;> simp [hP, convex_singleton, convex_univ]

-- lemma exists_smooth_and_eqOn_aux1 {f : E → F} {ε : E → ℝ} (hf : continuous f)
--   (hε : continuous ε) (h2ε : ∀ x, 0 < ε x) (x₀ : E) :
--   ∃ U ∈ 𝓝 x₀, ∀ x ∈ U, dist (f x₀) (f x) < ε x :=
-- begin
--   have h0 : ∀ x, dist (f x) (f x) < ε x := λ x, by simp_rw [dist_self, h2ε],
--   refine ⟨_, (isOpen_lt (continuous_const.dist hf) hε).mem_nhds $ h0 x₀, λ x hx, hx⟩
-- end
-- lemma exists_smooth_and_eqOn_aux2 {n : ℕ∞} {f : E → F} {ε : E → ℝ} (hf : continuous f)
--   (hε : continuous ε) (h2ε : ∀ x, 0 < ε x)
--   {s : set E} (hs : is_closed s) (hfs : ∃ U ∈ 𝓝ˢ s, cont_diff_on ℝ n f U)
--   (x₀ : E) :
--   ∃ U ∈ 𝓝 x₀, ∀ x ∈ U, dist (f x₀) (f x) < ε x :=
-- begin
--   have h0 : ∀ x, dist (f x) (f x) < ε x := λ x, by simp_rw [dist_self, h2ε],
--   refine ⟨_, (isOpen_lt (continuous_const.dist hf) hε).mem_nhds $ h0 x₀, λ x hx, hx⟩
-- end
theorem exists_smooth_and_eqOn {n : ℕ∞} {f : E → F} {ε : E → ℝ} (hf : Continuous f)
    (hε : Continuous ε) (h2ε : ∀ x, 0 < ε x) {s : Set E} (hs : IsClosed s)
    (hfs : ∃ U ∈ 𝓝ˢ s, ContDiffOn ℝ n f U) :
    ∃ f' : E → F, ContDiff ℝ n f' ∧ (∀ x, dist (f' x) (f x) < ε x) ∧ EqOn f' f s := by
  have h0 : ∀ x, dist (f x) (f x) < ε x := fun x ↦ by simp_rw [dist_self, h2ε]
  let P : E → F → Prop := fun x t ↦ dist t (f x) < ε x ∧ (x ∈ s → t = f x)
  have hP : ∀ x, Convex ℝ {y | P x y} := fun x ↦
    (convex_ball (f x) (ε x)).inter (convex_setOf_imp_eq _ _)
  obtain ⟨f', hf', hPf'⟩ : ∃ f' : E → F, ContDiff ℝ n f' ∧  ∀ x, P x (f' x) := by
    apply exists_contDiff_of_convex hP
    intro x
    obtain ⟨U, hU, hfU⟩ := hfs
    by_cases hx : x ∈ s
    · refine ⟨U, mem_nhdsSet_iff_forall.mp hU x hx, ?_⟩
      exact ⟨f, hfU, fun y _ ↦ ⟨h0 y, fun _ ↦ rfl⟩⟩
    · have : IsOpen {y : E | dist (f x) (f y) < ε y} := isOpen_lt (continuous_const.dist hf) hε
      exact ⟨_, (this.sdiff hs).mem_nhds ⟨h0 x, hx⟩, fun _ ↦ f x, contDiffOn_const, fun y hy ↦
        ⟨hy.1, fun h2y ↦ (hy.2 h2y).elim⟩⟩
  exact ⟨f', hf', fun x ↦ (hPf' x).1, fun x ↦ (hPf' x).2⟩

end
