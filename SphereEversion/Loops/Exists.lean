import SphereEversion.Loops.Reparametrization
import SphereEversion.ToMathlib.Analysis.CutOff
import Mathlib.Topology.MetricSpace.HausdorffDistance

noncomputable section

open Set Function Int Metric Filter Real MeasureTheory
open scoped  MeasureTheory.Measure Topology unitInterval ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : Type*} [NormedAddCommGroup F]
  {g b : E → F} {Ω : Set (E × F)} {U K C : Set E}

variable [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exist_loops_aux1 (hK : IsCompact K) (hΩ_op : IsOpen Ω) (hb : 𝒞 ∞ b)
    (hgK : ∀ᶠ x near K, g x = b x)
    (hconv : ∀ x, g x ∈ hull (connectedComponentIn (Prod.mk x ⁻¹' Ω) <| b x)) :
    ∃ γ : E → ℝ → Loop F,
      ∃ V ∈ 𝓝ˢ K,
        ∃ ε > 0,
          SurroundingFamilyIn g b γ V Ω ∧
            (∀ x ∈ V, ball (x, b x) (ε + ε) ⊆ Ω) ∧ ∀ x ∈ V, ∀ (t s), dist (γ x t s) (b x) < ε := by
  have b_in : ∀ x, (x, b x) ∈ Ω := fun x ↦
    (connectedComponentIn_nonempty_iff.mp (convexHull_nonempty_iff.mp ⟨g x, hconv x⟩) : _)
  -- we could probably get away with something simpler to get γ₀.
  obtain
    ⟨γ₀, hγ₀_cont, hγ₀, h2γ₀, h3γ₀, -, hγ₀_surr⟩ :=-- γ₀ is γ* in notes
      surrounding_loop_of_convexHull
      isOpen_univ isConnected_univ (by rw [convexHull_univ]; exact mem_univ 0) (mem_univ (0 : F))
  obtain ⟨ε₀, hε₀, V, hV, hεΩ⟩ :=
    hK.exists_thickening_image_subset hΩ_op
      (fun x hx ↦ (continuous_id.prodMk hb.continuous).continuousAt) fun x _ ↦ b_in x
  let range_γ₀ := (fun i : ℝ × ℝ ↦ ‖γ₀ i.1 i.2‖) '' I ×ˢ I
  have h4γ₀ : BddAbove range_γ₀ :=
    (isCompact_Icc.prod isCompact_Icc).bddAbove_image (by fun_prop)
  have h0 : 0 < 1 + sSup range_γ₀ :=
    add_pos_of_pos_of_nonneg zero_lt_one
      (le_csSup_of_le h4γ₀
          (mem_image_of_mem _ <| mk_mem_prod unitInterval.zero_mem unitInterval.zero_mem) <|
        norm_nonneg _)
  generalize h0ε₁ : ε₀ / 2 = ε₁
  have hε₁ : 0 < ε₁ := h0ε₁ ▸ div_pos hε₀ two_pos
  let ε := ε₁ / (1 + sSup range_γ₀)
  have hε : 0 < ε := div_pos hε₁ h0
  have h2ε : ∀ t s : ℝ, ‖ε • γ₀ t s‖ < ε₁ := by
    intro t s
    simp only [ε, norm_smul, Real.norm_eq_abs, abs_eq_self.mpr hε.le, mul_comm_div]
    refine lt_of_lt_of_le ?_ (mul_one _).le
    rw [mul_lt_mul_iff_right₀ hε₁, div_lt_one h0]
    refine (zero_add _).symm.le.trans_lt (add_lt_add_of_lt_of_le zero_lt_one (le_csSup h4γ₀ ?_))
    rw [← Loop.fract_eq, ← h3γ₀]
    exact mem_image_of_mem _ (mk_mem_prod projI_mem_Icc <| unitInterval.fract_mem _)
  let γ₁ : E → ℝ → Loop F := fun x t ↦ (γ₀ t).transform fun y ↦ b x + ε • y
  -- `γ₁ x` is `γₓ` in notes
  refine ⟨γ₁, ?_⟩
  have hbV : ∀ᶠ x near K, x ∈ V := hV
  have h1 : ∀ x ∈ V, ∀ (_t _s : ℝ), ball (x, b x) (ε₁ + ε₁) ⊆ Ω := by
    intro x hx _t _s
    simp only [← h0ε₁, add_halves]
    exact (ball_subset_thickening (mem_image_of_mem _ hx) _).trans hεΩ
  refine ⟨_, hgK.and hbV, ε₁, hε₁, ⟨⟨by simp [γ₁, hγ₀], by simp [γ₁, h2γ₀],
    ?_, ?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · intro x t s; simp [γ₁, h3γ₀]
  · rintro x ⟨hx, -⟩; simp_rw [γ₁, hx]
    exact (hγ₀_surr.smul0 hε.ne').vadd0
  · exact hb.continuous.fst'.add (continuous_const.smul <| hγ₀_cont.snd')
  · rintro x ⟨-, hx⟩ t _ht s _hs
    have : ‖ε • γ₀ t s‖ < ε₀ := (h2ε t s).trans (h0ε₁ ▸ half_lt_self hε₀)
    exact h1 x hx t s (by simpa [γ₁, ← h0ε₁])
  · intro x hx
    rw [← h0ε₁, add_halves]
    exact (ball_subset_thickening (mem_image_of_mem _ hx.2) _).trans hεΩ
  · rintro x ⟨-, -⟩ t s
    simp [γ₁, h2ε]

attribute [fun_prop] Continuous.infDist Continuous.if_const

/- Some remarks about `exist_loops_aux2`:
  `δ`: loop after smoothing
  `γ`: loop before smoothing (defined on all of `E`)
  Requirements:
  (0) `δ x t` is a loop
  (1) `δ` lands in `Ω`
  (2) `δ` has the correct values: for `s = 0` and `t = 0` it should be `b`
  (3) `δ` should be constant on `t ≤ 0` and for `t ≥ 1`.
  (4) `δ x 1` surrounds `g x`.
  (5) Near `K`, the line connecting `b` and `δ` lies in `Ω`

  Strategy:
  (a) We need `ε₁` satisfying the following conditions:
  (a1) We need to ensure that an `ε₁ x`-ball around `(x, δ x s t)` lies in `Ω` for some
    continuous `ε₁`.
  (a4) Furthermore, `ε₁` should be small enough so that any function with that
    distance from `γ` still surrounds `g`, using `SurroundingFamily.surrounds_of_close`.
  (a5): `ε₁ x < ε₀` (obtained from `exist_loops_aux1`)
  (b) Replace `γ x t s` by `γ x (linearReparam t) (linearReparam s)`.
  (e) Let `δ' x` be a family of loops that is at most `ε₁` away from `γ` using
    `exists_smooth_and_eqOn`. Since `γ` is smooth near `s ∈ ℤ` and `t ≤ 0` we can also
    ensure that `δ' = γ` for those values (*).
    Now let `δ x t s = δ' x (smoothTransition t) (fract s)`
    We immediately get (0) and (3). We get (2) by (*).
    This is still smooth, since `δ'` is doesn't depend on `s` near `s ∈ ℤ`.
  (f) (a1) gives (1), (a4) gives (4) and (a5) gives (5).

  Note: to ensure (2) the reparamerization strategy that was originally in the blueprint
  (ensuring that `γ` is locally constant in the `t` and `s` directions)
  didn't work. Indeed it needed to take the convolution in the `x`-direction,
  meaning that the value won't stay the same, since `γ` is not constant in the `x`-direction.
-/
theorem exist_loops_aux2 [FiniteDimensional ℝ E] (hK : IsCompact K) (hΩ_op : IsOpen Ω) (hg : 𝒞 ∞ g)
    (hb : 𝒞 ∞ b) (hgK : ∀ᶠ x near K, g x = b x)
    (hconv : ∀ x, g x ∈ hull (connectedComponentIn (Prod.mk x ⁻¹' Ω) <| b x)) :
    ∃ γ : E → ℝ → Loop F,
      SurroundingFamilyIn g b γ univ Ω ∧
        𝒞 ∞ ↿γ ∧ ∀ᶠ x near K, ∀ t s, closedBall (x, b x) (dist (γ x t s) (b x)) ⊆ Ω := by
  obtain ⟨γ₁, V, hV, ε₀, hε₀, hγ₁, hΩ, h2γ₁⟩ := exist_loops_aux1 hK hΩ_op hb hgK hconv
  obtain ⟨γ₂, hγ₂, hγ₂₁⟩ :=
    exists_surrounding_loops hK.isClosed hΩ_op (fun x ↦ hg.continuous.continuousAt) hb.continuous
      (fun x ↦ hconv x) ⟨V, hV, hγ₁⟩
  let γ₃ : E → ℝ → Loop F := fun x t ↦ (γ₂ x (linearReparam t)).reparam linearReparam
  have hγ₃ : SurroundingFamilyIn g b γ₃ univ Ω := hγ₂.reparam
  obtain ⟨ε₁, hε₁, hcε₁, hγε₁⟩ := hγ₃.to_sf.surrounds_of_close_univ hg.continuous
  classical
  let f : E → ℝ × ℝ → ℝ := fun x y ↦ if Ωᶜ.Nonempty then infDist (x, γ₃ x y.1 y.2) (Ωᶜ) else 1
  have hI : IsCompact (I ×ˢ I) := isCompact_Icc.prod isCompact_Icc
  have h1f : Continuous ↿f := (continuous_fst.prodMk hγ₃.cont).infDist.if_const _ continuous_const
  have h2f : ∀ x : E, Continuous (f x) := fun x ↦ h1f.comp₂ continuous_const continuous_id
  have h3f : ∀ {x y}, 0 < f x y := by
    intro x y; by_cases hΩ : Ωᶜ.Nonempty
    · simp_rw [f, if_pos hΩ, ← hΩ_op.isClosed_compl.notMem_iff_infDist_pos hΩ, notMem_compl_iff,
        hγ₃.val_in (mem_univ _)]
    · simp_rw [f, if_neg hΩ, zero_lt_one]
  let ε₂ : E → ℝ := fun x ↦ min (min ε₀ (ε₁ x)) (sInf (f x '' I ×ˢ I))
  have hcε₂ : Continuous ε₂ := (continuous_const.min hcε₁).min (hI.continuous_sInf h1f)
  have hε₂ : ∀ {x}, 0 < ε₂ x := fun {x} ↦
    lt_min (lt_min hε₀ (hε₁ x))
      ((hI.lt_sInf_iff_of_continuous
            ((nonempty_Icc.mpr zero_le_one).prod (nonempty_Icc.mpr zero_le_one))
            (h2f x).continuousOn _).mpr
        fun x _ ↦ h3f)
  let γ₄ := ↿γ₃
  have h0γ₄ : ∀ x t s, γ₄ (x, t, s) = γ₃ x t s := fun x t s ↦ rfl
  have hγ₄ : Continuous γ₄ := hγ₃.cont
  let C₁ : Set ℝ := Iic (5⁻¹ : ℝ) ∪ Ici (4 / 5)
  have h0C₁ : (0 : ℝ) ∈ C₁ := Or.inl (by rw [mem_Iic]; norm_num1)
  have h2C₁ : ∀ (s : ℝ) (hs : fract s = 0), fract ⁻¹' C₁ ∈ 𝓝 s := by
    refine fun s hs ↦ fract_preimage_mem_nhds ?_ fun _ ↦ ?_
    · exact hs ▸ mem_of_superset (Iic_mem_nhds <| by norm_num) subset_union_left
    · exact mem_of_superset (Ici_mem_nhds <| by norm_num) subset_union_right
  let C : Set (E × ℝ × ℝ) := (fun x ↦ x.2.1) ⁻¹' Iic (5⁻¹ : ℝ) ∪ (fun x ↦ fract x.2.2) ⁻¹' C₁
  have hC : IsClosed C := by
    refine (isClosed_Iic.preimage continuous_snd.fst).union ?_
    refine ((isClosed_Iic.union isClosed_Ici).preimage_fract ?_).preimage continuous_snd.snd
    exact fun _ ↦ Or.inl (show (0 : ℝ) ≤ 5⁻¹ by norm_num)
  let U₁ : Set ℝ := Iio (4⁻¹ : ℝ) ∪ Ioi (3 / 4)
  let U : Set (E × ℝ × ℝ) := (fun x ↦ x.2.1) ⁻¹' Iio (4⁻¹ : ℝ) ∪ (fun x ↦ fract x.2.2) ⁻¹' U₁
  have hUC : U ∈ 𝓝ˢ C := by
    haveI hU : IsOpen U := by
      refine (isOpen_Iio.preimage continuous_snd.fst).union ?_
      refine ((isOpen_Iio.union isOpen_Ioi).preimage_fract ?_).preimage continuous_snd.snd
      exact fun _ ↦ Or.inr (show (3 / 4 : ℝ) < 1 by norm_num)
    -- Porting note: the following four lines were
    /-
    exact hU.mem_nhds_set.mpr (union_subset_union (λ x hx, lt_of_le_of_lt hx (by norm_num)) $
      union_subset_union (λ x hx, lt_of_le_of_lt hx (by norm_num))
      (λ x hx, lt_of_lt_of_le (by norm_num) hx))
    in Lean 3.
    -/
    apply hU.mem_nhdsSet.mpr
    refine (union_subset_union fun (x : E × ℝ × ℝ)
      (hx : x.2.1 ≤ 5⁻¹) ↦ lt_of_le_of_lt hx (by norm_num)) ?_
    refine union_subset_union (fun (x : E × ℝ × ℝ)
      (hx : fract x.2.2 ≤ 5⁻¹) ↦ lt_of_le_of_lt hx (by norm_num)) ?_
    exact fun x hx ↦ lt_of_lt_of_le (by norm_num : (3 / 4 : ℝ) < 4 / 5) hx
  have h2γ₄ : EqOn γ₄ (fun x ↦ b x.1) U := by
    rintro ⟨x, t, s⟩ hxts
    simp_rw [h0γ₄, γ₃, Loop.reparam_apply]
    obtain (ht | hs) := hxts
    · exact hγ₂.to_sf.t_le_zero_eq_b x (linearReparam s) (linearReparam_nonpos (le_of_lt ht))
    · rw [← Loop.fract_eq, fract_linearReparam_eq_zero, hγ₂.base]
      exact Or.imp le_of_lt le_of_lt hs
  have h3γ₄ : ContDiffOn ℝ ∞ γ₄ U := hb.fst'.contDiffOn.congr h2γ₄
  obtain ⟨γ₅, hγ₅, hγ₅₄, hγ₅C⟩ :=
    exists_smooth_and_eqOn hγ₄ hcε₂.fst' (fun x ↦ hε₂) hC ⟨U, hUC, h3γ₄⟩
  let γ : E → ℝ → Loop F := fun x t ↦
    ⟨fun s ↦ γ₅ (x, smoothTransition t, fract s), fun s ↦ by dsimp; rw [fract_add_one s]⟩
  have hγ : 𝒞 ∞ ↿γ := by
    rw [contDiff_iff_contDiffAt]
    rintro ⟨x, t, s⟩; by_cases hs : fract s = 0
    · have : (fun x ↦ γ x.1 x.2.1 x.2.2) =ᶠ[𝓝 (x, t, s)] fun x ↦ b x.1 := by
        have :
          (fun x : E × ℝ × ℝ ↦ (x.1, smoothTransition x.2.1, fract x.2.2)) ⁻¹' C ∈ 𝓝 (x, t, s) := by
          simp_rw [C, preimage_union, preimage_preimage, fract_fract]
          refine mem_of_superset ?_ subset_union_right
          refine continuousAt_id.snd'.snd'.preimage_mem_nhds (h2C₁ s hs)
        filter_upwards [this] with x hx
        exact (hγ₅C hx).trans
          (h2γ₄ <| (subset_interior_iff_mem_nhdsSet.mpr hUC).trans interior_subset hx)
      exact hb.fst'.contDiffAt.congr_of_eventuallyEq this
    · exact (hγ₅.comp₃ contDiff_fst smoothTransition.contDiff.fst'.snd' <|
          contDiff_snd.snd'.sub contDiff_const).contDiffAt.congr_of_eventuallyEq
        ((EventuallyEq.rfl.prodMk <| EventuallyEq.rfl.prodMk <|
              (fract_eventuallyEq hs).comp_tendsto continuousAt_id.snd'.snd').fun_comp ↿γ₅)
  refine ⟨γ, ⟨⟨?_, ?_, ?_, ?_, hγ.continuous⟩, ?_⟩, hγ, ?_⟩
  · intro x t
    simp_rw [γ, fract_zero]
    rw [hγ₅C]
    · exact hγ₃.base x _
    · exact Or.inr (by rw [mem_preimage, fract_zero]; exact h0C₁)
  · intro x s
    simp_rw [γ, smoothTransition.zero_of_nonpos le_rfl]
    rw [hγ₅C]
    · exact hγ₃.t₀ x (fract s)
    · exact Or.inl (show (0 : ℝ) ≤ 5⁻¹ by norm_num)
  · intro x t s
    simp_rw [γ, smoothTransition_projI]
  · rintro x -
    refine hγε₁ _ _ fun s ↦ ?_
    simp_rw [← (γ₃ x 1).fract_eq s, γ, smoothTransition.one_of_one_le le_rfl]
    exact (hγ₅₄ (x, 1, fract s)).trans_le ((min_le_left _ _).trans <| min_le_right _ _)
  · rintro x - t - s -; rw [← notMem_compl_iff]
    by_cases hΩ : Ωᶜ.Nonempty; swap
    · rw [not_nonempty_iff_eq_empty] at hΩ; rw [hΩ]; apply notMem_empty
    refine notMem_of_dist_lt_infDist (x := ?_) ?_
    · exact (x, γ₃ x (smoothTransition t) (fract s))
    · rw [dist_comm, dist_prod_same_left]
      refine (hγ₅₄ (x, _, fract s)).trans_le ((min_le_right _ _).trans <| csInf_le ?_ ?_)
      · exact (isCompact_Icc.prod isCompact_Icc).bddBelow_image (h2f x).continuousOn
      · rw [← hγ₃.projI]
        simp_rw [f, if_pos hΩ]
        apply mem_image_of_mem _ (mk_mem_prod projI_mem_Icc (unitInterval.fract_mem s))
  · refine eventually_of_mem (Filter.inter_mem hV hγ₂₁) fun x hx t s ↦ ?_
    refine (closedBall_subset_ball ?_).trans (hΩ x hx.1)
    refine (dist_triangle ..).trans_lt (add_lt_add_of_le_of_lt
      ((hγ₅₄ (x, _, fract s)).le.trans <| (min_le_left _ _).trans <| min_le_left ..) ?_)
    simp_rw [γ₄, γ₃, HasUncurry.uncurry, Loop.reparam_apply, show γ₂ x = γ₁ x from hx.2]
    exact h2γ₁ x hx.1 ..

variable (g b Ω U K)

/-- A "nice" family of loops consists of all the properties we want from the `exist_loops` lemma:
it is a smooth homotopy in `Ω` with fixed endpoints from the constant loop at `b x` to a loop with
average `g x` that is also constantly `b x` near `K`.
The first two conditions are implementation specific: the homotopy is constant outside the unit
interval. -/
structure NiceLoop (γ : ℝ → E → Loop F) : Prop where
  t_le_zero : ∀ x, ∀ t ≤ 0, γ t x = γ 0 x
  t_ge_one : ∀ x, ∀ t ≥ 1, γ t x = γ 1 x
  t_zero : ∀ x s, γ 0 x s = b x
  s_zero : ∀ x t, γ t x 0 = b x
  avg : ∀ x, (γ 1 x).average = g x
  mem_Ω : ∀ x t s, (x, γ t x s) ∈ Ω
  smooth : 𝒞 ∞ ↿γ
  rel_K : ∀ᶠ x in 𝓝ˢ K, ∀ t s, γ t x s = b x

variable {g b Ω U K}

theorem exist_loops [FiniteDimensional ℝ E] (hK : IsCompact K) (hΩ_op : IsOpen Ω) (hg : 𝒞 ∞ g)
    (hb : 𝒞 ∞ b) (hgK : ∀ᶠ x near K, g x = b x)
    (hconv : ∀ x, g x ∈ hull (connectedComponentIn (Prod.mk x ⁻¹' Ω) <| b x)) :
    ∃ γ : ℝ → E → Loop F, NiceLoop g b Ω K γ := by
  obtain ⟨γ₁, hγ₁, hsγ₁, h2γ₁⟩ := exist_loops_aux2 hK hΩ_op hg hb hgK hconv
  let γ₂ : SmoothSurroundingFamily g :=
    ⟨hg, fun x ↦ γ₁ x 1, hsγ₁.comp₃ contDiff_fst contDiff_const contDiff_snd, fun x ↦
      hγ₁.surrounds x (mem_univ _)⟩
  classical
  let γ₃ : ℝ → E → Loop F := fun t x ↦ (γ₁ x t).reparam <| (γ₂.reparametrize x).equivariantMap
  have hγ₃ : 𝒞 ∞ ↿γ₃ := hsγ₁.comp₃ contDiff_snd.fst contDiff_fst γ₂.reparametrize_smooth.snd'
  obtain ⟨χ, hχ, h1χ, h0χ, h2χ⟩ :=
    exists_contDiff_one_nhds_of_interior hK.isClosed
      (subset_interior_iff_mem_nhdsSet.mpr <| hgK.and h2γ₁)
  simp_rw [← or_iff_not_imp_left] at h0χ
  let γ : ℝ → E → Loop F := fun t x ↦ χ x • Loop.const (b x) + (1 - χ x) • γ₃ t x
  have h1γ : ∀ x, ∀ t ≤ 0, γ t x = γ 0 x := by
    intro x t ht; ext s;
    simp [γ, γ₃, hγ₁.to_sf.t_le_zero _ _ ht]
  have h2γ : ∀ x, ∀ t ≥ 1, γ t x = γ 1 x := by
    intro x t ht; ext s
    simp [γ, γ₃, hγ₁.to_sf.t_ge_one _ _ ht]
  refine ⟨γ, h1γ, h2γ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x t
    simp [γ, γ₃, hγ₁.t₀]
  · intro x t
    simp [γ, γ₃, hγ₁.base]
  · intro x
    have h1 : IntervalIntegrable (χ x • Loop.const (b x) : Loop F) volume 0 1 := by
      change IntervalIntegrable (fun _ ↦ χ x • b x) volume (0 : ℝ) (1 : ℝ)
      exact intervalIntegrable_const
    have h2 : IntervalIntegrable ((1 - χ x) • γ₃ 1 x : Loop F) volume 0 1 :=
      ((hγ₃.comp₃ contDiff_const contDiff_const contDiff_id).continuous.intervalIntegrable ..).smul
        _
    have h3 : (γ₃ 1 x).average = g x := γ₂.reparametrize_average x
    simp [γ, γ₃, h1, h2, h3]
    rcases h0χ x with (⟨hx, -⟩ | hx)
    · rw [hx, smul_add_one_sub_smul]
    · simp [hx]
  · intro x t s
    have : ∀ (P : F → Prop) (t), (∀ t ∈ I, P (γ t x s)) → P (γ t x s) := by
      intro P t hP
      rcases le_total 0 t with (h1t | h1t); rcases le_total t 1 with (h2t | h2t)
      · exact hP t ⟨h1t, h2t⟩
      · rw [h2γ x t h2t]; exact hP 1 ⟨zero_le_one, le_rfl⟩
      · rw [h1γ x t h1t]; exact hP 0 ⟨le_rfl, zero_le_one⟩
    refine this (fun y ↦ (x, y) ∈ Ω) t fun t _ht ↦ ?_
    rcases h0χ x with (⟨_hx, h2x⟩ | hx)
    · refine h2x t (γ₂.reparametrize x s) ?_
      simp [γ, γ₃, dist_smul_add_one_sub_smul_le (h2χ x)]
    · simp [γ, hx]; exact hγ₁.val_in (mem_univ _)
  · exact (hχ.fst'.snd'.smul hb.fst'.snd').add ((contDiff_const.sub hχ.fst'.snd').smul hγ₃)
  · exact h1χ.mono fun x (hx : χ x = 1) ↦ by simp [γ, hx]
