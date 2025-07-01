import Mathlib.Analysis.Convex.AmpleSet
import SphereEversion.ToMathlib.Analysis.InnerProductSpace.Rotation
import SphereEversion.ToMathlib.Analysis.InnerProductSpace.Dual
import SphereEversion.Local.ParametricHPrinciple

/-!
This is file proves the existence of a sphere eversion from the local verson of the h-principle.

We define the relation of immersions `R = immersion_sphere_rel ⊆ J¹(E, F)` which consist of all
`(x, y, ϕ)` such that if `x` is outside a ball around the origin with chosen radius `R < 1` then
`ϕ` must be injective on `(ℝ ∙ x)ᗮ` (the orthogonal complement of the span of `x`).
We show that `R` is open and ample.

Furthermore, we define a formal solution of sphere eversion that is holonomic near `0` and `1`.
We have to be careful since we're not actually working on the sphere,
but in the ambient space `E ≃ ℝ³`.
See `loc_formal_eversion` for the choice and constaints of the solution.

Finally, we obtain the existence of sphere eversion from the parametric local h-principle,
proven in `Local/ParametricHPrinciple`.
-/


noncomputable section

open Metric Module Set Function RelLoc InnerProductSpace Submodule

open Filter hiding mem_map

open LinearMap (ker)

open scoped Topology RealInnerProductSpace

section SphereEversion

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {F : Type*}
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

@[inherit_doc] local notation "𝕊²" => sphere (0 : E) 1

@[inherit_doc] local notation "dim" => Module.finrank ℝ

@[inherit_doc] local notation "pr[" x "]ᗮ" => projSpanOrthogonal x

@[inherit_doc] local notation "B" => ball (0 : E) 0.9

/-- A map between vector spaces is a immersion viewed as a map on the sphere, when its
derivative at `x ∈ 𝕊²` is injective on the orthogonal complement of `x`
(the tangent space to the sphere). Note that this implies `f` is differentiable at every point
`x ∈ 𝕊²` since otherwise `D f x = 0`.
-/
def SphereImmersion (f : E → F) : Prop :=
  ∀ x ∈ 𝕊², InjOn (D f x) (ℝ ∙ x)ᗮ

variable (E F)

/-- The relation of immersionsof a two-sphere into its ambient Euclidean space. -/
def immersionSphereRel : RelLoc E F :=
  {w : OneJet E F | w.1 ∉ B → InjOn w.2.2 (ℝ ∙ w.1)ᗮ}

@[inherit_doc] local notation "R" => immersionSphereRel E F

variable {E F}

@[simp]
theorem mem_loc_immersion_rel {x y φ} :
    (⟨x, y, φ⟩ : OneJet E F) ∈ immersionSphereRel E F ↔ x ∉ B → InjOn φ (ℝ ∙ x)ᗮ :=
  Iff.rfl

theorem sphereImmersion_of_sol (f : E → F) :
    (∀ x ∈ 𝕊², (x, f x, fderiv ℝ f x) ∈ immersionSphereRel E F) → SphereImmersion f := by
  intro h x x_in
  have : x ∉ B := by
    rw [mem_sphere_zero_iff_norm] at x_in
    norm_num [x_in]
  exact h x x_in this

theorem mem_slice_iff_of_not_mem {x : E} {w : F} {φ : E →L[ℝ] F} {p : DualPair E} (hx : x ∉ B)
    (y : F) : w ∈ slice R p (x, y, φ) ↔ InjOn (p.update φ w) (ℝ ∙ x)ᗮ := by
  change x ∉ B → InjOn (p.update φ w) (ℝ ∙ x)ᗮ ↔ InjOn (p.update φ w) (ℝ ∙ x)ᗮ
  simp_rw [eq_true hx, true_imp_iff]

section AssumeFiniteDimensional

variable [FiniteDimensional ℝ E]

-- The following is extracted from `loc_immersion_rel_open` because it is slow to typecheck
theorem loc_immersion_rel_open_aux {x₀ : E} {y₀ : F} {φ₀ : E →L[ℝ] F} (hx₀ : x₀ ∉ B)
    (H : InjOn φ₀ (ℝ ∙ x₀)ᗮ) :
    ∀ᶠ p : OneJet E F in 𝓝 (x₀, y₀, φ₀),
      ⟪x₀, p.1⟫ ≠ 0 ∧
      Injective ((p.2.2.comp <| (subtypeL (ℝ ∙ p.1)ᗮ).comp pr[p.1]ᗮ).comp (ℝ ∙ x₀)ᗮ.subtypeL) := by
  -- This is true at (x₀, y₀, φ₀) and is an open condition because `p ↦ ⟪x₀, p.1⟫` and
  -- `p ↦ (p.2.2.comp <| (subtypeL (ℝ ∙ p.1)ᗮ).comp pr[p.1]ᗮ).comp j₀` are continuous
  set j₀ := subtypeL (ℝ ∙ x₀)ᗮ
  let f : OneJet E F → ℝ × ((ℝ ∙ x₀)ᗮ →L[ℝ] F) := fun p ↦
    (⟪x₀, p.1⟫, (p.2.2.comp <| (subtypeL (ℝ ∙ p.1)ᗮ).comp pr[p.1]ᗮ).comp j₀)
  let P : ℝ × ((ℝ ∙ x₀)ᗮ →L[ℝ] F) → Prop := fun q ↦ q.1 ≠ 0 ∧ Injective q.2
  have x₀_ne : x₀ ≠ 0 := by
    refine fun hx₀' ↦ hx₀ ?_
    rw [hx₀']
    apply mem_ball_self
    norm_num
  -- The following suffices looks stupid but is much faster than using the change tactic.
  suffices ∀ᶠ p : OneJet E F in 𝓝 (x₀, y₀, φ₀), P (f p) by exact this
  have hf : ContinuousAt (fun x ↦ f x) (x₀, y₀, φ₀) := by
    refine (continuousAt_const.inner continuousAt_fst).prodMk ?_
    apply ContinuousAt.compL
    · apply ContinuousAt.compL
      exact continuousAt_snd.comp continuousAt_snd
      -- Faster than change.
      suffices ContinuousAt ((fun x ↦ (ℝ ∙ x)ᗮ.subtypeL.comp pr[x]ᗮ) ∘ Prod.fst) (x₀, y₀, φ₀) by
        exact this
      apply ContinuousAt.comp _ continuousAt_fst
      exact continuousAt_orthogonalProjection_orthogonal x₀_ne
    exact continuousAt_const
  have hP : IsOpen {y | P y} :=
    (continuous_fst.isOpen_preimage _ isOpen_compl_singleton).inter
      (continuous_snd.isOpen_preimage _ ContinuousLinearMap.isOpen_injective)
  have : P (f (x₀, y₀, φ₀)) := by
    constructor
    · change ⟪x₀, x₀⟫ ≠ 0
      apply inner_self_eq_zero.not.mpr x₀_ne
    · change Injective (φ₀ ∘ (Subtype.val : (ℝ ∙ x₀)ᗮ → E) ∘ (orthogonalProjection (ℝ ∙ x₀)ᗮ) ∘
        (Subtype.val : (ℝ ∙ x₀)ᗮ → E))
      erw [orthogonalProjection_comp_coe, comp_id]
      exact injOn_iff_injective.mp H
  exact hf (isOpen_iff_mem_nhds.mp hP _ this)

theorem loc_immersion_rel_open : IsOpen (immersionSphereRel E F) := by
  dsimp only [immersionSphereRel]
  rw [isOpen_iff_mem_nhds]
  rintro ⟨x₀, y₀, φ₀⟩ (H : x₀ ∉ B → InjOn φ₀ (ℝ ∙ x₀)ᗮ)
  change ∀ᶠ p : OneJet E F in 𝓝 (x₀, y₀, φ₀), _
  by_cases hx₀ : x₀ ∈ B
  · have : ∀ᶠ p : OneJet E F in 𝓝 (x₀, y₀, φ₀), p.1 ∈ B := by
      rw [nhds_prod_eq]
      exact (isOpen_ball.eventually_mem hx₀).prod_inl ..
    apply this.mono
    rintro ⟨x, y, φ⟩ (hx : x ∈ B) (Hx : x ∉ B)
    exact (Hx hx).elim
  · replace H := H hx₀
    set j₀ := subtypeL (ℝ ∙ x₀)ᗮ
    let f : OneJet E F → ℝ × ((ℝ ∙ x₀)ᗮ →L[ℝ] F) := fun p ↦
      (⟪x₀, p.1⟫, (p.2.2.comp <| (subtypeL (ℝ ∙ p.1)ᗮ).comp pr[p.1]ᗮ).comp j₀)
    let P : ℝ × ((ℝ ∙ x₀)ᗮ →L[ℝ] F) → Prop := fun q ↦ q.1 ≠ 0 ∧ Injective q.2
    have : ∀ᶠ p : OneJet E F in 𝓝 (x₀, y₀, φ₀), P (f p) := loc_immersion_rel_open_aux hx₀ H
    apply this.mono
    rintro ⟨x, y, φ⟩ ⟨hxx₀ : ⟪x₀, x⟫ ≠ 0, Hφ⟩ _
    change InjOn φ (ℝ ∙ x)ᗮ
    have : range (subtypeL (ℝ ∙ x)ᗮ ∘ pr[x]ᗮ ∘ j₀) = (ℝ ∙ x)ᗮ := by
      rw [Function.Surjective.range_comp]
      exact Subtype.range_coe
      exact (orthogonalProjectionOrthogonalLineIso hxx₀).surjective
    rw [← this]
    exact Function.Injective.injOn_range Hφ

variable [FiniteDimensional ℝ F]

-- In the next lemma the assumption `dim E = n + 1` is for convenience
-- using `finrank_orthogonal_span_singleton`. We could remove it to treat empty spheres...
theorem loc_immersion_rel_ample (n : ℕ) [Fact (dim E = n + 1)] (h : finrank ℝ E ≤ finrank ℝ F) :
    (immersionSphereRel E F).IsAmple := by
  classical
  -- gives a minor speedup
  rw [isAmple_iff]
  rintro ⟨x, y, φ⟩ p h_mem
  by_cases hx : x ∈ B
  · apply ample_slice_of_forall
    intro w
    simp only [hx, mem_loc_immersion_rel, not_true, IsEmpty.forall_iff]
  have x_ne : x ≠ 0 := by
    rintro rfl
    apply hx
    apply mem_ball_self
    norm_num1
  have hφ : InjOn φ (ℝ ∙ x)ᗮ := h_mem hx
  clear h_mem
  let u : E := (InnerProductSpace.toDual ℝ E).symm p.π
  have u_ne : u ≠ 0 := (InnerProductSpace.toDual ℝ E).symm.apply_ne_zero p.pi_ne_zero
  by_cases H : ker p.π = (ℝ ∙ x)ᗮ
  · have key : ∀ w, EqOn (p.update φ w) φ (ℝ ∙ x)ᗮ := by
      intro w x
      rw [← H]
      exact p.update_ker_pi φ w
    exact ample_slice_of_forall _ p fun w _ ↦ hφ.congr (key w).symm
  obtain ⟨v', v'_in, hv', hπv'⟩ :
    ∃ v' : E, v' ∈ (ℝ ∙ x)ᗮ ∧ ((ℝ ∙ x)ᗮ = ker p.π ⊓ (ℝ ∙ x)ᗮ ⊔ ℝ ∙ v') ∧ p.π v' = 1 := by
    have ne_z : p.π (pr[x]ᗮ u) ≠ 0 := by
      rw [← toDual_symm_apply]
      change ¬⟪u, pr[x]ᗮ u⟫ = 0
      rw [inner_projection_self_eq_zero_iff.not]
      contrapose! H
      rw [orthogonal_orthogonal] at H
      rw [← orthogonal_span_toDual_symm, spanOrthogonal, spanLine,
          span_singleton_eq_span_singleton_of_ne u_ne H]
    have ne_z' : (p.π <| pr[x]ᗮ u)⁻¹ ≠ 0 := inv_ne_zero ne_z
    refine ⟨(p.π <| pr[x]ᗮ u)⁻¹ • (pr[x]ᗮ u : E), (ℝ ∙ x)ᗮ.smul_mem _ (pr[x]ᗮ u).2, ?_, ?_⟩
    · rw [← orthogonal_span_toDual_symm p.π, span_singleton_smul_eq ne_z'.isUnit]
      exact (orthogonal_line_inf_sup_line u x).symm
    rw [p.π.map_smul, smul_eq_mul, inv_mul_cancel₀ ne_z]
  let p' : DualPair E :=
    { π := p.π
      v := v'
      pairing := hπv' }
  apply ample_slice_of_ample_slice (show p'.π = p.π from rfl)
  suffices slice R p' (x, y, φ) = (map φ (ker p.π ⊓ (ℝ ∙ x)ᗮ) : Set F)ᶜ by
    rw [this]
    apply AmpleSet.of_one_lt_codim
    let Φ := φ.toLinearMap
    suffices 2 ≤ dim (F ⧸ map Φ (ker p.π ⊓ (ℝ ∙ x)ᗮ)) by
      rw [← finrank_eq_rank]
      exact_mod_cast this
    apply le_of_add_le_add_right
    rw [Submodule.finrank_quotient_add_finrank (map Φ <| ker p.π ⊓ (ℝ ∙ x)ᗮ)]
    have : dim (ker p.π ⊓ (ℝ ∙ x)ᗮ : Submodule ℝ E) + 1 = n := by
      have eq := Submodule.finrank_sup_add_finrank_inf_eq (ker p.π ⊓ (ℝ ∙ x)ᗮ) (span ℝ {v'})
      have eq₁ : dim (ℝ ∙ x)ᗮ = n := finrank_orthogonal_span_singleton x_ne
      have eq₂ : ker p.π ⊓ (ℝ ∙ x)ᗮ ⊓ span ℝ {v'} = (⊥ : Submodule ℝ E) := by
        erw [inf_left_right_swap, inf_comm, ← inf_assoc, p'.inf_eq_bot, bot_inf_eq]
      have eq₃ : dim (span ℝ {v'}) = 1 := finrank_span_singleton p'.v_ne_zero
      rw [← hv', eq₁, eq₃, eq₂] at eq
      simpa only [finrank_bot] using eq.symm
    have : dim E = n + 1 := Fact.out
    linarith [finrank_map_le Φ (ker p.π ⊓ (ℝ ∙ x)ᗮ)]
  ext w
  rw [mem_slice_iff_of_not_mem hx y]
  rw [injOn_iff_injective]
  let j := (ℝ ∙ x)ᗮ.subtypeL
  let p'' : DualPair (ℝ ∙ x)ᗮ := ⟨p.π.comp j, ⟨v', v'_in⟩, hπv'⟩
  have eq : ((ℝ ∙ x)ᗮ : Set E).restrict (p'.update φ w) = p''.update (φ.comp j) w := by
    ext z
    simp only [p', j, DualPair.update, restrict_apply, ContinuousLinearMap.add_apply, p'',
      ContinuousLinearMap.coe_comp', coe_subtypeL', Submodule.coe_subtype, comp_apply]
  have eq' : map (φ.comp j) (ker p''.π) = map φ (ker p.π ⊓ (ℝ ∙ x)ᗮ) := by
    have : map (↑j) (ker p''.π) = ker p.π ⊓ (ℝ ∙ x)ᗮ := by
      ext z
      simp only [mem_map, LinearMap.mem_ker, mem_inf]
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact ⟨ht, t.2⟩
      · rintro ⟨hz, z_in⟩
        exact ⟨⟨z, z_in⟩, hz, rfl⟩
    erw [← this, map_comp]
    rfl
  rw [eq, p''.injective_update_iff, mem_compl_iff, eq']
  · exact Iff.rfl
  rw [← show ((ℝ ∙ x)ᗮ : Set E).restrict φ = φ.comp j by ext; rfl]
  exact hφ.injective

end AssumeFiniteDimensional

/-- The main ingredient of the linear map in the formal eversion of the sphere. -/
def locFormalEversionAuxφ [Fact (dim E = 3)] (ω : Orientation ℝ E (Fin 3)) (t : ℝ) (x : E) :
    E →L[ℝ] E :=
  ω.rot (t, x) - (2 * t) • Submodule.subtypeL (ℝ ∙ x) ∘L orthogonalProjection (ℝ ∙ x)

section AssumeFiniteDimensional
local notation "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

variable [Fact (dim E = 3)] [FiniteDimensional ℝ E] (ω : Orientation ℝ E (Fin 3))

theorem smooth_at_locFormalEversionAuxφ {p : ℝ × E} (hx : p.2 ≠ 0) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (uncurry (locFormalEversionAuxφ ω)) p := by
  apply ContDiffAt.of_le _ le_top
  refine (ω.contDiff_rot hx).sub ?_
  refine ContDiffAt.smul (contDiffAt_const.mul contDiffAt_fst) ?_
  exact (contDiffAt_orthogonalProjection_singleton hx).comp p contDiffAt_snd

/-- A formal eversion of `𝕊²`, viewed as a homotopy. -/
def locFormalEversionAux : HtpyJetSec E E where
  f (t : ℝ) (x : E) := (1 - 2 * smoothStep t) • x
  φ t x := smoothStep (‖x‖ ^ 2) • locFormalEversionAuxφ ω (smoothStep t) x
  f_diff :=
    ContDiff.smul (contDiff_const.sub <| contDiff_const.mul <| smoothStep.smooth.comp contDiff_fst)
      contDiff_snd
  φ_diff := by
    refine contDiff_iff_contDiffAt.mpr fun x ↦ ?_
    obtain (hx | hx) := eq_or_ne x.2 0
    · refine (contDiffAt_const (c := 0)).congr_of_eventuallyEq ?_
      have : (fun x ↦ ‖x‖ ^ 2) ⁻¹' Iio (1 / 4) ∈ 𝓝 (0 : E) := by
        refine IsOpen.mem_nhds ?_ ?_
        · exact isOpen_Iio.preimage (contDiff_norm_sq ℝ (n :=∞)).continuous
        · simp_rw [mem_preimage, norm_zero, mem_Iio]
          norm_num
      have : (fun x ↦ smoothStep (‖x‖ ^ 2)) ⁻¹' {0} ∈ 𝓝 (0 : E) := by
        refine mem_of_superset this ?_
        erw [preimage_comp (g := smoothStep)]
        refine preimage_mono ?_
        intro x hx
        rw [mem_preimage, mem_singleton_iff, smoothStep.of_lt hx]
      have : (fun p : ℝ × E ↦ smoothStep (‖p.2‖ ^ 2)) ⁻¹' {0} ∈ 𝓝 x := by
        rw [← hx] at this
        exact continuousAt_snd.preimage_mem_nhds this
      filter_upwards [this]
      rintro ⟨t, x⟩ hx
      simp_rw [mem_preimage, mem_singleton_iff] at hx
      change smoothStep (‖x‖ ^ 2) • locFormalEversionAuxφ ω (smoothStep t) x = 0
      simp_rw [hx, zero_smul]
    refine ContDiffAt.smul ?_ ?_
    · exact (smoothStep.smooth.comp <| (contDiff_norm_sq ℝ).comp contDiff_snd).contDiffAt
    · exact (smooth_at_locFormalEversionAuxφ ω
        (show (Prod.map smoothStep id x).2 ≠ 0 from hx)).comp x
        (smoothStep.smooth.prodMap contDiff_id).contDiffAt

/-- A formal eversion of `𝕊²` into its ambient Euclidean space.
The corresponding map `E → E` is roughly a linear homotopy from `id` at `t = 0` to `- id` at
`t = 1`. The continuous linear maps are roughly rotations with angle `t * π`. However, we have to
keep track of a few complications:
* We need the formal solution to be holonomic near `0` and `1`.
  Therefore, we compose the above maps with a smooth step function that is constant `0` near `t = 0`
  and constant `1` near `t = 1`.
* We need to modify the derivative of `ω.rot` to also have the right behavior on `(ℝ ∙ x)`
  at `t = 1` (it is the identity, but it should be `-id`). Therefore, we subtract
  `(2 * t) • (submodule.subtypeL (ℝ ∙ x) ∘L orthogonal_projection (ℝ ∙ x))`,
  which is `2t` times the identity on `(ℝ ∙ x)`.
* We have to make sure the family of continuous linear map is smooth at `x = 0`. Therefore, we
  multiply the family with a factor of `smooth_step (‖x‖ ^ 2)`.
-/
def locFormalEversion : HtpyFormalSol (immersionSphereRel E E) :=
  { locFormalEversionAux ω with
    is_sol := by
      intro t x
      change x ∉ B →
        InjOn (smoothStep (HPow.hPow ‖x‖ 2) • locFormalEversionAuxφ ω (smoothStep t) x) (ℝ ∙ x)ᗮ
      intro hx
      have h2x : smoothStep (HPow.hPow ‖x‖ 2) = 1 := by
        refine smoothStep.of_gt ?_
        rw [mem_ball, not_lt, dist_zero_right] at hx
        refine (show (3 : ℝ) / 4 < (0.9 : ℝ) ^ 2 by norm_num).trans_le ?_
        rwa [sq_le_sq, show |(0.9 : ℝ)| = 0.9 by norm_num, abs_norm]
      rw [h2x, one_smul]
      have h3x : x ≠ 0 := by rintro rfl; apply hx; exact mem_ball_self (by norm_num)
      refine (EqOn.injOn_iff ?_).mpr (ω.injOn_rot_of_ne (smoothStep t) h3x)
      intro v hv
      simp_rw [locFormalEversionAuxφ, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.comp_apply,
        orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero hv, _root_.map_zero,
        smul_zero, sub_zero] }

@[simp]
theorem locFormalEversion_f (t : ℝ) :
    (locFormalEversion ω t).f = fun x : E ↦ ((1 : ℝ) - 2 * smoothStep t) • x :=
  rfl

theorem locFormalEversion_φ (t : ℝ) (x : E) (v : E) :
    (locFormalEversion ω t).φ x v =
      smoothStep (‖x‖ ^ 2) •
        (ω.rot (smoothStep t, x) v - (2 * smoothStep t) • orthogonalProjection (ℝ ∙ x) v) :=
  rfl

theorem locFormalEversion_zero (x : E) : (locFormalEversion ω 0).f x = x := by
  simp


theorem locFormalEversion_one (x : E) : (locFormalEversion ω 1).f x = -x := by
  simp [show (1 : ℝ) - 2 = -1 by norm_num]

theorem locFormalEversionHolAtZero {t : ℝ} (ht : t < 1 / 4) {x : E}
    (hx : smoothStep (‖x‖ ^ 2) = 1) : (locFormalEversion ω t).IsHolonomicAt x := by
  simp_rw [JetSec.IsHolonomicAt, locFormalEversion_f, ContinuousLinearMap.ext_iff,
    locFormalEversion_φ, smoothStep.of_lt ht, hx, ω.rot_zero]
  simp

theorem locFormalEversionHolAtOne {t : ℝ} (ht : 3 / 4 < t) {x : E} (hx : smoothStep (‖x‖ ^ 2) = 1) :
    (locFormalEversion ω t).IsHolonomicAt x := by
  simp_rw [JetSec.IsHolonomicAt, locFormalEversion_f, ContinuousLinearMap.ext_iff,
    locFormalEversion_φ, smoothStep.of_gt ht, hx]
  intro v
  have : (fun x : E ↦ ((1 : ℝ) - 2) • x) = fun x ↦ -x := by ext x; norm_num
  simp [this]
  obtain ⟨v', hv', v, hv, rfl⟩ := Submodule.exists_add_mem_mem_orthogonal (ℝ ∙ x) v
  simp_rw [ContinuousLinearMap.map_add, ω.rot_one _ hv, ω.rot_eq_of_mem_span (1, x) hv']
  rw [fderiv_fun_neg, fderiv_id']
  simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.coe_id', id_eq,
    orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero hv, add_zero,
    orthogonalProjection_eq_self_iff.mpr hv', two_smul, add_sub_add_left_eq_sub]
  abel

theorem locFormalEversion_hol :
    ∀ᶠ p : ℝ × E near {0, 1} ×ˢ 𝕊², (locFormalEversion ω p.1).IsHolonomicAt p.2 := by
  have :
    (Iio (1 / 4 : ℝ) ∪ Ioi (3 / 4)) ×ˢ ((fun x ↦ ‖x‖ ^ 2) ⁻¹' Ioi (3 / 4)) ∈
      𝓝ˢ (({0, 1} : Set ℝ) ×ˢ 𝕊²) := by
    refine (IsOpen.mem_nhdsSet ?_).mpr ?_
    · exact (isOpen_Iio.union isOpen_Ioi).prod
        (isOpen_Ioi.preimage (contDiff_norm_sq ℝ : 𝒞 ∞ _).continuous)
    · rintro ⟨s, x⟩ ⟨hs, hx⟩
      refine ⟨?_, ?_⟩
      simp_rw [mem_insert_iff, mem_singleton_iff] at hs
      rcases hs with (rfl | rfl)
      · exact Or.inl (show (0 : ℝ) < 1 / 4 by norm_num)
      · exact Or.inr (show (3 / 4 : ℝ) < 1 by norm_num)
      simp_rw [mem_sphere_zero_iff_norm] at hx
      simp_rw [mem_preimage, hx, one_pow, mem_Ioi]
      norm_num
  have : (Iio (1 / 4 : ℝ) ∪ Ioi (3 / 4)) ×ˢ ((fun x ↦smoothStep (‖x‖ ^ 2)) ⁻¹' {1}) ∈
      𝓝ˢ (({0, 1} : Set ℝ) ×ˢ 𝕊²) := by
    refine mem_of_superset this (prod_mono Subset.rfl ?_)
    erw [preimage_comp (g := smoothStep)]
    refine preimage_mono ?_
    intro x hx
    rw [mem_preimage, mem_singleton_iff, smoothStep.of_gt hx]
  filter_upwards [this]
  rintro ⟨t, x⟩ ⟨ht | ht, hx⟩
  · exact locFormalEversionHolAtZero ω ht hx
  · exact locFormalEversionHolAtOne ω ht hx

end AssumeFiniteDimensional

open scoped unitInterval

local notation "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

theorem sphere_eversion_of_loc [Fact (dim E = 3)] :
    ∃ f : ℝ → E → E,
      𝒞 ∞ ↿f ∧ (∀ x ∈ 𝕊², f 0 x = x) ∧ (∀ x ∈ 𝕊², f 1 x = -x) ∧ ∀ t ∈ I, SphereImmersion (f t) := by
  classical
  borelize E
  have rankE : (dim E = 3) := Fact.out
  haveI : FiniteDimensional ℝ E := FiniteDimensional.of_finrank_eq_succ rankE
  let ω : Orientation ℝ E (Fin 3) :=
    ((stdOrthonormalBasis _ _).reindex <| finCongr rankE).toBasis.orientation
  have is_closed_pair : IsClosed ({0, 1} : Set ℝ) := (by simp : ({0, 1} : Set ℝ).Finite).isClosed
  obtain ⟨f, h₁, h₂, h₃⟩ :=
    (locFormalEversion ω).exists_sol loc_immersion_rel_open (loc_immersion_rel_ample 2 le_rfl)
      ({0, 1} ×ˢ 𝕊²) (is_closed_pair.prod isClosed_sphere) 𝕊² (isCompact_sphere 0 1)
      (locFormalEversion_hol ω)
  refine ⟨f, h₁, ?_, ?_, ?_⟩
  · intro x hx; rw [h₂ (0, x) (mk_mem_prod (by simp) hx), locFormalEversion_zero]
  · intro x hx; rw [h₂ (1, x) (mk_mem_prod (by simp) hx), locFormalEversion_one]
  · exact fun t ht ↦ sphereImmersion_of_sol _ fun x hx ↦ h₃ x hx t ht

-- Stating the full statement with all type-class arguments and no uncommon notation.
example (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fact (Module.finrank ℝ E = 3)] :
    ∃ f : ℝ → E → E,
      ContDiff ℝ ∞ (uncurry f) ∧
        (∀ x ∈ sphere (0 : E) 1, f 0 x = x) ∧
          (∀ x ∈ sphere (0 : E) 1, f 1 x = -x) ∧ ∀ t ∈ unitInterval, SphereImmersion (f t) :=
  sphere_eversion_of_loc

end SphereEversion
