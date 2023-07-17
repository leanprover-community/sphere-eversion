import SphereEversion.ToMathlib.Analysis.NormedGroup
import SphereEversion.ToMathlib.LinearAlgebra.Basis
import SphereEversion.ToMathlib.Topology.Algebra.Order.Basic
import SphereEversion.Loops.Exists
import SphereEversion.Local.Corrugation
import SphereEversion.Local.AmpleRelation
import SphereEversion.InteractiveExpr

/- ./././Mathport/Syntax/Translate/Basic.lean:334:40: warning: unsupported option trace.filter_inst_type -/
set_option trace.filter_inst_type true

/-!
# Local h-principle for open and ample relations

This file proves lem:h_principle_open_ample_loc from the blueprint. This is the local
version of the h-principle for open and ample relations. The proof brings together the
main result `exist_loops` from the loop folder (Chapter 1 in the blueprint) and
the corrugation technique.

One formalization issue is that the whole construction carries around a lot of data.
On paper it is easy to state one lemma listing once all this data and proving many properties.
Here it is more convenient to give each property its own lemma so carrying around data,
assumptions and constructions requires some planning. Our way to mitigate this issue
is to use two ad-hoc structures `landscape` and `step_landscape` which partly bundle
all this.

The `landscape` structure record three sets in a vector space, a closed
set `C` and two nested compact sets `K₀` and `K₁`. This is the ambiant data for
the local h-principle result. We call this partly bundled because it doesn't include
the data of the formal solution we want to improve. Instead we have a Prop-valued
structure `landscape.accepts` that takes a landscape and a formal solution and assert
some compatibility conditions. There are four conditions, which is already enough
motivation to introduce a structure instead of one definition using the logical
conjunction operator that would lead to awkward and error prone access to the
individual conditions.

The proof of this proposition involves an induction on a flag of subspaces (nested
subspaces of increasing dimensions). For the purpose of this induction we use
a second structure `step_landscape` that extends `landscape` with two more pieces
of data, a subspace and a dual pair, and a compatibility condition, namely the subspace
has to be in the hyperplane defined by the dual pair.

In this setup, given `(L : step_landscape E) {𝓕 : formal_sol R} (h : L.accepts R 𝓕)`,
the loop family constructed by Chapter 2 is `L.loop h`. Together with corrugation,
it is used to build `L.improve_step h` which is the homotopy of 1-jet sections improving
the formal solution `𝓕` in that step of the main inductive proof. A rather long series of
lemmas prove all the required properties of that homotopy, corresponding to
lemma lem:integration_step from the blueprint.

The inductive proof itself is the proof of `rel_loc.formal_sol.improve`.
Here all conclusions are stated at once this the induction requires to know about each
of them to proceed to the next step. We could have introduced one more ad-hoc structure
to record those conclusion but this isn't needed (at least in that Chapter) since we
need to access its components only once.

-/


noncomputable section

open scoped unitInterval Classical Filter Topology

open Filter Set RelLoc

open LinearMap (ker)

variable (E : Type _) [NormedAddCommGroup E] [NormedSpace ℝ E] {F : Type _} [NormedAddCommGroup F]
  [NormedSpace ℝ F] {G : Type _} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The setup for local h-principle is two compact subsets `K₀ ⊆ K₁` in `E` with
`K₀ ⊆ interior K₁` and a closed subset `C`.
-/
structure Landscape where
  (C k₀ k₁ : Set E)
  hC : IsClosed C
  hK₀ : IsCompact K₀
  hK₁ : IsCompact K₁
  h₀₁ : K₀ ⊆ interior K₁

section ImproveStep

/-!
## Improvement step

This section proves lem:integration_step.
-/


/-- The setup for a one-step improvement towards a local h-principle is two compact subsets
`K₀ ⊆ K₁` in `E` with `K₀ ⊆ interior K₁` and a closed subset `C`
together with a dual pair `p` and a subspace `E'` of the corresponding hyperplane `ker p.π`.
-/
structure StepLandscape extends Landscape E where
  e' : Submodule ℝ E
  p : DualPair E
  hEp : E' ≤ ker p.π

variable {E}

open scoped Classical

variable (R : RelLoc E F)

namespace StepLandscape

/-- A one-step improvement landscape accepts a formal solution if it can improve it. -/
structure Accepts (L : StepLandscape E) (𝓕 : JetSec E F) : Prop where
  h_op : IsOpen R
  hK₀ : ∀ᶠ x near L.k₀, 𝓕.IsPartHolonomicAt L.e' x
  hShort : ∀ x, 𝓕.IsShortAt R L.p x
  hC : ∀ᶠ x near L.C, 𝓕.IsHolonomicAt x

/-- The union of all slices of `R` corresponding to `𝓕`. -/
def Ω (L : StepLandscape E) (𝓕 : JetSec E F) : Set (E × F) :=
  {p | p.2 ∈ 𝓕.sliceAt R L.p p.1}

--⋃ x, ({x} : set E) ×ˢ (connected_component_in (𝓕.slice_at R L.p x) $ 𝓕.φ x L.p.v)
/-- The linear form in a `step_landscape`, coming from the underlying dual pair. -/
def π (L : StepLandscape E) : E →L[ℝ] ℝ :=
  L.p.π

/-- The vector in a `step_landscape`, coming from the underlying dual pair. -/
def v (L : StepLandscape E) : E :=
  L.p.V

/-- One more compact set in the landscape: K₁ ∩ C, needed as an input to the
loop construction. -/
def k (L : StepLandscape E) : Set E :=
  L.k₁ ∩ L.C

/-- The base function for the loop family associated in any jet section in a
step landscape. -/
def b (L : StepLandscape E) (𝓕 : JetSec E F) : E → F := fun x => 𝓕.φ x L.V

/-- The desired average for the loop family associated in any jet section in a
step landscape. -/
def g (L : StepLandscape E) (𝓕 : JetSec E F) : E → F := fun x => D 𝓕.f x L.V

theorem isCompact_k (L : StepLandscape E) : IsCompact L.k :=
  L.hK₁.inter_right L.hC

variable {R}

theorem Accepts.open [FiniteDimensional ℝ E] {L : StepLandscape E} {𝓕 : JetSec E F}
    (h : L.Accepts R 𝓕) : IsOpen (L.Ω R 𝓕) :=
  by
  set ψ : E × F → OneJet E F := fun p => (p.1, 𝓕.f p.1, L.p.update (𝓕.φ p.1) p.2)
  change IsOpen {p : E × F | ψ p ∈ R}
  apply IsOpen.preimage _ h.h_op
  apply continuous_fst.prod_mk (𝓕.f_diff.continuous.fst'.prod_mk _)
  exact L.p.continuous_update 𝓕.φ_diff.continuous.fst' continuous_snd

theorem smooth_b (L : StepLandscape E) (𝓕 : JetSec E F) : 𝒞 ∞ (L.b 𝓕) :=
  (ContinuousLinearMap.apply ℝ F L.V).ContDiff.comp 𝓕.φ_diff

theorem smooth_g (L : StepLandscape E) (𝓕 : JetSec E F) : 𝒞 ∞ (L.g 𝓕) :=
  (ContinuousLinearMap.apply ℝ F L.V).ContDiff.comp (contDiff_top_iff_fderiv.mp 𝓕.f_diff).2

theorem Accepts.rel {L : StepLandscape E} {𝓕 : JetSec E F} (h : L.Accepts R 𝓕) :
    ∀ᶠ x : E near L.k, (L.g 𝓕) x = (L.b 𝓕) x :=
  by
  apply (h.hC.filter_mono <| monotone_nhdsSet (inter_subset_right L.K₁ L.C)).mono
  intro x hx
  dsimp [JetSec.IsHolonomicAt] at hx 
  dsimp [StepLandscape.g, StepLandscape.b]
  rw [hx]

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

open scoped Borelize

/-- The loop family to use in some landscape to improve a formal solution. -/
def loop (L : StepLandscape E) {𝓕 : FormalSol R} (h : L.Accepts R 𝓕) : ℝ → E → Loop F :=
  Classical.choose (exist_loops L.isCompact_k h.open (L.smooth_g 𝓕) (L.smooth_b 𝓕) h.Rel h.hShort)

theorem nice (L : StepLandscape E) {𝓕 : FormalSol R} (h : L.Accepts R 𝓕) :
    NiceLoop (L.g ↑𝓕) (L.b ↑𝓕) (Ω R L 𝓕) L.k (L.Loop h) :=
  Classical.choose_spec <|
    exist_loops L.isCompact_k h.open (L.smooth_g 𝓕) (L.smooth_b 𝓕) h.Rel h.hShort

theorem update_zero (L : StepLandscape E) {𝓕 : FormalSol R} (h : L.Accepts R 𝓕) (x : E) (s : ℝ) :
    L.p.update (𝓕.φ x) ((L.Loop h 0 x) s) = 𝓕.φ x :=
  by
  rw [(L.nice h).t_zero x s]
  exact L.p.update_self _

theorem loop_smooth (L : StepLandscape E) {𝓕 : FormalSol R} (h : L.Accepts R 𝓕) : 𝒞 ∞ ↿(L.Loop h) :=
  (L.nice h).smooth

theorem loop_smooth' (L : StepLandscape E) {𝓕 : FormalSol R} (h : L.Accepts R 𝓕) {t : G → ℝ}
    (ht : 𝒞 ∞ t) {s : G → ℝ} (hs : 𝒞 ∞ s) {x : G → E} (hx : 𝒞 ∞ x) :
    𝒞 ∞ fun g => L.Loop h (t g) (x g) (s g) :=
  (L.loop_smooth h).comp (ht.Prod <| hx.Prod hs)

theorem loop_C1 (L : StepLandscape E) {𝓕 : FormalSol R} (h : L.Accepts R 𝓕) :
    ∀ t, 𝒞 1 ↿(L.Loop h t) := fun t =>
  (L.loop_smooth' h contDiff_const contDiff_snd contDiff_fst).of_le le_top

variable (L : StepLandscape E)

/-- The cut-off function associated to a step landscape, equal to one near K₀ and
zero outside K₁. -/
def ρ (L : StepLandscape E) : E → ℝ :=
  (exists_contDiff_one_nhds_of_interior L.hK₀.IsClosed L.h₀₁).some

theorem ρ_smooth (L : StepLandscape E) : 𝒞 ∞ L.ρ :=
  (exists_contDiff_one_nhds_of_interior L.hK₀.IsClosed L.h₀₁).choose_spec.1

theorem ρ_mem (L : StepLandscape E) (x : E) : L.ρ x ∈ I :=
  (exists_contDiff_one_nhds_of_interior L.hK₀.IsClosed L.h₀₁).choose_spec.2.2.2 x

theorem ρ_le (L : StepLandscape E) (x : E) : |L.ρ x| ≤ 1 :=
  by
  cases' L.ρ_mem x with h h'
  rw [abs_le]
  refine' ⟨_, h'⟩
  linarith

theorem hρ₀ (L : StepLandscape E) : ∀ᶠ x near L.k₀, L.ρ x = 1 :=
  (exists_contDiff_one_nhds_of_interior L.hK₀.IsClosed L.h₀₁).choose_spec.2.1

theorem hρ_compl_k₁ (L : StepLandscape E) {x : E} : x ∉ L.k₁ → L.ρ x = 0 :=
  (exists_contDiff_one_nhds_of_interior L.hK₀.IsClosed L.h₀₁).choose_spec.2.2.1 x

/-- Homotopy of formal solutions obtained by corrugation in the direction of `p : dual_pair E`
in some landscape to improve a formal solution `𝓕` from being `L.E'`-holonomic to
`L.E' ⊔ span {p.v}`-holonomic near `L.K₀`.
-/
def improveStep {𝓕 : FormalSol R} (h : L.Accepts R 𝓕) (N : ℝ) : HtpyJetSec E F
    where
  f t x := 𝓕.f x + (smoothStep t * L.ρ x) • corrugation L.π N (L.Loop h t) x
  f_diff :=
    𝓕.f_diff.snd'.add <|
      (smoothStep.smooth.fst'.mul L.ρ_smooth.snd').smul <|
        corrugation.cont_diff' N (L.loop_smooth h) contDiff_snd contDiff_fst
  φ t x :=
    L.p.update (𝓕.φ x) (L.Loop h (smoothStep t * L.ρ x) x <| N * L.π x) +
      (smoothStep t * L.ρ x) • corrugation.remainder L.p.π N (L.Loop h 1) x
  φ_diff := by
    apply ContDiff.add
    apply L.p.smooth_update
    apply 𝓕.φ_diff.snd'
    apply L.loop_smooth'
    exact smooth_step.smooth.fst'.mul L.ρ_smooth.snd'
    apply cont_diff_const.mul L.π.cont_diff.snd'
    exact contDiff_snd
    apply ContDiff.smul
    exact smooth_step.smooth.fst'.mul L.ρ_smooth.snd'
    exact Remainder.smooth _ _ (L.loop_smooth h) contDiff_snd contDiff_const

variable {L} {𝓕 : FormalSol R} (h : L.Accepts R 𝓕) (N : ℝ)

@[simp]
theorem improveStep_apply (t : ℝ) (x : E) :
    L.improveStep h N t x =
      (𝓕.f x + (smoothStep t * L.ρ x) • corrugation L.π N (L.Loop h t) x,
        L.p.update (𝓕.φ x) (L.Loop h (smoothStep t * L.ρ x) x <| N * L.π x) +
          (smoothStep t * L.ρ x) • corrugation.remainder L.p.π N (L.Loop h 1) x) :=
  by simp [improve_step, h]; rfl

@[simp]
theorem improveStep_apply_f (t : ℝ) (x : E) :
    (L.improveStep h N t).f x = 𝓕.f x + (smoothStep t * L.ρ x) • corrugation L.π N (L.Loop h t) x :=
  rfl

@[simp]
theorem improveStep_apply_φ (t : ℝ) (x : E) :
    (L.improveStep h N t).φ x =
      L.p.update (𝓕.φ x) (L.Loop h (smoothStep t * L.ρ x) x <| N * L.π x) +
        (smoothStep t * L.ρ x) • corrugation.remainder L.p.π N (L.Loop h 1) x :=
  rfl

theorem improveStep_of_support (t : ℝ) {x : E} (H : ∀ t, x ∉ Loop.support (L.Loop h t)) :
    L.improveStep h N t x = 𝓕 x :=
  by
  have : ∀ t s, L.loop h t x s = 𝓕.φ x L.v := by
    intro t s
    rw [Loop.isConst_of_not_mem_support (H t) s 0]
    apply (L.nice h).s_zero x t
  rw [improve_step_apply h, corrugation_eq_zero _ _ _ _ (H t),
    remainder_eq_zero _ _ (L.loop_C1 h 1) (H 1)]
  simp only [formal_sol.to_jet_sec_eq_coe, smul_zero, add_zero, this]
  erw [L.p.update_self]
  rfl

theorem improveStep_rel_t_eq_0 : L.improveStep h N 0 = 𝓕 :=
  by
  ext x
  · rw [improve_step_apply_f h]
    simp [(L.nice h).t_zero x]
  · ext x
    rw [improve_step_apply_φ h]
    simp only [formal_sol.to_jet_sec_eq_coe, MulZeroClass.zero_mul, smoothStep.zero, zero_smul,
      add_zero]
    erw [L.update_zero h]; rfl

theorem improveStep_rel_compl_k₁ {x} (hx : x ∉ L.k₁) (t) : L.improveStep h N t x = 𝓕 x :=
  by
  rw [improve_step_apply h, L.hρ_compl_K₁ hx]
  simp only [formal_sol.to_jet_sec_eq_coe, MulZeroClass.mul_zero, zero_smul, add_zero]
  erw [L.update_zero h]
  rfl

theorem improveStep_rel_k : ∀ᶠ x near L.k, ∀ t, L.improveStep h N t x = 𝓕 x :=
  by
  have : ∀ᶠ x near L.K, ∀ t, x ∉ Loop.support (L.loop h t) :=
    by
    apply (L.nice h).rel_K.eventually_nhdsSet.mono
    intro x hx t
    apply Loop.not_mem_support
    apply hx.mono
    intro y hy
    exact Loop.isConst_of_eq (hy t)
  apply this.mono
  intro x hx t
  exact improve_step_of_support _ _ _ hx

theorem improveStep_rel_c : ∀ᶠ x near L.C, ∀ t, L.improveStep h N t x = 𝓕 x :=
  by
  apply eventually.filter_mono (L.hK₁.is_closed.nhds_set_le_sup' L.C)
  rw [eventually_sup]
  constructor
  · apply improve_step_rel_K
  · rw [eventually_principal]
    exact fun x => improve_step_rel_compl_K₁ h N

-- In the next lemma we reintroduce F to appaise the unused argument linter since
-- `finite_dimensional ℝ F` isn't needed here.
theorem bu_lt {F : Type _} [NormedAddCommGroup F] [NormedSpace ℝ F] (t : ℝ) (x : E) {v : F} {ε : ℝ}
    (hv : ‖v‖ < ε) : ‖(smoothStep t * L.ρ x) • v‖ < ε :=
  calc
    ‖(smoothStep t * L.ρ x) • v‖ = |smoothStep t| * |L.ρ x| * ‖v‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_mul]
    _ ≤ ‖v‖ :=
      (mul_le_of_le_one_left (norm_nonneg _)
        (mul_le_one (smoothStep.abs_le t) (abs_nonneg _) (L.ρ_le x)))
    _ < ε := hv

theorem improveStep_c0_close {ε : ℝ} (ε_pos : 0 < ε) :
    ∀ᶠ N in atTop, ∀ x t, ‖(L.improveStep h N t).f x - 𝓕.f x‖ ≤ ε :=
  by
  set γ := L.loop h
  have γ_cont : Continuous ↿fun t x => γ t x := (L.nice h).smooth.continuous
  have γ_C1 : 𝒞 1 ↿(γ 1) := ((L.nice h).smooth.comp (contDiff_prod_mk_right 1)).of_le le_top
  apply
    ((corrugation.c0_small_on L.hK₁ (L.nice h).t_le_zero (L.nice h).t_ge_one γ_cont ε_pos).And <|
        remainder_c0_small_on L.π L.hK₁ γ_C1 ε_pos).mono
  rintro N ⟨H, H'⟩ x t
  by_cases hx : x ∈ L.K₁
  · rw [improve_step_apply_f h]
    suffices ‖(smoothStep t * L.ρ x) • corrugation L.π N (L.loop h t) x‖ ≤ ε by simpa
    exact (bu_lt _ _ <| H _ hx t).le
  · rw [show (L.improve_step h N t).f x = 𝓕.f x from
        congr_arg Prod.fst (improve_step_rel_compl_K₁ h N hx t)]
    simp [ε_pos.le]

theorem improveStep_part_hol {N : ℝ} (hN : N ≠ 0) :
    ∀ᶠ x near L.k₀, (L.improveStep h N 1).IsPartHolonomicAt (L.e' ⊔ L.p.spanV) x :=
  by
  have γ_C1 : 𝒞 1 ↿(L.loop h 1) := ((L.nice h).smooth.comp (contDiff_prod_mk_right 1)).of_le le_top
  let 𝓕' : JetSec E F :=
    { f := fun x => 𝓕.f x + corrugation L.π N (L.loop h 1) x
      f_diff := 𝓕.f_diff.add (corrugation.cont_diff' _ (L.loop_smooth h) contDiff_id contDiff_const)
      φ := fun x =>
        L.p.update (𝓕.φ x) (L.loop h 1 x <| N * L.π x) +
          corrugation.remainder L.p.π N (L.loop h 1) x
      φ_diff := by
        apply ContDiff.add
        apply L.p.smooth_update
        apply 𝓕.φ_diff
        apply L.loop_smooth'
        apply contDiff_const
        apply cont_diff_const.mul L.π.cont_diff
        exact contDiff_id
        exact Remainder.smooth _ _ (L.loop_smooth h) contDiff_id contDiff_const }
  have H : ∀ᶠ x near L.K₀, L.improve_step h N 1 x = 𝓕' x :=
    by
    apply L.hρ₀.mono
    intro x hx
    simp [improve_step_apply h, hx]
    rfl
  have fderiv_𝓕' := fun x =>
    fderiv_corrugated_map N hN γ_C1 (𝓕.f_diff.of_le le_top) L.p ((L.nice h).avg x)
  rw [eventually_congr (H.is_part_holonomic_at_congr (L.E' ⊔ L.p.span_v))]
  apply h.hK₀.mono
  intro x hx
  apply JetSec.IsPartHolonomicAt.sup
  · intro u hu
    have hu_ker := L.hEp hu
    dsimp [𝓕']
    erw [fderiv_𝓕', ContinuousLinearMap.add_apply, L.p.update_ker_pi _ _ hu_ker,
      L.p.update_ker_pi _ _ hu_ker, hx u hu]
  · intro u hu
    rcases submodule.mem_span_singleton.mp hu with ⟨l, rfl⟩
    rw [(D 𝓕'.f x).map_smul, (𝓕'.φ x).map_smul]
    apply congr_arg
    dsimp [𝓕']
    erw [fderiv_𝓕', L.p.update_v, ContinuousLinearMap.add_apply, L.p.update_v]
    rfl

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem improveStep_formalSol : ∀ᶠ N in atTop, ∀ t, (L.improveStep h N t).IsFormalSol R :=
  by
  set γ := L.loop h
  have γ_cont : Continuous ↿fun t x => γ t x := (L.nice h).smooth.continuous
  have γ_C1 : 𝒞 1 ↿(γ 1) := ((L.nice h).smooth.comp (contDiff_prod_mk_right 1)).of_le le_top
  set K :=
    (fun p : E × ℝ × ℝ => (p.1, 𝓕.f p.1, L.p.update (𝓕.φ p.1) (L.loop h p.2.1 p.1 p.2.2))) ''
      L.K₁ ×ˢ I ×ˢ I
  have K_cpt : IsCompact K :=
    by
    refine' (L.hK₁.prod (is_compact_Icc.prod is_compact_Icc)).image _
    refine' continuous_fst.prod_mk (𝓕.f_diff.continuous.fst'.prod_mk _)
    apply L.p.continuous_update 𝓕.φ_diff.continuous.fst'
    change Continuous (↿(L.loop h) ∘ fun g : E × ℝ × ℝ => (g.snd.fst, g.fst, g.snd.snd))
    exact (L.loop_smooth h).continuous.comp₃ continuous_snd.fst continuous_fst continuous_snd.snd
  have K_sub : K ⊆ R := by
    rintro _ ⟨⟨x, t, s⟩, ⟨x_in, t_in, s_in⟩, rfl⟩
    exact (L.nice h).mem_Ω x t s
  obtain ⟨ε, ε_pos, hε⟩ : ∃ ε, 0 < ε ∧ Metric.thickening ε K ⊆ R
  exact K_cpt.exists_thickening_subset_open h.h_op K_sub
  apply
    ((corrugation.c0_small_on L.hK₁ (L.nice h).t_le_zero (L.nice h).t_ge_one γ_cont ε_pos).And <|
        remainder_c0_small_on L.π L.hK₁ γ_C1 ε_pos).mono
  rintro N ⟨H, H'⟩ t x
  by_cases hxK₁ : x ∈ L.K₁
  · apply hε
    rw [Metric.mem_thickening_iff]
    refine' ⟨(x, 𝓕.f x, L.p.update (𝓕.φ x) <| L.loop h (smoothStep t * L.ρ x) x <| N * L.π x), _, _⟩
    · simp only [hxK₁, formal_sol.to_jet_sec_eq_coe, exists_prop, mem_set_of_eq, eq_self_iff_true,
        true_and_iff, K]
      exact
        ⟨⟨x, smoothStep t * L.ρ x, Int.fract (N * L.π x)⟩,
          ⟨hxK₁, unitInterval.mul_mem (smoothStep.mem t) (L.ρ_mem x), unitInterval.fract_mem _⟩, by
          simp only [Loop.fract_eq]⟩
    · simp only [h, improve_step_apply_f, formal_sol.to_jet_sec_eq_coe, improve_step_apply_φ]
      rw [Prod.dist_eq, max_lt_iff, Prod.dist_eq, max_lt_iff]
      refine' ⟨by simpa using ε_pos, _, _⟩ <;> dsimp only <;> rw [dist_self_add_left]
      · exact bu_lt _ _ <| H _ hxK₁ _
      · exact bu_lt _ _ <| H' _ hxK₁
  · rw [show ((L.improve_step h N) t).f x = 𝓕.f x from
        congr_arg Prod.fst <| improve_step_rel_compl_K₁ h N hxK₁ t,
      show ((L.improve_step h N) t).φ x = 𝓕.φ x from
        congr_arg Prod.snd <| improve_step_rel_compl_K₁ h N hxK₁ t]
    exact 𝓕.is_sol _

end StepLandscape

end ImproveStep

section Improve

/-!
## Full improvement

This section proves lem:h_principle_open_ample_loc.
-/


open FiniteDimensional Submodule StepLandscape

variable {E} [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] {R : RelLoc E F} (h_op : IsOpen R)
  (h_ample : R.IsAmple)

variable (L : Landscape E)

variable {ε : ℝ} (ε_pos : 0 < ε)

/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (x «expr ∉ » L.K₁) -/
/--
Homotopy of formal solutions obtained by successive corrugations in some landscape `L` to improve a
formal solution `𝓕` until it becomes holonomic near `L.K₀`.
-/
theorem RelLoc.FormalSol.improve (𝓕 : FormalSol R) (h_hol : ∀ᶠ x near L.C, 𝓕.IsHolonomicAt x) :
    ∃ H : HtpyJetSec E F,
      (∀ᶠ t near Iic 0, H t = 𝓕) ∧
        (∀ᶠ t near Ici 1, H t = H 1) ∧
          (∀ᶠ x near L.C, ∀ t, H t x = 𝓕 x) ∧
            (∀ x, x ∉ L.k₁ → ∀ t, H t x = 𝓕 x) ∧
              (∀ x t, ‖(H t).f x - 𝓕.f x‖ ≤ ε) ∧
                (∀ t, (H t).IsFormalSol R) ∧ ∀ᶠ x near L.k₀, (H 1).IsHolonomicAt x :=
  by
  let n := finrank ℝ E
  let e := fin_basis ℝ E
  let E' := e.flag
  suffices
    ∀ k : Fin (n + 1),
      ∀ δ > (0 : ℝ),
        ∃ H : HtpyJetSec E F,
          (∀ᶠ t near Iic 0, H t = 𝓕) ∧
            (∀ᶠ t near Ici 1, H t = H 1) ∧
              (∀ᶠ x near L.C, ∀ t, H t x = 𝓕 x) ∧
                (∀ x, x ∉ L.K₁ → ∀ t, H t x = 𝓕 x) ∧
                  (∀ x t, ‖(H t).f x - 𝓕.f x‖ ≤ δ) ∧
                    (∀ t, (H t).IsFormalSol R) ∧ ∀ᶠ x near L.K₀, (H 1).IsPartHolonomicAt (E' k) x
    by
    simpa only [show E' (Fin.last n) = ⊤ from e.flag_last, JetSec.is_part_holonomic_top] using
      this (Fin.last n) ε ε_pos
  clear ε_pos ε
  intro k
  apply Fin.inductionOn k <;> clear k
  · intro δ δ_pos
    use 𝓕.to_jet_sec.const_htpy
    simp [show E' 0 = ⊥ from e.flag_zero, le_of_lt δ_pos]
  · rintro k HH δ δ_pos
    rcases HH (δ / 2) (half_pos δ_pos) with ⟨H, hH₀, hH₁, hHC, hHK₁, hHc0, hH_sol, hH_hol⟩; clear HH
    let S : StepLandscape E :=
      { L with
        e' := E' k
        p := e.dual_pair k
        hEp := by simpa only [E', Basis.dualPair] using e.flag_le_ker_dual k }
    set H₁ : formal_sol R := (hH_sol 1).FormalSol
    have h_span : S.E' ⊔ S.p.span_v = E' k.succ := e.flag_span_succ k
    have acc : S.accepts R H₁ :=
      { h_op
        hK₀ := by
          apply hH_hol.mono
          intro x hx
          dsimp [S]
          convert hx
          rw [← Fin.coe_eq_castSucc, coe_coe]
        hShort := fun x => h_ample.is_short_at H₁ S.p x
        hC := by
          apply h_hol.congr (formal_sol.is_holonomic_at_congr _ _ _)
          apply hHC.mono
          tauto }
    have hH₁_rel_C : ∀ᶠ x : E near S.C, H₁ x = 𝓕 x :=
      by
      apply hHC.mono
      intro x hx
      apply hx
    have hH₁_C : ∀ᶠ x : E near S.to_landscape.C, H₁.is_holonomic_at x :=
      by
      apply h_hol.congr (formal_sol.is_holonomic_at_congr _ _ _)
      exact (h_hol.and hH₁_rel_C).mono fun x hx => hx.2.symm
    have hH₁_K₁ : ∀ (x) (_ : x ∉ L.K₁), H₁ x = 𝓕 x :=
      by
      intro x hx
      apply hHK₁ x hx
    obtain ⟨N, ⟨hN_close, hN_sol⟩, hNneq⟩ :=
      (((improve_step_c0_close Acc <| half_pos δ_pos).And (improve_step_formal_sol Acc)).And <|
          eventually_ne_at_top (0 : ℝ)).exists
    have glue : H 1 = S.improve_step Acc N 0 :=
      by
      rw [improve_step_rel_t_eq_0]
      rfl
    refine' ⟨H.comp (S.improve_step Acc N) glue, _, _, _, _, _, _, _⟩
    · apply (H.comp_le_0 _ _).mono
      intro t ht
      rw [ht]
      exact hH₀.on_set 0 right_mem_Iic
    -- t = 0
    · apply (H.comp_ge_1 _ _).mono
      intro t ht
      rw [ht, H.comp_1]
    · -- rel C
      apply (hHC.and <| hH₁_rel_C.and <| improve_step_rel_C Acc N).mono
      rintro x ⟨hx, hx', hx''⟩ t
      by_cases ht : t ≤ 1 / 2
      · simp only [ht, hx, HtpyJetSec.comp_of_le]
      · simp only [ht, hx', hx'', HtpyJetSec.comp_of_not_le, not_false_iff]
    · -- rel K₁
      intro x hx t
      by_cases ht : t ≤ 1 / 2
      · simp only [ht, hx, hHK₁, HtpyJetSec.comp_of_le, not_false_iff]
      ·
        simp only [ht, hx, hH₁_K₁, improve_step_rel_compl_K₁, HtpyJetSec.comp_of_not_le,
          not_false_iff]
    · -- C⁰-close
      intro x t
      by_cases ht : t ≤ 1 / 2
      · apply le_trans _ (half_le_self <| le_of_lt δ_pos)
        simp only [ht, hHc0, HtpyJetSec.comp_of_le]
      · simp only [ht, HtpyJetSec.comp_of_not_le, not_false_iff]
        rw [← add_halves δ]
        exact norm_sub_le_add_of_le (hN_close _ _) (hHc0 _ _)
    · -- formal solution
      intro t
      by_cases ht : t ≤ 1 / 2
      · simp only [ht, hH_sol, HtpyJetSec.comp_of_le]
      · simp only [ht, hN_sol, HtpyJetSec.comp_of_not_le, not_false_iff]
    · -- part-hol E' (k + 1)
      rw [← h_span, HtpyJetSec.comp_1]
      apply improve_step_part_hol Acc hNneq

/-- A repackaging of `rel_loc.formal_sol.improve` for convenience. -/
theorem RelLoc.FormalSol.improve_htpy' (𝓕 : FormalSol R)
    (h_hol : ∀ᶠ x near L.C, 𝓕.IsHolonomicAt x) :
    ∃ H : HtpyFormalSol R,
      (∀ᶠ t near Iic 0, H t = 𝓕) ∧
        (∀ᶠ t near Ici 1, H t = H 1) ∧
          (∀ᶠ x near L.C, ∀ t, H t x = 𝓕 x) ∧
            (∀ x, x ∉ L.k₁ → ∀ t, H t x = 𝓕 x) ∧
              (∀ x t, ‖(H t).f x - 𝓕.f x‖ < ε) ∧ ∀ᶠ x near L.k₀, (H 1).IsHolonomicAt x :=
  by
  rcases 𝓕.improve h_op h_ample L (half_pos ε_pos) h_hol with ⟨H, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩
  exact
    ⟨{ H with is_sol := h₆ }, h₁, h₂, h₃, h₄, fun x t => (h₅ x t).trans_lt (half_lt_self ε_pos), h₇⟩

end Improve

