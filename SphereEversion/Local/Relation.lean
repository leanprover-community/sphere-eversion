import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Topology.MetricSpace.HausdorffDistance
import SphereEversion.Local.OneJet

/-!
# Local partial differential relations and their formal solutions

This file defines `rel_loc E F`, the type of first order partial differential relations
for maps between two real normed spaces `E` and `F`.

To any `R : rel_loc E F` we associate the type `sol R` of maps `f : E → F` of
solutions of `R`, and its formal counterpart `formal_sol R`.

The h-principle question is whether we can deform any formal solution into a solution.
The type of deformations is `htpy_jet_sec E F` (homotopies of 1-jet sections).
-/


noncomputable section

open Set Function Real Filter

open scoped unitInterval Topology

variable (E : Type _) [NormedAddCommGroup E] [NormedSpace ℝ E]

variable (F : Type _) [NormedAddCommGroup F] [NormedSpace ℝ F]

variable (P : Type _) [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- A first order relation for maps between real vector spaces. -/
def RelLoc :=
  Set (OneJet E F)

instance : Membership (E × F × (E →L[ℝ] F)) (RelLoc E F) := by delta RelLoc; infer_instance

variable {E F}

/-- A predicate stating that a 1-jet section is a formal solution to a first order relation for
maps between vector spaces. -/
def JetSec.IsFormalSol (𝓕 : JetSec E F) (R : RelLoc E F) : Prop :=
  ∀ x, (x, 𝓕.f x, 𝓕.φ x) ∈ R

namespace RelLoc

/-- A formal solution to a local relation `R`. -/
@[ext]
structure FormalSol (R : RelLoc E F) extends JetSec E F where
  is_sol : ∀ x, (x, f x, φ x) ∈ R

instance (R : RelLoc E F) : CoeOut (FormalSol R) (JetSec E F) :=
  ⟨FormalSol.toJetSec⟩

@[simp]
theorem FormalSol.toJetSec_eq_coe {R : RelLoc E F} (𝓕 : FormalSol R) :
    𝓕.toJetSec = (𝓕 : JetSec E F) :=
  rfl

@[simp]
theorem FormalSol.coeIsFormalSol {R : RelLoc E F} (𝓕 : FormalSol R) :
    (𝓕 : JetSec E F).IsFormalSol R :=
  𝓕.is_sol

/-- Bundling a formal solution from a 1-jet section that is a formal solution. -/
def _root_.JetSec.IsFormalSol.formalSol {𝓕 : JetSec E F} {R : RelLoc E F} (h : 𝓕.IsFormalSol R) :
    FormalSol R :=
  { 𝓕 with is_sol := h }

instance (R : RelLoc E F) : CoeFun (FormalSol R) fun _ => E → F × (E →L[ℝ] F) :=
  ⟨fun 𝓕 => fun x => (𝓕.f x, 𝓕.φ x)⟩

@[simp]
theorem FormalSol.coe_apply {R : RelLoc E F} (𝓕 : FormalSol R) (x : E) : (𝓕 : JetSec E F) x = 𝓕 x :=
  rfl

variable {R : RelLoc E F}

theorem FormalSol.eq_iff {𝓕 𝓕' : FormalSol R} {x : E} :
    𝓕 x = 𝓕' x ↔ 𝓕.f x = 𝓕'.f x ∧ 𝓕.φ x = 𝓕'.φ x :=
  JetSec.eq_iff

/-- A formal solution (f, φ) is holonomic at `x` if the differential of `f` at `x` is `φ x`. -/
def FormalSol.IsHolonomicAt (𝓕 : FormalSol R) (x : E) : Prop :=
  D 𝓕.f x = 𝓕.φ x

-- TODO: this should come from a lemma about `jet_sec`
theorem FormalSol.isHolonomicAt_congr (𝓕 𝓕' : FormalSol R) {s : Set E}
    (h : ∀ᶠ x near s, 𝓕 x = 𝓕' x) : ∀ᶠ x near s, 𝓕.IsHolonomicAt x ↔ 𝓕'.IsHolonomicAt x :=
  by
  apply h.eventually_nhdsSet.mono
  intro x hx
  have hf : 𝓕.f =ᶠ[𝓝 x] 𝓕'.f := by
    apply hx.mono
    simp_rw [RelLoc.FormalSol.eq_iff]
    tauto
  unfold RelLoc.FormalSol.IsHolonomicAt
  rw [hf.fderiv_eq, (RelLoc.FormalSol.eq_iff.mp hx.self_of_nhds).2]

/-- A family of formal solutions is a 1-parameter family of formal solutions. -/
@[ext]
structure FamilyFormalSol (R : RelLoc E F) extends FamilyJetSec E F P where
  is_sol : ∀ t x, (x, f t x, φ t x) ∈ R

/-- A homotopy of formal solutions is a 1-parameter family of formal solutions. -/
@[reducible]
def HtpyFormalSol (R : RelLoc E F) :=
  R.FamilyFormalSol ℝ

def HtpyFormalSol.toHtpyJetSec {R : RelLoc E F} (𝓕 : R.HtpyFormalSol) : HtpyJetSec E F :=
  𝓕.toFamilyJetSec

open RelLoc

instance (R : RelLoc E F) : CoeFun (FamilyFormalSol P R) fun _ => P → JetSec E F :=
  ⟨fun S t =>
    { f := S.f t
      f_diff := S.f_diff.comp (contDiff_const.prod contDiff_id)
      φ := S.φ t
      φ_diff := S.φ_diff.comp (contDiff_const.prod contDiff_id) }⟩

end RelLoc
