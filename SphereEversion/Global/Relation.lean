import Mathlib.Geometry.Manifold.Metrizable
import SphereEversion.Local.DualPair
import SphereEversion.Global.OneJetSec
import SphereEversion.Global.SmoothEmbedding
import Mathlib.Analysis.Convex.AmpleSet

/-!
# First order partial differential relations for maps between manifolds

This file contains fundamental definitions about first order partial differential relations
for maps between manifolds and relating them to the local story of first order partial differential
relations for maps between vector spaces.

Given manifolds `M` and `M'` modelled on `I` and `I'`, a first order partial differential relation
for maps from `M` to `M'` is a set in the 1-jet bundle J¹(M, M'), also known as
`OneJetBundle I M I' M'`.
-/


noncomputable section

open Set Function

open Filter hiding map_smul

open ChartedSpace

open scoped Topology Manifold Bundle ContDiff

section Defs

/-! ## Fundamental definitions -/


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] (I' : ModelWithCorners ℝ E' H')
  (M' : Type*) [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] (J : ModelWithCorners ℝ F G)
  (N : Type*) [TopologicalSpace N] [ChartedSpace G N]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
  {G' : Type*} [TopologicalSpace G'] (J' : ModelWithCorners ℝ F' G')
  (N' : Type*) [TopologicalSpace N'] [ChartedSpace G' N'] [IsManifold J' ∞ N']
  {EP : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  {HP : Type*} [TopologicalSpace HP] (IP : ModelWithCorners ℝ EP HP)
  (P : Type*) [TopologicalSpace P] [ChartedSpace HP P]
  {EX : Type*} [NormedAddCommGroup EX] [NormedSpace ℝ EX]
  {HX : Type*} [TopologicalSpace HX] {IX : ModelWithCorners ℝ EX HX}
  -- note: X is a metric space
  {X : Type*} [MetricSpace X] [ChartedSpace HX X] [IsManifold IX ∞ X]

@[inherit_doc] local notation "TM" => TangentSpace I

@[inherit_doc] local notation "TM'" => TangentSpace I'

/-- A first-order differential relation for maps from `M` to `N` is a subset of the 1-jet bundle. -/
@[reducible]
def RelMfld :=
  Set (OneJetBundle I M I' M')

variable {I M I' M'}
variable {R : RelMfld I M I' M'}

@[ext]
structure FormalSol (R : RelMfld I M I' M') extends OneJetSec I M I' M' where
  is_sol' : ∀ x : M, toOneJetSec x ∈ R

set_option backward.isDefEq.respectTransparency false in
instance (R : RelMfld I M I' M') : FunLike (FormalSol R) M (OneJetBundle I M I' M')  where
  coe := fun F ↦ F.toOneJetSec
  coe_injective' := by
    intro F G h
    ext x : 2
    · exact congrArg Prod.snd (congrArg Bundle.TotalSpace.proj (congrFun h x))
    · simpa using (Bundle.TotalSpace.ext_iff.mp (congrFun h x)).2


def mkFormalSol (F : M → OneJetBundle I M I' M') (hsec : ∀ x, (F x).1.1 = x) (hsol : ∀ x, F x ∈ R)
    (hsmooth : ContMDiff I ((I.prod I').prod 𝓘(ℝ, E →L[ℝ] E')) ∞ F) : FormalSol R
    where
  bs m := (F m).1.2
  ϕ m := (F m).2
  contMDiff' := by
    convert hsmooth
    ext
    on_goal 1 => rw [hsec]
    all_goals rfl
  is_sol' m := by
    convert hsol m
    ext
    on_goal 1 => rw [hsec]
    all_goals rfl

@[simp]
theorem mkFormalSol_apply (F : M → OneJetBundle I M I' M') (hsec : ∀ x, (F x).1.1 = x)
    (hsol : ∀ x, F x ∈ R) (hsmooth : ContMDiff I ((I.prod I').prod 𝓘(ℝ, E →L[ℝ] E')) ∞ ↿F) :
    (mkFormalSol F hsec hsol hsmooth : M → OneJetBundle I M I' M') = F := by
  ext x <;> try rfl
  rw [hsec]
  rfl

@[simp]
theorem mkFormalSol_bs_apply (F : M → OneJetBundle I M I' M') (hsec : ∀ x, (F x).1.1 = x)
    (hsol : ∀ x, F x ∈ R) (hsmooth : ContMDiff I ((I.prod I').prod 𝓘(ℝ, E →L[ℝ] E')) ∞ ↿F) (x : M) :
    (mkFormalSol F hsec hsol hsmooth).bs x = (F x).1.2 :=
  rfl

namespace FormalSol

@[simp]
theorem coe_mk {S : OneJetSec I M I' M'} {h : ∀ x, S x ∈ R} {x : M} : FormalSol.mk S h x = S x :=
  rfl

theorem coe_inj_iff {S T : FormalSol R} : S = T ↔ ∀ x, S x = T x := by
  constructor
  · rintro rfl x; rfl
  · intro h; ext x v : 3; · change (S x).1.2 = (T x).1.2; rw [h]
    change (S x).2 v = (T x).2 v; rw [h]

theorem coe_inj {S T : FormalSol R} (h : ∀ x, S x = T x) : S = T :=
  coe_inj_iff.mpr h

@[simp]
theorem toOneJetSec_coe (S : FormalSol R) {x : M} : S.toOneJetSec x = S x :=
  rfl

theorem is_sol (F : FormalSol R) : ∀ x, F x ∈ R :=
  F.is_sol'

theorem coe_apply (F : FormalSol R) (x : M) : F x = ⟨(x, F.bs x), F.ϕ x⟩ :=
  rfl

theorem fst_eq (F : FormalSol R) (x : M) : (F x).1 = (x, F.bs x) :=
  rfl

theorem snd_eq (F : FormalSol R) (x : M) : (F x).2 = F.ϕ x :=
  rfl

theorem is_sec (F : FormalSol R) (x : M) : (F x).1.1 = x :=
  rfl

theorem bs_eq (F : FormalSol R) (x : M) : F.bs x = (F x).1.2 :=
  rfl

end FormalSol

/-! ## Ampleness -/

open scoped Manifold Bundle

/- Porting note: the following four statements are defeq to existing assumption but not found by TC
search. There was no problem in Lean 3. -/

instance (σ : OneJetBundle I M I' M') :
    NormedAddCommGroup (((ContMDiffMap.snd : C^∞⟮I.prod I', M × M'; I', M'⟯) *ᵖ TM') σ.proj) := by
  assumption

instance (σ : OneJetBundle I M I' M') :
    NormedSpace ℝ (((ContMDiffMap.snd : C^∞⟮I.prod I', M × M'; I', M'⟯) *ᵖ TM') σ.proj) := by
  assumption

instance (x : M) (x' : M') :
    NormedAddCommGroup (((ContMDiffMap.snd : C^∞⟮I.prod I', M × M'; I', M'⟯) *ᵖ TM')
    (x, x')) := by
  assumption

instance (x : M) (x' : M') :
    NormedSpace ℝ (((ContMDiffMap.snd : C^∞⟮I.prod I', M × M'; I', M'⟯) *ᵖ TM')
    (x, x')) := by
  assumption

/-- The slice `R(σ,p)`. -/
def RelMfld.slice (R : RelMfld I M I' M') (σ : OneJetBundle I M I' M') (p : DualPair <| TM σ.1.1) :
    Set (TM' σ.1.2) :=
  {w : TM' σ.1.2 | OneJetBundle.mk σ.1.1 σ.1.2 (p.update σ.2 w) ∈ R}

omit [IsManifold I ∞ M] [IsManifold I' ∞ M'] in
/-- For some reason `rw [mem_setOf_eq]` fails after unfolding `slice`,
but rewriting with this lemma works. -/
theorem mem_slice {R : RelMfld I M I' M'} {σ : OneJetBundle I M I' M'} {p : DualPair <| TM σ.1.1}
    {w : TM' σ.1.2} : w ∈ R.slice σ p ↔ OneJetBundle.mk σ.1.1 σ.1.2 (p.update σ.2 w) ∈ R :=
  Iff.rfl

set_option backward.isDefEq.respectTransparency false in
omit [IsManifold I ∞ M] [IsManifold I' ∞ M'] in
theorem slice_mk_update {R : RelMfld I M I' M'} {σ : OneJetBundle I M I' M'}
    {p : DualPair <| TM σ.1.1} (x : E') :
    R.slice (OneJetBundle.mk σ.1.1 σ.1.2 (p.update σ.2 x)) p = (R.slice σ p : Set E') := by
  ext1 w
  rw [mem_slice]
  change _ ↔ OneJetBundle.mk σ.proj.1 σ.proj.2 (DualPair.update p σ.snd w) ∈ R
  convert Iff.rfl using 3
  rw [oneJetBundle_mk_snd, p.update_update]

/-- A differential relation is ample if all its slices are ample sets. -/
def RelMfld.Ample (R : RelMfld I M I' M') : Prop :=
  ∀ ⦃σ : OneJetBundle I M I' M'⦄ (p : DualPair <| TM σ.1.1), AmpleSet (R.slice σ p)

omit [IsManifold I ∞ M] [IsManifold I' ∞ M'] in
theorem RelMfld.ample_iff (R : RelMfld I M I' M') :
    R.Ample ↔
    ∀ ⦃σ : OneJetBundle I M I' M'⦄ (p : DualPair <| TM σ.1.1), σ ∈ R → AmpleSet (R.slice σ p) := by
  simp_rw [RelMfld.Ample]
  refine ⟨fun h σ p _ ↦ h p, fun h σ p x hx ↦ ?_⟩
  have := @h (OneJetBundle.mk σ.1.1 σ.1.2 (p.update σ.2 x)) p hx
  rw [slice_mk_update] at this
  exact this x hx


/-! ## Families of formal solutions. -/

/-- A family of formal solutions indexed by manifold `N` is a function from `N` into formal
  solutions in such a way that the function is smooth as a function of all arguments. -/
@[ext]
structure FamilyFormalSol (R : RelMfld I M I' M') extends FamilyOneJetSec I M I' M' J N where
  is_sol' : ∀ (t : N) (x : M), toFamilyOneJetSec t x ∈ R

instance : FunLike (FamilyFormalSol J N R) N (FormalSol R) where
  coe := fun S n ↦ ⟨S.toFamilyOneJetSec n, S.is_sol' n⟩
  coe_injective' := by
    intro S T
    rcases S with ⟨S, -⟩
    rcases T with ⟨T, -⟩
    intro h
    have fact : ∀ n, S n = T n := fun n ↦ congrArg FormalSol.toOneJetSec (congrFun h n)
    congr! 1
    ext n : 2
    exacts [(OneJetSec.mk.inj <| fact n).1, (OneJetSec.mk.inj <| fact n).2]

namespace FamilyFormalSol

variable {J N J' N'}

@[simp]
theorem coe_mk {S : FamilyOneJetSec I M I' M' J N} {h : ∀ t x, S t x ∈ R} {t : N} {x : M} :
    FamilyFormalSol.mk S h t x = S t x :=
  rfl

theorem coe_mk_toOneJetSec {S : FamilyOneJetSec I M I' M' J N} {h : ∀ t x, S t x ∈ R} {t : N} :
    (FamilyFormalSol.mk S h t).toOneJetSec = S t :=
  rfl

theorem toFamilyOneJetSec_coe (S : FamilyFormalSol J N R) {t : N} {x : M} :
    S.toFamilyOneJetSec t x = S t x :=
  rfl

@[simp]
theorem toFamilyOneJetSec_eq (S : FamilyFormalSol J N R) {t : N} :
    S.toFamilyOneJetSec t = (S t).toOneJetSec :=
  rfl

theorem is_sol (S : FamilyFormalSol J N R) {t : N} {x : M} : S t x ∈ R :=
  S.is_sol' t x

/-- Reindex a family along a smooth function `f`. -/
def reindex (S : FamilyFormalSol J' N' R) (f : C^∞⟮J, N; J', N'⟯) : FamilyFormalSol J N R :=
  ⟨S.toFamilyOneJetSec.reindex f, fun t ↦ S.is_sol' (f t)⟩

end FamilyFormalSol


/-! ## Homotopies of formal solutions. -/

/-- A homotopy of formal solutions is a family indexed by `ℝ` -/
abbrev HtpyFormalSol (R : RelMfld I M I' M') :=
  FamilyFormalSol 𝓘(ℝ, ℝ) ℝ R

def mkHtpyFormalSol (F : ℝ → M → OneJetBundle I M I' M') (hsec : ∀ t x, (F t x).1.1 = x)
    (hsol : ∀ t x, F t x ∈ R)
    (hsmooth : ContMDiff (𝓘(ℝ).prod I) ((I.prod I').prod 𝓘(ℝ, E →L[ℝ] E')) ∞ ↿F) : HtpyFormalSol R
    where
  bs t m := (F t m).1.2
  ϕ t m := (F t m).2
  contMDiff' := by
    convert hsmooth using 1
    ext ⟨t, x⟩
    · exact (hsec t x).symm
    all_goals rfl
  is_sol' t m := by
    convert hsol t m
    ext
    on_goal 1 => rw [hsec]
    all_goals rfl

@[simp]
theorem mkHtpyFormalSol_apply (F : ℝ → M → OneJetBundle I M I' M') (hsec : ∀ t x, (F t x).1.1 = x)
    (hsol : ∀ t x, F t x ∈ R)
    (hsmooth : ContMDiff (𝓘(ℝ).prod I) ((I.prod I').prod 𝓘(ℝ, E →L[ℝ] E')) ∞ ↿F) (t : ℝ) :
    (mkHtpyFormalSol F hsec hsol hsmooth t : M → OneJetBundle I M I' M') = F t := by
  ext x <;> try rfl
  rw [hsec]
  rfl

/-- The constant homotopy of formal solution associated to a formal solution. -/
def FormalSol.constHtpy (F : FormalSol R) : HtpyFormalSol R where
  bs _ := F.bs
  ϕ _ := F.ϕ
  contMDiff' := F.contMDiff.comp contMDiff_snd
  is_sol' _ := F.is_sol

variable (R)

/-- The empty homotopy of formal solution associated to any relation whose source manifold
is empty. This is required to avoid a silly nonemptyness assumption in the main theorems. -/
def emptyHtpyFormalSol [IsEmpty M] : HtpyFormalSol R where
  bs _t x := (IsEmpty.false x).elim
  ϕ _t x := (IsEmpty.false x).elim
  contMDiff' := fun ⟨_t, x⟩ ↦ (IsEmpty.false x).elim
  is_sol' _t x := (IsEmpty.false x).elim


/-! ## The h-principle -/

variable {P}

/-- A relation `R` satisfies the (non-parametric) relative C⁰-dense h-principle w.r.t. a subset
`C` of the domain if for every formal solution `𝓕₀` that is holonomic near `C`
there is a homotopy between `𝓕₀` and a holonomic solution that is constant near `C` and
`ε`-close to `𝓕₀`. This is a temporary version with a slightly weaker conclusion.
The weak version has `∀ x ∈ C, ∀ t : ℝ, 𝓕 t x = 𝓕₀ x` while the strong one has
`∀ᶠ x near C, ∀ t, 𝓕 t x = 𝓕₀ x`. The strong version is easy to derive from the weak one
if we prove the weak one for *all* closed sets, see `RelMfld.satisfiesHPrinciple_of_weak`
below. The reason why the weak one is more convenient for us is we will prove
the h-principle using a sequence of homotopy of formal solutions and we don't
want to keep control of a fixed neighborhood of `C` independant from the sequence index. -/
def RelMfld.SatisfiesHPrincipleWeak (R : RelMfld I M IX X) (C : Set M) (ε : M → ℝ) : Prop :=
  ∀ 𝓕₀ : FormalSol R,
    (∀ᶠ x near C, 𝓕₀.toOneJetSec.IsHolonomicAt x) →
      ∃ 𝓕 : HtpyFormalSol R,
        (∀ x : M, 𝓕 0 x = 𝓕₀ x) ∧
          (𝓕 1).toOneJetSec.IsHolonomic ∧
            (∀ x ∈ C, ∀ t : ℝ, 𝓕 t x = 𝓕₀ x) ∧ ∀ (t : ℝ) (x : M), dist ((𝓕 t).bs x) (𝓕₀.bs x) ≤ ε x

/-- A relation `R` satisfies the (non-parametric) relative C⁰-dense h-principle w.r.t. a subset
`C` of the domain if for every formal solution `𝓕₀` that is holonomic near `C`
there is a homotopy between `𝓕₀` and a holonomic solution that is constant near `C` and
`ε`-close to `𝓕₀`. -/
def RelMfld.SatisfiesHPrinciple (R : RelMfld I M IX X) (C : Set M) (ε : M → ℝ) : Prop :=
  ∀ 𝓕₀ : FormalSol R,
    (∀ᶠ x near C, 𝓕₀.toOneJetSec.IsHolonomicAt x) →
      ∃ 𝓕 : HtpyFormalSol R,
        (∀ x : M, 𝓕 0 x = 𝓕₀ x) ∧
        (𝓕 1).toOneJetSec.IsHolonomic ∧
        (∀ᶠ x near C, ∀ t : ℝ, 𝓕 t x = 𝓕₀ x) ∧
        ∀ (t : ℝ) (x : M), dist ((𝓕 t).bs x) (𝓕₀.bs x) ≤ ε x

theorem RelMfld.satisfiesHPrinciple_of_weak [FiniteDimensional ℝ E] [T2Space M]
    [SigmaCompactSpace M] {R : RelMfld I M IX X} {ε : M → ℝ} {C : Set M} (hC : IsClosed C)
    (h : ∀ A : Set M, IsClosed A → R.SatisfiesHPrincipleWeak A ε) : R.SatisfiesHPrinciple C ε := by
  haveI := Manifold.metrizableSpace I M
  letI : MetricSpace M := TopologicalSpace.metrizableSpaceMetric M
  intro 𝓕₀ h𝓕₀
  obtain ⟨C', hCC', hC', h𝓕₀C'⟩ := h𝓕₀.closed_neighborhood hC
  obtain ⟨𝓕, h1, h2, h3, h4⟩ := h C' hC' 𝓕₀ h𝓕₀C'
  exact ⟨𝓕, h1, h2, eventually_of_mem hCC' h3, h4⟩

/-- A relation `R` satisfies the parametric relative C⁰-dense h-principle w.r.t. manifold `P`,
`C ⊆ P × M` and `ε : M → ℝ` if for every family of
formal solutions `𝓕₀` indexed by a manifold with boundary `P` that is holonomic near `C`,
there is a homotopy `𝓕` between `𝓕₀` and a holonomic solution,
in such a way that `𝓕` is constant near `C` and `ε`-close to `𝓕₀`.
-/
def RelMfld.SatisfiesHPrincipleWith (R : RelMfld I M IX X) (C : Set (P × M)) (ε : M → ℝ) : Prop :=
  ∀ 𝓕₀ : FamilyFormalSol IP P R,
    (-- given a family of formal solutions with parameters in `P`
      ∀ᶠ p : P × M near C, (𝓕₀ p.1).toOneJetSec.IsHolonomicAt p.2) →-- holonomic near `C`
      ∃ 𝓕 : FamilyFormalSol (𝓘(ℝ, ℝ).prod IP) (ℝ × P) R,
        (-- then there is a homotopy of such families
          ∀ (s : P) (x : M), 𝓕 (0, s) x = 𝓕₀ s x) ∧
          (-- that agrees on `t = 0`
            ∀ s : P, (𝓕 (1, s)).toOneJetSec.IsHolonomic) ∧
            (-- is holonomic everywhere for `t = 1`
              ∀ᶠ p : P × M near C, ∀ t : ℝ, 𝓕 (t, p.1) p.2 = 𝓕₀ p.1 p.2) ∧-- and agrees near `C`
              ∀ (t : ℝ) (s : P) (x : M), dist ((𝓕 (t, s)).bs x) ((𝓕₀ s).bs x) ≤ ε x

-- and close to `𝓕₀`.
variable {IP}

/-- If a relation satisfies the parametric relative C⁰-dense h-principle wrt some data
then we can forget the homotopy and get a family of solutions from every
family of formal solutions. -/
theorem RelMfld.SatisfiesHPrincipleWith.bs {R : RelMfld I M IX X} {C : Set (P × M)} {ε : M → ℝ}
    (h : R.SatisfiesHPrincipleWith IP C ε) (𝓕₀ : FamilyFormalSol IP P R)
    (h2 : ∀ᶠ p : P × M near C, (𝓕₀ p.1).toOneJetSec.IsHolonomicAt p.2) :
    ∃ f : P → M → X,
      (ContMDiff (IP.prod I) IX ∞ <| uncurry f) ∧
        (∀ᶠ p : P × M near C, f p.1 p.2 = 𝓕₀.bs p.1 p.2) ∧
          (∀ p m, dist (f p m) ((𝓕₀ p).bs m) ≤ ε m) ∧ ∀ p m, oneJetExt I IX (f p) m ∈ R := by
  rcases h 𝓕₀ h2 with ⟨𝓕, _, h₂, h₃, h₄⟩
  refine ⟨fun s ↦ (𝓕 (1, s)).bs, ?_, ?_, ?_, ?_⟩
  · let j : C^∞⟮IP, P; 𝓘(ℝ, ℝ).prod IP, ℝ × P⟯ :=
      ⟨fun p ↦ (1, p), ContMDiff.prodMk contMDiff_const contMDiff_id⟩
    rw [show
        (uncurry fun s ↦ (𝓕 (1, s)).bs) =
          Prod.snd ∘ π _ (OneJetSpace I IX) ∘ fun p : P × M ↦ 𝓕.reindex j p.1 p.2
          by ext; rfl]
    exact (𝓕.reindex j).toFamilyOneJetSec.contMDiff_bs
  · refine h₃.mono fun x hx ↦ ?_
    simp_rw [OneJetSec.bs_eq, FormalSol.toOneJetSec_coe, hx, FamilyOneJetSec.bs_eq,
      𝓕₀.toFamilyOneJetSec_coe]
  · exact fun p m ↦ h₄ ..
  · intro p m
    suffices oneJetExt I IX (𝓕 (1, p)).bs m = (𝓕.toFamilyOneJetSec (1, p)) m by
      rw [this]
      exact 𝓕.is_sol' (1, p) m
    exact OneJetSec.isHolonomicAt_iff.mp (h₂ p m)

end Defs

section OpenSmoothEmbedding

/-! ## Localisation of one jet sections

In order to use the local story of convex integration, we need a way to turn a
one jet section into local ones, then apply the local story to build a homotopy of one jets section
and transfer back to the original manifolds. There is a dissymetry here: we use
maps from whole vector spaces to open sets in manifold.

The global manifolds are called `M` and `N'`. We don't assume the local ones are vector spaces,
there are manifolds `X` and `Y` that will be vector spaces in the next section.
-/


variable {EX : Type*} [NormedAddCommGroup EX] [NormedSpace ℝ EX]
  {HX : Type*} [TopologicalSpace HX] {IX : ModelWithCorners ℝ EX HX}
  {X : Type*} [TopologicalSpace X] [ChartedSpace HX X] [IsManifold IX ∞ X]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M] [IsManifold IM ∞ M]
  {EY : Type*} [NormedAddCommGroup EY] [NormedSpace ℝ EY]
  {HY : Type*} [TopologicalSpace HY] {IY : ModelWithCorners ℝ EY HY}
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace HY Y] [IsManifold IY ∞ Y]
  {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  {HN : Type*} [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN}
  {N : Type*} [TopologicalSpace N] [ChartedSpace HN N] [IsManifold IN ∞ N]
  (F : OneJetSec IM M IN N)
  (φ : OpenSmoothEmbedding IX X IM M) (ψ : OpenSmoothEmbedding IY Y IN N)
  {R : RelMfld IM M IN N}

@[inherit_doc] local notation "TM" => TangentSpace IM

@[inherit_doc] local notation "TN" => TangentSpace IN

@[inherit_doc] local notation "TX" => TangentSpace IX

@[inherit_doc] local notation "TY" => TangentSpace IY

@[inherit_doc] local notation "J¹XY" => OneJetBundle IX X IY Y

@[inherit_doc] local notation "J¹MN" => OneJetBundle IM M IN N

@[inherit_doc] local notation "IXY" => ModelWithCorners.prod (IX.prod IY) 𝓘(ℝ, EX →L[ℝ] EY)

@[inherit_doc] local notation "IMN" => ModelWithCorners.prod (IM.prod IN) 𝓘(ℝ, EM →L[ℝ] EN)


/-! ## Transfer from J¹(X, Y) to J¹(M, N) and localized relations -/

/-- Transfer map between one jet bundles induced by open smooth embedding into the source and
targets. -/
@[simps! proj_fst proj_snd]
def OpenSmoothEmbedding.transfer : OneJetBundle IX X IY Y → OneJetBundle IM M IN N :=
  OneJetBundle.map IY IN φ ψ fun x ↦ (φ.fderiv x).symm

theorem OpenSmoothEmbedding.smooth_transfer :
    ContMDiff ((IX.prod IY).prod 𝓘(ℝ, EX →L[ℝ] EY)) ((IM.prod IN).prod 𝓘(ℝ, EM →L[ℝ] EN)) ∞
      (φ.transfer ψ) := by
  intro x
  refine ContMDiffAt.oneJetBundle_map (φ.contMDiff_to.contMDiffAt.comp _ contMDiffAt_snd)
     (ψ.contMDiff_to.contMDiffAt.comp _ contMDiffAt_snd) ?_ contMDiffAt_id
  have' :=
    ContMDiffAt.mfderiv (fun _ ↦ φ.invFun) (fun x : OneJetBundle IX X IY Y ↦ φ x.1.1)
      ((φ.contMDiffAt_inv <| _).comp (x, φ x.1.1) contMDiffAt_snd)
      (φ.contMDiff_to.contMDiffAt.comp x (contMDiff_oneJetBundle_proj.fst x)) (mod_cast le_top)
  · simp only [left_inv] at this; exact this
  exact mem_range_self _

theorem OneJetBundle.continuous_transfer : Continuous (φ.transfer ψ) :=
  (OpenSmoothEmbedding.smooth_transfer _ _).continuous

omit [IsManifold IX ∞ X] [IsManifold IM ∞ M]
  [IsManifold IY ∞ Y] [IsManifold IN ∞ N] in
theorem OpenSmoothEmbedding.range_transfer :
    range (φ.transfer ψ) = π _ (OneJetSpace IM IN) ⁻¹' range φ ×ˢ range ψ := by
  ext σ; constructor
  · rintro ⟨σ, rfl⟩; exact mk_mem_prod (mem_range_self _) (mem_range_self _)
  · rcases σ with ⟨⟨x, y⟩, τ⟩
    rintro ⟨⟨x, rfl⟩ : x ∈ range φ, ⟨y, rfl⟩ : y ∈ range ψ⟩
    refine ⟨⟨(x, y), ((ψ.fderiv y).symm : TangentSpace IN (ψ y) →L[ℝ] TangentSpace IY y) ∘L
      τ ∘L (φ.fderiv x : TangentSpace IX x →L[ℝ] TangentSpace IM (φ x))⟩, ?_⟩
    refine congr_arg (Bundle.TotalSpace.mk _) (ContinuousLinearMap.ext fun v ↦ ?_)
    /- Porting note: Lean 3 version was
    simp_rw [continuous_linear_map.comp_apply, ← ψ.fderiv_coe, continuous_linear_equiv.coe_coe,
      (φ.fderiv x).apply_symm_apply, (ψ.fderiv y).apply_symm_apply] -/
    simp only [ContinuousLinearMap.comp_apply, ← ψ.fderiv_coe]
    erw [ContinuousLinearEquiv.coe_coe (fderiv ψ  y), (ψ.fderiv y).apply_symm_apply]
    change τ _ = _
    erw [(φ.fderiv x).apply_symm_apply]
    rfl

omit [IsManifold IX ∞ X] [IsManifold IY ∞ Y] in
theorem OpenSmoothEmbedding.isOpen_range_transfer : IsOpen (range (φ.transfer ψ)) := by
  rw [φ.range_transfer ψ]
  exact (φ.isOpen_range.prod ψ.isOpen_range).preimage oneJetBundle_proj_continuous

/-- localize a relation -/
def RelMfld.localize (R : RelMfld IM M IN N) : RelMfld IX X IY Y :=
  φ.transfer ψ ⁻¹' R


/- Porting note: the following two statements are defeq to existing assumptions but not found by TC
search. There was no problem in Lean 3. -/
instance (y : Y) : NormedAddCommGroup (TY y) := by assumption

instance (y : Y) : NormedSpace ℝ (TY y) := by assumption

set_option backward.isDefEq.respectTransparency false in
omit [IsManifold IX ∞ X] [IsManifold IM ∞ M]
  [IsManifold IY ∞ Y] [IsManifold IN ∞ N] in
/-- Ampleness survives localization -/
theorem RelMfld.Ample.localize (hR : R.Ample) : (R.localize φ ψ).Ample := by
  intro x p
  have :
    (RelMfld.localize φ ψ R).slice x p =
      (ψ.fderiv x.1.2).symm '' R.slice (φ.transfer ψ x) (p.map (φ.fderiv x.1.1)) := by
    ext v
    simp_rw [RelMfld.localize, ContinuousLinearEquiv.image_symm_eq_preimage, mem_preimage,
      mem_slice, mem_preimage]
    -- Porting note: the next `rw` should be part of the `simp_rw` above
    rw [mem_slice]
    dsimp only [OpenSmoothEmbedding.transfer, OneJetBundle.map, oneJetBundle_mk_fst,
      oneJetBundle_mk_snd]
    simp_rw [p.map_update_comp_right, ← p.update_comp_left, OneJetBundle.mk, ← ψ.fderiv_coe]
    rfl
  rw [this]
  exact (hR _).image ((ψ.fderiv x.1.2).symm).toContinuousAffineEquiv

/-! ## Localized 1-jet sections -/

/-- Localize a one-jet section in two open embeddings.
  It maps `x` to `(x, y, (D_y(g))⁻¹ ∘ F_φ(φ x) ∘ D_x(φ))` where `y : M := g⁻¹(F_{bs}(φ x))`. -/
@[simps]
def OneJetSec.localize (hF : range (F.bs ∘ φ) ⊆ range ψ) : OneJetSec IX X IY Y where
  bs x := ψ.invFun (F.bs <| φ x)
  ϕ x :=
    let y := ψ.invFun (F.bs <| φ x)
    (↑(ψ.fderiv y).symm : TN (ψ y) →L[ℝ] TY y) ∘L (F <| φ x).2 ∘L (φ.fderiv x : TX x →L[ℝ] TM (φ x))
  contMDiff' := by
    -- Porting note: next 4 lines were
    -- simp_rw [φ.fderiv_coe, ψ.fderiv_symm_coe,
    --          mfderiv_congr_point (ψ.right_inv (hF <| mem_range_self _))]
    simp_rw [φ.fderiv_coe, ψ.fderiv_symm_coe]
    have : ∀ x, mfderiv% ψ.invFun (ψ (ψ.invFun (bs F (φ x)))) = mfderiv _ _ _ (F.bs (φ x)) :=
      fun x ↦ mfderiv_congr_point (ψ.right_inv (hF <| mem_range_self x))
    simp only [this]
    refine ContMDiff.oneJet_comp IN (fun x' ↦ F.bs (φ x')) ?_ ?_
    · exact fun x ↦ (ψ.contMDiffAt_inv <| hF <| mem_range_self x).oneJetExt.comp _
        (F.contMDiff_bs.comp φ.contMDiff_to).contMDiffAt
    · exact .oneJet_comp IM φ (F.contMDiff_eta.comp φ.contMDiff_to) φ.contMDiff_to.oneJetExt

set_option maxHeartbeats 800000 in -- adaptation note: this is required since the bump
-- from version 4.28.0 to version 4.29.0-rc6
set_option backward.isDefEq.respectTransparency false in
theorem transfer_localize (hF : range (F.bs ∘ φ) ⊆ range ψ) (x : X) :
    φ.transfer ψ (F.localize φ ψ hF x) = F (φ x) := by
  rw [OneJetSec.coe_apply, OneJetSec.localize_bs, OneJetSec.localize_ϕ,
    OpenSmoothEmbedding.transfer, OneJetBundle.map]
  dsimp only [OneJetBundle.mk]
  ext
  · rfl
  · dsimp only; erw [ψ.right_inv (hF <| mem_range_self x), Function.comp_apply, F.bs_eq]
  · -- Porting note: was simp_rw [← ψ.fderiv_coe, continuous_linear_map.comp_apply,
    --  continuous_linear_equiv.coe_coe, continuous_linear_equiv.apply_symm_apply]
    -- Porting note: we are missing an ext lemma here.
    apply ContinuousLinearMap.ext_iff.2 (fun v ↦ ?_)
    rw [← ψ.fderiv_coe]
    rw [ContinuousLinearMap.comp_apply]
    erw [ContinuousLinearEquiv.coe_coe,
      ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.apply_symm_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.apply_symm_apply]
    rfl

theorem OneJetSec.localize_bs_fun (hF : range (F.bs ∘ φ) ⊆ range ψ) :
    (F.localize φ ψ hF).bs = ψ.invFun ∘ F.bs ∘ φ :=
  rfl

theorem OneJetSec.localize_mem_iff (hF : range (F.bs ∘ φ) ⊆ range ψ) {x : X} :
    F.localize φ ψ hF x ∈ R.localize φ ψ ↔ F (φ x) ∈ R := by
  rw [RelMfld.localize, mem_preimage, transfer_localize F φ ψ hF]

set_option backward.isDefEq.respectTransparency false in
theorem isHolonomicAt_localize_iff (hF : range (F.bs ∘ φ) ⊆ range ψ) (x : X) :
    (F.localize φ ψ hF).IsHolonomicAt x ↔ F.IsHolonomicAt (φ x) := by
  have :
    mfderiv% (ψ.invFun ∘ F.bs ∘ φ) x =
      (ψ.fderiv (ψ.invFun (F.bs (φ x)))).symm.toContinuousLinearMap.comp
        ((mfderiv% F.bs (φ x)).comp (φ.fderiv x).toContinuousLinearMap) := by
    have h1 : MDifferentiableAt IN IY ψ.invFun (F.bs (φ x)) :=
      (ψ.contMDiffAt_inv <| hF <| mem_range_self _).mdifferentiableAt (by simp)
    have h2 : MDifferentiableAt IM IN F.bs (φ x) := F.contMDiff_bs.mdifferentiableAt (by simp)
    have h3 : MDifferentiableAt IX IM φ x := φ.contMDiff_to.mdifferentiableAt (by simp)
    rw [mfderiv_comp x h1 (h2.comp x h3), mfderiv_comp x h2 h3, ←
      ψ.fderiv_symm_coe' (hF <| mem_range_self _)]
    rfl
  simp_rw [OneJetSec.IsHolonomicAt]
  rw [mfderiv_congr (F.localize_bs_fun φ ψ hF), OneJetSec.snd_eq, F.localize_ϕ, this]
  simp_rw [ContinuousLinearEquiv.cancel_left, ContinuousLinearEquiv.cancel_right]


/-! ## From embeddings `X ↪ M` and `Y ↪ N` to `J¹(X, Y) ↪ J¹(M, N)` -/

-- very slow to elaborate :-(
set_option backward.isDefEq.respectTransparency false in
@[simps]
def OneJetBundle.embedding : OpenSmoothEmbedding IXY J¹XY IMN J¹MN where
  toFun := φ.transfer ψ
  invFun :=
    OneJetBundle.map IN IY φ.invFun ψ.invFun fun x ↦
      (φ.fderiv <| φ.invFun x : TX (φ.invFun x) →L[ℝ] TM (φ <| φ.invFun x))
  left_inv' {σ} := by
    rw [OpenSmoothEmbedding.transfer, OneJetBundle.map_map]; rotate_left
    · exact (ψ.contMDiffAt_inv'.mdifferentiableAt (by simp))
    · exact ψ.contMDiff_to.contMDiffAt.mdifferentiableAt (by simp)
    conv_rhs => rw [← OneJetBundle.map_id σ]
    congr 1
    · rw [OpenSmoothEmbedding.invFun_comp_coe]
    · rw [OpenSmoothEmbedding.invFun_comp_coe]
    · ext x v; simp_rw [ContinuousLinearMap.comp_apply]
      convert (φ.fderiv x).symm_apply_apply v
      erw [φ.left_inv]; rfl
  isOpen_range := φ.isOpen_range_transfer ψ
  contMDiff_to := φ.smooth_transfer ψ
  contMDiffOn_inv := by
    rintro _ ⟨x, rfl⟩
    refine (ContMDiffAt.oneJetBundle_map ?_ ?_ ?_ contMDiffAt_id).contMDiffWithinAt
    · refine (φ.contMDiffAt_inv ?_).comp (φ.transfer ψ x, (φ.transfer ψ x).proj.1) contMDiffAt_snd
      exact mem_range_self _
    · refine (ψ.contMDiffAt_inv ?_).comp (φ.transfer ψ x, (φ.transfer ψ x).proj.2) contMDiffAt_snd
      exact mem_range_self _
    have' :=
      ContMDiffAt.mfderiv (fun _ ↦ φ) (fun x : OneJetBundle IM M IN N ↦ φ.invFun x.1.1)
        (φ.contMDiff_to.contMDiffAt.comp _ contMDiffAt_snd)
        ((φ.contMDiffAt_inv _).comp _ (contMDiff_oneJetBundle_proj.fst (φ.transfer ψ x)))
        (mod_cast le_top)
    · dsimp only [id]
      refine this.congr_of_eventuallyEq ?_
      refine Filter.eventually_of_mem ((φ.isOpen_range_transfer ψ).mem_nhds (mem_range_self _)) ?_
      rw [φ.range_transfer ψ]
      rintro ⟨⟨x, y⟩, τ⟩ ⟨⟨x, rfl⟩ : x ∈ range φ, ⟨y, rfl⟩ : y ∈ range ψ⟩
      simp_rw [inTangentCoordinates, φ.fderiv_coe, φ.transfer_proj_fst, φ.left_inv]
      congr 1
      rw [φ.left_inv]
    exact mem_range_self _


/-! ## Updating 1-jet sections and formal solutions -/

/-- Local notation for `φ.update (OneJetBundle.embedding φ ψ)` -/
local notation "JΘ" => φ.update (OneJetBundle.embedding φ ψ)

variable {K : Set X}

namespace OpenSmoothEmbedding

theorem Jupdate_aux (F : OneJetSec IM M IN N) (G : OneJetSec IX X IY Y) (m : M) :
    (JΘ F G m).1.1 = m := by
  simp_rw [OpenSmoothEmbedding.update]; split_ifs with h
  · rcases h with ⟨x, rfl⟩
    simp_rw [OneJetBundle.embedding_toFun, φ.transfer_proj_fst, φ.left_inv, G.fst_eq]
  · rfl

variable [T2Space M]

/-- Update a global homotopy of 1-jet-sections `F` using a local one `G`. -/
def Jupdate (F : OneJetSec IM M IN N) (G : HtpyOneJetSec IX X IY Y) (hK : IsCompact K)
    (hFG : ∀ t, ∀ x ∉ K, F (φ x) = (OneJetBundle.embedding φ ψ) (G t x)) :
    HtpyOneJetSec IM M IN N := by
  refine FamilyOneJetSec.mk' (fun t ↦ JΘ F (G t)) (fun t ↦ φ.Jupdate_aux ψ F (G t)) ?_
  refine φ.contMDiff_update _ _ _ (hK.image φ.continuous).isClosed ?_ ?_
      contMDiff_snd fun x ↦ hFG x.1
  · exact F.contMDiff.comp contMDiff_snd
  · exact G.contMDiff.comp (contMDiff_fst.prodMap contMDiff_id)

theorem Jupdate_apply {F : OneJetSec IM M IN N} {G : HtpyOneJetSec IX X IY Y} (hK : IsCompact K)
    (hFG : ∀ t, ∀ x ∉ K, F (φ x) = (OneJetBundle.embedding φ ψ) (G t x)) (t : ℝ) (m : M) :
    φ.Jupdate ψ F G hK hFG t m = JΘ F (G t) m := by
  ext; exacts [(φ.Jupdate_aux ψ F (G t) m).symm, rfl, rfl]

theorem Jupdate_bs (F : OneJetSec IM M IN N) (G : HtpyOneJetSec IX X IY Y) (t : ℝ)
    (hK : IsCompact K)
    (hFG : ∀ t, ∀ x ∉ K, F (φ x) = OneJetBundle.embedding φ ψ (G t x)) :
    (OpenSmoothEmbedding.Jupdate φ ψ F G hK hFG t).bs =
      OpenSmoothEmbedding.update φ ψ F.bs (G t).bs := by
  classical
  ext x
  change
    (if x ∈ range φ then φ.transfer ψ (G t (φ.invFun x)) else F x).1.2 =
      if x ∈ range φ then _ else _
  split_ifs <;> rfl

theorem Jupdate_localize {F : OneJetSec IM M IN N} {G : HtpyOneJetSec IX X IY Y} (hK : IsCompact K)
    (hFG : ∀ t, ∀ x ∉ K, F (φ x) = (OneJetBundle.embedding φ ψ) (G t x)) (t : ℝ)
    (rg : range ((φ.Jupdate ψ F G hK hFG t).bs ∘ φ) ⊆ range ψ) (x : X) :
    (φ.Jupdate ψ F G hK hFG t).localize φ ψ rg x = G t x := by
  have foo : ψ.invFun ((φ.Jupdate ψ F G hK hFG t).bs (φ x)) = (G t).bs x := by
    simp_rw [Jupdate_bs, OpenSmoothEmbedding.update_apply_embedding, OpenSmoothEmbedding.left_inv]
  ext -- This is partially failing compared to Lean 3.
  · rfl
  · exact foo
  · -- Porting note: we are missing an ext lemma here.
    apply ContinuousLinearMap.ext_iff.2 (fun v ↦ ?_)
    rw [OneJetSec.snd_eq, OneJetSec.localize_ϕ, foo]
    change (ψ.fderiv ((G t).bs x)).symm ((JΘ F (G t) (φ x)).2 (φ.fderiv x v)) = ((G t).ϕ x) v
    rw [φ.update_apply_embedding]
    change
      (ψ.fderiv ((G t).bs x)).symm
          (ψ.fderiv ((G t).bs x) <| (G t).ϕ x <| (φ.fderiv x).symm <| φ.fderiv x v) =
        (G t).ϕ x v
    simp_rw [ContinuousLinearEquiv.symm_apply_apply]

/-- Update a global formal solutions `F` using a homotopy of local ones `G`. -/
def updateFormalSol (F : FormalSol R) (G : HtpyFormalSol (R.localize φ ψ)) (hK : IsCompact K)
    (hFG : ∀ t, ∀ x ∉ K, F (φ x) = (OneJetBundle.embedding φ ψ) (G t x)) : HtpyFormalSol R
    where
  toFamilyOneJetSec := φ.Jupdate ψ F.toOneJetSec G.toFamilyOneJetSec hK hFG
  is_sol' t x := by
    simp_rw [Jupdate_apply, OpenSmoothEmbedding.update, OneJetBundle.embedding_toFun]
    split_ifs
    · exact G.is_sol
    · exact F.is_sol x

theorem updateFormalSol_apply {F : FormalSol R} {G : HtpyFormalSol (R.localize φ ψ)}
    (hK : IsCompact K)
    (hFG : ∀ t, ∀ x ∉ K, F (φ x) = (OneJetBundle.embedding φ ψ) (G t x)) (t x) :
    φ.updateFormalSol ψ F G hK hFG t x = ⟨⟨x, (JΘ F (G t) x).1.2⟩, (JΘ F (G t) x).2⟩ :=
  rfl

theorem updateFormalSol_bs' {F : FormalSol R} {G : HtpyFormalSol (R.localize φ ψ)}
    (hK : IsCompact K)
    (hFG : ∀ t, ∀ x ∉ K, F (φ x) = (OneJetBundle.embedding φ ψ) (G t x)) (t) :
    (φ.updateFormalSol ψ F G hK hFG t).bs = fun x ↦ (JΘ F (G t) x).1.2 :=
  rfl

theorem updateFormalSol_bs {F : FormalSol R} {G : HtpyFormalSol (R.localize φ ψ)} (hK : IsCompact K)
    (hFG : ∀ t, ∀ x ∉ K, F (φ x) = (OneJetBundle.embedding φ ψ) (G t x)) (t) :
    (φ.updateFormalSol ψ F G hK hFG t).bs = φ.update ψ F.bs (G t).bs := by
  rw [updateFormalSol_bs']
  ext x
  by_cases hx : x ∈ range φ
  · simp only [hx, update_of_mem_range, OneJetBundle.embedding_toFun, transfer_proj_snd]
    rfl
  · rw [update_of_nmem_range, update_of_nmem_range]
    exacts [rfl, hx, hx]

@[simp]
theorem updateFormalSol_apply_of_mem {F : FormalSol R} {G : HtpyFormalSol (R.localize φ ψ)}
    (hK : IsCompact K)
    (hFG : ∀ t, ∀ x ∉ K, F (φ x) = (OneJetBundle.embedding φ ψ) (G t x)) (t) {m}
    (hx : m ∈ range φ) : φ.updateFormalSol ψ F G hK hFG t m = φ.transfer ψ (G t <| φ.invFun m) := by
  rw [updateFormalSol_apply, φ.update_of_mem_range _ _ _ hx]
  ext
  · change m = φ (φ.invFun m)
    rw [φ.right_inv hx]
  · rfl
  · rfl

theorem updateFormalSol_apply_image {F : FormalSol R} {G : HtpyFormalSol (R.localize φ ψ)}
    (hK : IsCompact K)
    (hFG : ∀ t, ∀ x ∉ K, F (φ x) = (OneJetBundle.embedding φ ψ) (G t x)) (t) {x} :
    φ.updateFormalSol ψ F G hK hFG t (φ x) = φ.transfer ψ (G t x) := by simp

end OpenSmoothEmbedding

end OpenSmoothEmbedding
