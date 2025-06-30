import SphereEversion.Local.HPrinciple
import SphereEversion.ToMathlib.Topology.Algebra.Module

/-!
In this file we prove the parametric version of the local h-principle.

We will not use this to prove the global version of the h-principle, but we do use this to conclude
the existence of sphere eversion from the local h-principle, which is proven in `Local.HPrinciple`.

The parametric h-principle states the following: Suppose that `R` is a local relation,
`𝓕₀ : P → J¹(E, F)` is a family of formal solutions of `R` that is holonomic near some set
`C ⊆ P × E`, `K ⊆ P × E` is compact and `ε : ℝ`,
then there exists a homotopy `𝓕 : ℝ × P → J¹(E, F)` between `𝓕` and a solution that is holonomic
near `K`, that agrees with `𝓕₀` near `C` and is everywhere `ε`-close to `𝓕₀`
-/


noncomputable section

open Metric FiniteDimensional Set Function RelLoc

open LinearMap (ker)

open scoped Topology Pointwise ContDiff

section ParameterSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  -- `G` will be `ℝ` in the proof of the parametric h-principle.
  -- It indicates the homotopy variable `t`.
  {G : Type*}
  [NormedAddCommGroup G] [NormedSpace ℝ G] {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

variable {R : RelLoc E F}

/-- The projection `J¹(P × E, F) → J¹(E, F)`. -/
def oneJetSnd : OneJet (P × E) F → OneJet E F := fun p ↦
  (p.1.2, p.2.1, p.2.2 ∘L fderiv ℝ (fun y ↦ (p.1.1, y)) p.1.2)

theorem continuous_oneJetSnd : Continuous (oneJetSnd : OneJet (P × E) F → OneJet E F) :=
  continuous_fst.snd.prodMk <|
    continuous_snd.fst.prodMk <|
      continuous_snd.snd.clm_comp <|
        Continuous.fderiv (contDiff_fst.fst.prodMap contDiff_id) continuous_fst.snd le_top

theorem oneJetSnd_eq (p : OneJet (P × E) F) :
    oneJetSnd p = (p.1.2, p.2.1, p.2.2 ∘L ContinuousLinearMap.inr ℝ P E) := by
  simp_rw [oneJetSnd, fderiv_prod_right]

variable (P)

/-- The relation `R.relativize P` (`𝓡 ^ P` in the blueprint) is the relation on `J¹(P × E, F)`
induced by `R`. -/
def RelLoc.relativize (R : RelLoc E F) : RelLoc (P × E) F :=
  oneJetSnd ⁻¹' R

variable {P} (R)

theorem RelLoc.mem_relativize (w : OneJet (P × E) F) :
    w ∈ R.relativize P ↔ (w.1.2, w.2.1, w.2.2 ∘L ContinuousLinearMap.inr ℝ P E) ∈ R := by
  simp_rw [RelLoc.relativize, mem_preimage, oneJetSnd_eq]

theorem RelLoc.isOpen_relativize (R : RelLoc E F) (h2 : IsOpen R) : IsOpen (R.relativize P) :=
  h2.preimage continuous_oneJetSnd

variable {R}

theorem relativize_slice_loc {σ : OneJet (P × E) F} {p : DualPair (P × E)} (q : DualPair E)
    (hpq : p.π.comp (ContinuousLinearMap.inr ℝ P E) = q.π) :
    (R.relativize P).slice p σ = σ.2.2 (p.v - (0, q.v)) +ᵥ R.slice q (oneJetSnd σ) := by
  have h2pq : ∀ x : E, p.π ((0 : P), x) = q.π x := fun x ↦ congr_arg (fun f : E →L[ℝ] ℝ ↦ f x) hpq
  ext1 w
  have h1 :
    (p.update σ.2.2 w).comp (ContinuousLinearMap.inr ℝ P E) =
      q.update (oneJetSnd σ).2.2 (-σ.2.2 (p.v - (0, q.v)) +ᵥ w) := by
    ext1 x
    simp_rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
    rw [← ContinuousLinearMap.map_neg, neg_sub]
    obtain ⟨u, hu, t, rfl⟩ := q.decomp x
    have hv : (0, q.v) - p.v ∈ ker p.π := by
      rw [LinearMap.mem_ker, map_sub, p.pairing, h2pq, q.pairing, sub_self]
    have hup : ((0 : P), u) ∈ ker p.π := (h2pq u).trans hu
    rw [q.update_apply _ hu, ← Prod.zero_mk_add_zero_mk, map_add, p.update_ker_pi _ _ hup, ←
      Prod.smul_zero_mk, map_smul, vadd_eq_add]
    conv_lhs => { rw [← sub_add_cancel (0, q.v) p.v] }
    rw [map_add, p.update_ker_pi _ _ hv, p.update_v, oneJetSnd_eq]
    rfl
  have := preimage_vadd_neg (show F from σ.2.2 (p.v - (0, q.v))) (R.slice q (oneJetSnd σ))
  dsimp only at this
  simp_rw [← this, mem_preimage, mem_slice, R.mem_relativize, h1]
  rfl

theorem relativize_slice_eq_univ_loc {σ : OneJet (P × E) F} {p : DualPair (P × E)}
    (hp : p.π.comp (ContinuousLinearMap.inr ℝ P E) = 0) :
    ((R.relativize P).slice p σ).Nonempty ↔ (R.relativize P).slice p σ = univ := by
  have h2p : ∀ x : E, p.π ((0 : P), x) = 0 := fun x ↦ congr_arg (fun f : E →L[ℝ] ℝ ↦ f x) hp
  have : ∀ y : F,
      (p.update σ.2.2 y).comp (ContinuousLinearMap.inr ℝ P E) =
        σ.2.2.comp (ContinuousLinearMap.inr ℝ P E) := by
    intro y
    ext1 x
    simp_rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
      p.update_ker_pi _ _ (h2p x)]
  simp_rw [Set.Nonempty, eq_univ_iff_forall, mem_slice, R.mem_relativize, this, exists_const,
           forall_const]

variable (P)

theorem RelLoc.IsAmple.relativize (hR : R.IsAmple) : (R.relativize P).IsAmple := by
  intro p σ
  let p2 := p.π.comp (ContinuousLinearMap.inr ℝ P E)
  rcases eq_or_ne p2 0 with (h | h)
  · intro w hw
    rw [(relativize_slice_eq_univ_loc h).mp ⟨w, hw⟩, connectedComponentIn_univ,
      PreconnectedSpace.connectedComponent_eq_univ, convexHull_univ]
  obtain ⟨u', hu'⟩ := ContinuousLinearMap.exists_ne_zero h
  let u := (p2 u')⁻¹ • u'
  let q : DualPair E := ⟨p2, u, by rw [p2.map_smul, smul_eq_mul, inv_mul_cancel₀ hu']⟩
  rw [relativize_slice_loc q rfl]
  exact (hR q _).vadd

variable {P}

/-- Turn a family of sections of `J¹(E, E')` parametrized by `P` into a section of `J¹(P × E, E')`.
-/
@[simps]
def FamilyJetSec.uncurry (S : FamilyJetSec E F P) : JetSec (P × E) F where
  f p := S.f p.1 p.2
  φ p := fderiv ℝ (fun z : P × E ↦ S.f z.1 p.2) p + S.φ p.1 p.2 ∘L fderiv ℝ Prod.snd p
  f_diff := S.f_diff
  φ_diff := by
    refine (ContDiff.fderiv ?_ contDiff_id (m := ∞) le_rfl).add (S.φ_diff.clm_comp ?_)
    · exact S.f_diff.comp (contDiff_snd.fst.prodMk contDiff_fst.snd)
    · exact ContDiff.fderiv contDiff_snd.snd contDiff_id le_top

theorem FamilyJetSec.uncurry_φ' (S : FamilyJetSec E F P) (p : P × E) :
    S.uncurry.φ p =
      fderiv ℝ (fun z ↦ S.f z p.2) p.1 ∘L ContinuousLinearMap.fst ℝ P E +
        S.φ p.1 p.2 ∘L ContinuousLinearMap.snd ℝ P E := by
  simp_rw [S.uncurry_φ, fderiv_snd, add_left_inj]
  refine (fderiv_comp p ((S.f_diff.comp (contDiff_id.prodMk contDiff_const)).differentiable
    (mod_cast le_top) p.1) differentiableAt_fst).trans ?_
  rw [fderiv_fst]
  rfl

open ContinuousLinearMap
theorem FamilyJetSec.uncurry_mem_relativize (S : FamilyJetSec E F P) {s : P} {x : E} :
    ((s, x), S.uncurry (s, x)) ∈ R.relativize P ↔ (x, S s x) ∈ R := by
  rw [RelLoc.relativize, mem_preimage, oneJetSnd_eq, JetSec.coe_apply, JetSec.coe_apply,
    S.uncurry_f, S.uncurry_φ']
  suffices ((D (fun z ↦ f S z x) s).comp (fst ℝ P E) + (φ S s x).comp (snd ℝ P E)).comp
      (ContinuousLinearMap.inr ℝ P E) = JetSec.φ (S s) x by
    rw [this]; rfl
  ext v
  simp_rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', ContinuousLinearMap.map_zero, zero_add]
  rfl

theorem FamilyJetSec.isHolonomicAt_uncurry (S : FamilyJetSec E F P) {p : P × E} :
    S.uncurry.IsHolonomicAt p ↔ (S p.1).IsHolonomicAt p.2 := by
  simp_rw [JetSec.IsHolonomicAt, S.uncurry_φ]
  rw [show S.uncurry.f = fun x ↦ S.uncurry.f x from rfl, funext S.uncurry_f,
    show (fun x : P × E ↦ S.f x.1 x.2) = ↿S.f from rfl]
  rw [fderiv_prod_eq_add (S.f_diff.differentiable (mod_cast le_top) _), fderiv_snd]
  refine (add_right_inj _).trans ?_
  have := fderiv_comp p ((S p.1).f_diff.contDiffAt.differentiableAt (mod_cast le_top))
    differentiableAt_snd
  rw [show D (fun z : P × E ↦ (↿S.f) (p.fst, z.snd)) p = _ from this, fderiv_snd,
    (show Surjective (ContinuousLinearMap.snd ℝ P E) from
          Prod.snd_surjective).clm_comp_injective.eq_iff]
  rfl

/-- Turn a family of formal solutions of `R ⊆ J¹(E, E')` parametrized by `P` into a formal solution
of `R.relativize P`. -/
def RelLoc.FamilyFormalSol.uncurry (S : R.FamilyFormalSol P) : FormalSol (R.relativize P) := by
  refine ⟨S.toFamilyJetSec.uncurry, ?_⟩
  rintro ⟨s, x⟩
  exact S.toFamilyJetSec.uncurry_mem_relativize.mpr (S.is_sol s x)

theorem RelLoc.FamilyFormalSol.uncurry_φ' (S : R.FamilyFormalSol P) (p : P × E) :
    (S.uncurry p).2 =
      fderiv ℝ (fun z ↦ S.f z p.2) p.1 ∘L ContinuousLinearMap.fst ℝ P E +
        S.φ p.1 p.2 ∘L ContinuousLinearMap.snd ℝ P E :=
  S.toFamilyJetSec.uncurry_φ' p

/-- Turn a family of sections of `J¹(P × E, F)` parametrized by `G` into a family of sections of
`J¹(E, F)` parametrized by `G × P`. -/
def FamilyJetSec.curry (S : FamilyJetSec (P × E) F G) : FamilyJetSec E F (G × P) where
  f p x := (S p.1).f (p.2, x)
  φ p x := (S p.1).φ (p.2, x) ∘L fderiv ℝ (fun x ↦ (p.2, x)) x
  f_diff := S.f_diff.comp ((contDiff_prodAssoc : ContDiff ℝ ω (Equiv.prodAssoc G P E)).of_le le_top)
  φ_diff := by
    refine (S.φ_diff.comp
      ((contDiff_prodAssoc : ContDiff ℝ ω (Equiv.prodAssoc G P E)).of_le le_top)).clm_comp ?_
    refine ContDiff.fderiv ?_ contDiff_snd le_top
    exact contDiff_fst.fst.snd.prodMk contDiff_snd

theorem FamilyJetSec.curry_f (S : FamilyJetSec (P × E) F G) (p : G × P) (x : E) :
    (S.curry p).f x = (S p.1).f (p.2, x) :=
  rfl

theorem FamilyJetSec.curry_φ (S : FamilyJetSec (P × E) F G) (p : G × P) (x : E) :
    (S.curry p).φ x = (S p.1).φ (p.2, x) ∘L fderiv ℝ (fun x ↦ (p.2, x)) x :=
  rfl

theorem FamilyJetSec.curry_φ' (S : FamilyJetSec (P × E) F G) (p : G × P) (x : E) :
    (S.curry p).φ x = (S p.1).φ (p.2, x) ∘L ContinuousLinearMap.inr ℝ P E := by
  rw [S.curry_φ]
  congr 1
  refine ((differentiableAt_const _).fderiv_prodMk differentiableAt_id).trans ?_
  rw [fderiv_id, fderiv_fun_const]
  rfl

theorem FamilyJetSec.isHolonomicAt_curry (S : FamilyJetSec (P × E) F G) {t : G} {s : P} {x : E}
    (hS : (S t).IsHolonomicAt (s, x)) : (S.curry (t, s)).IsHolonomicAt x := by
  simp_rw [JetSec.IsHolonomicAt, S.curry_φ] at hS ⊢
  rw [show (S.curry (t, s)).f = fun x ↦ (S.curry (t, s)).f x from rfl, funext (S.curry_f _)]
  refine (fderiv_comp x ((S t).f_diff.contDiffAt.differentiableAt (mod_cast le_top))
    ((differentiableAt_const _).prodMk differentiableAt_id)).trans ?_
  rw [_root_.id, hS]
  rfl

theorem FamilyJetSec.curry_mem (S : FamilyJetSec (P × E) F G) {p : G × P} {x : E}
    (hR : ((p.2, x), S p.1 (p.2, x)) ∈ R.relativize P) : (x, S.curry p x) ∈ R := by
  unfold RelLoc.relativize at hR
  rwa [mem_preimage, JetSec.coe_apply, oneJetSnd_eq, ← S.curry_φ'] at hR

/-- Turn a family of formal solutions of `R.relativize P` parametrized by `G` into a family of
formal solutions of `R` parametrized by `G × P`. -/
def RelLoc.FamilyFormalSol.curry (S : FamilyFormalSol G (R.relativize P)) :
    FamilyFormalSol (G × P) R :=
  ⟨S.toFamilyJetSec.curry, fun _ _ ↦ S.toFamilyJetSec.curry_mem (S.is_sol _ _)⟩

theorem RelLoc.FamilyFormalSol.curry_φ (S : FamilyFormalSol G (R.relativize P)) (p : G × P)
    (x : E) : (S.curry p).φ x = (S p.1).φ (p.2, x) ∘L fderiv ℝ (fun x ↦ (p.2, x)) x :=
  rfl

theorem RelLoc.FamilyFormalSol.curry_φ' (S : FamilyFormalSol G (R.relativize P)) (p : G × P)
    (x : E) : (S.curry p x).2 = (S p.1 (p.2, x)).2 ∘L ContinuousLinearMap.inr ℝ P E :=
  S.toFamilyJetSec.curry_φ' p x

theorem curry_eq_iff_eq_uncurry_loc {𝓕 : FamilyFormalSol G (R.relativize P)}
    {𝓕₀ : R.FamilyFormalSol P} {t : G} {x : E} {s : P} (h : 𝓕 t (s, x) = 𝓕₀.uncurry (s, x)) :
    (𝓕.curry (t, s)) x = 𝓕₀ s x := by
  simp_rw [Prod.ext_iff] at h ⊢
  refine ⟨h.1, ?_⟩
  simp_rw [𝓕.curry_φ', h.2, 𝓕₀.uncurry_φ']
  change ((D (fun (z : P) ↦ 𝓕₀.toFamilyJetSec.f z x) s).comp (fst ℝ P E)
    + (𝓕₀.toFamilyJetSec.φ s x).comp (snd ℝ P E)).comp (inr ℝ P E) = ((𝓕₀ s) x).snd
  ext v
  simp_rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', ContinuousLinearMap.map_zero, zero_add]
  rfl

end ParameterSpace

section ParametricHPrinciple

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {F : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {G : Type*}
  [NormedAddCommGroup G] [NormedSpace ℝ G] {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P]

variable {R : RelLoc E F} (h_op : IsOpen R) (h_ample : R.IsAmple) (L : Landscape E)

include h_op h_ample in
-- The local parametric h-principle.
theorem RelLoc.FamilyFormalSol.improve_htpy {ε : ℝ} (ε_pos : 0 < ε) (C : Set (P × E))
    (hC : IsClosed C) (K : Set (P × E)) (hK : IsCompact K) (𝓕₀ : FamilyFormalSol P R)
    (h_hol : ∀ᶠ p : P × E near C, (𝓕₀ p.1).IsHolonomicAt p.2) :
    ∃ 𝓕 : FamilyFormalSol (ℝ × P) R,
      (∀ s x, 𝓕 (0, s) x = 𝓕₀ s x) ∧
        (∀ᶠ p : P × E near C, ∀ t, 𝓕 (t, p.1) p.2 = 𝓕₀ p.1 p.2) ∧
          (∀ s x t, ‖(𝓕 (t, s)).f x - 𝓕₀.f s x‖ ≤ ε) ∧
            ∀ᶠ p : P × E near K, (𝓕 (1, p.1)).IsHolonomicAt p.2 := by
  let parametric_landscape : Landscape (P × E) :=
    { C
      K₀ := K
      K₁ := (exists_compact_superset hK).choose
      hC
      hK₀ := hK
      hK₁ := (exists_compact_superset hK).choose_spec.1
      h₀₁ := (exists_compact_superset hK).choose_spec.2 }
  obtain ⟨𝓕, h₁, -, h₂, -, h₄, h₅⟩ :=
    𝓕₀.uncurry.improve_htpy' (R.isOpen_relativize h_op) (h_ample.relativize P) parametric_landscape
      ε_pos (h_hol.mono fun p hp ↦ 𝓕₀.isHolonomicAt_uncurry.mpr hp)
  have h₁ : ∀ p, 𝓕 0 p = 𝓕₀.uncurry p := by intro p; rw [h₁.self_of_nhdsSet 0 right_mem_Iic]; rfl
  refine ⟨𝓕.curry, ?_, ?_, ?_, ?_⟩
  · intro s x; exact curry_eq_iff_eq_uncurry_loc (h₁ (s, x))
  · refine h₂.mono ?_; rintro ⟨s, x⟩ hp t; exact curry_eq_iff_eq_uncurry_loc (hp t)
  · intro s x t; exact (h₄ (s, x) t).le
  · refine h₅.mono ?_; rintro ⟨s, x⟩ hp; exact 𝓕.toFamilyJetSec.isHolonomicAt_curry hp

open Filter

open scoped unitInterval

include h_op h_ample in
/-- A corollary of the local parametric h-principle, forgetting the homotopy and `ε`-closeness,
and just stating the existence of a solution that is holonomic near `K`.
Furthermore, we assume that `P = ℝ` and `K` is of the form `compact set × I`.
This is sufficient to prove sphere eversion. -/
theorem RelLoc.HtpyFormalSol.exists_sol (𝓕₀ : R.HtpyFormalSol) (C : Set (ℝ × E)) (hC : IsClosed C)
    (K : Set E) (hK : IsCompact K) (h_hol : ∀ᶠ p : ℝ × E near C, (𝓕₀ p.1).IsHolonomicAt p.2) :
    ∃ f : ℝ → E → F,
      (𝒞 ∞ <| uncurry f) ∧
        (∀ p ∈ C, f (p : ℝ × E).1 p.2 = (𝓕₀ p.1).f p.2) ∧
          ∀ x ∈ K, ∀ t ∈ I, (x, f t x, D (f t) x) ∈ R := by
  obtain ⟨𝓕, _, h₂, -, h₄⟩ :=
    𝓕₀.improve_htpy h_op h_ample zero_lt_one C hC (I ×ˢ K) (isCompact_Icc.prod hK) h_hol
  refine ⟨fun s ↦ (𝓕 (1, s)).f, ?_, ?_, ?_⟩
  · exact 𝓕.f_diff.comp ((contDiff_const.prodMk contDiff_id).prodMap contDiff_id)
  · intro p hp
    exact (Prod.ext_iff.mp ((h₂.forall_mem principal_le_nhdsSet) p hp 1)).1
  · intro x hx t ht
    rw [show D (𝓕 (1, t)).f x = (𝓕 (1, t)).φ x from
        (h₄.forall_mem principal_le_nhdsSet) (t, x) (mk_mem_prod ht hx)]
    exact 𝓕.is_sol (1, t) x

end ParametricHPrinciple
