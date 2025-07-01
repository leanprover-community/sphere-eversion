import SphereEversion.InductiveConstructions
import SphereEversion.Loops.Basic
import SphereEversion.ToMathlib.Analysis.Normed.Module.FiniteDimension
import SphereEversion.ToMathlib.ExistsOfConvex
import SphereEversion.ToMathlib.SmoothBarycentric
import SphereEversion.ToMathlib.Topology.Path
import Mathlib.Analysis.Convex.Caratheodory

/-!
# Surrounding families of loops

In order to carry out the corrugation technique of convex integration, one needs to a family of
loops with various prescribed properties.

This file begins the work of constructing such a family.

The key definitions are:
 * `Surrounded`
 * `SurroundingPts`
 * `SurroundingFamily`

The key results are:
 * `surrounded_iff_mem_interior_convexHull_aff_basis`
 * `surrounded_of_convexHull`
 * `smooth_surrounding`
 * `eventually_surroundingPts_of_tendsto_of_tendsto`
 * `surrounding_loop_of_convexHull`
 * `local_loops`
 * `satisfied_or_refund`
 * `extend_loops`
 * `exists_surrounding_loops`
-/

-- to obtain that normed spaces are locally connected
open Set Function Module Int Prod Path Filter
open scoped Topology unitInterval ContDiff

namespace IsPathConnected

-- we redo `exists_path_through_family` to use `def`s
variable {X : Type*} [TopologicalSpace X] {F : Set X}

/-- An arbitrary path joining `x` and `y` in `F`. -/
noncomputable def somePath (hF : IsPathConnected F) {x y : X} (hx : x ∈ F) (hy : y ∈ F) :
    Path x y :=
  (hF.joinedIn x hx y hy).somePath

theorem somePath_mem (hF : IsPathConnected F) {x y : X} (hx : x ∈ F) (hy : y ∈ F) (t : I) :
    hF.somePath hx hy t ∈ F :=
  JoinedIn.somePath_mem _ t

theorem range_somePath_subset (hF : IsPathConnected F) {x y : X} (hx : x ∈ F) (hy : y ∈ F) :
    range (hF.somePath hx hy) ⊆ F := by rintro _ ⟨t, rfl⟩; apply somePath_mem

open Fin.NatCast in -- TODO: fix this
/-- A path through `p 0`, ..., `p n`. Usually this is used with `n := m`. -/
noncomputable def pathThrough (hF : IsPathConnected F) {m : ℕ} {p : Fin (m + 1) → X}
    (hp : ∀ i, p i ∈ F) : ∀ n : ℕ, Path (p 0) (p n)
  | 0 => Path.refl (p 0)
  | n + 1 => (pathThrough hF hp n).trans <| hF.somePath (hp _) (hp _)

attribute [simp] Path.trans_range

theorem range_pathThrough_subset (hF : IsPathConnected F) {m : ℕ} {p : Fin (m + 1) → X}
    (hp : ∀ i, p i ∈ F) : ∀ {n : ℕ}, range (hF.pathThrough hp n) ⊆ F
  | 0 => by simp [pathThrough, hp]
  | n + 1 => by simpa [pathThrough, hp, range_somePath_subset]
    using range_pathThrough_subset hF hp (n := n)

open Fin.NatCast in -- TODO: fix this
theorem mem_range_pathThrough' (hF : IsPathConnected F) {m : ℕ} {p : Fin (m + 1) → X}
    (hp : ∀ i, p i ∈ F) {i n : ℕ} (h : i ≤ n) : p i ∈ range (hF.pathThrough hp n) := by
  induction' h with n _ ih
  · exact ⟨1, by simp⟩
  · simp only [pathThrough, Path.trans_range, mem_union, ih, true_or]

theorem mem_range_pathThrough (hF : IsPathConnected F) {m : ℕ} {p : Fin (m + 1) → X}
    (hp : ∀ i, p i ∈ F) {i : Fin (m + 1)} : p i ∈ range (hF.pathThrough hp m) := by
  convert hF.mem_range_pathThrough' hp (Nat.le_of_lt_succ i.2); simp [Fin.cast_val_eq_self]

end IsPathConnected

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace ℝ F]

set_option hygiene false
@[inherit_doc] local notation "d" => finrank ℝ F
set_option hygiene true

/-
The definition below gets a prime because it clashes with a manifold definition
in mathlib which is in the root namespace.
-/
/-- `f` is smooth at `x` if `f` is smooth on some neighborhood of `x`. -/
def SmoothAt' (f : E → F) (x : E) : Prop :=
  ∃ s ∈ 𝓝 x, smooth_on f s

section SurroundingPoints

set_option hygiene false
@[inherit_doc] local notation "ι" => Fin (d + 1)
set_option hygiene true

-- def:surrounds_points
/-- `p` is a collection of points surrounding `f` with weights `w` (that are positive and sum to 1)
if the weighted average of the points `p` is `f` and the points `p` form an affine basis of the
space. -/
structure SurroundingPts (f : F) (p : ι → F) (w : ι → ℝ) : Prop where
  indep : AffineIndependent ℝ p
  w_pos : ∀ i, 0 < w i
  w_sum : ∑ i, w i = 1
  avg : ∑ i, w i • p i = f

theorem SurroundingPts.tot [FiniteDimensional ℝ F] {f : F} {p : ι → F} {w : ι → ℝ}
    (h : SurroundingPts f p w) : affineSpan ℝ (range p) = ⊤ :=
  h.indep.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (Fintype.card_fin _)

theorem SurroundingPts.mem_affineBases [FiniteDimensional ℝ F] {f : F} {p : ι → F} {w : ι → ℝ}
    (h : SurroundingPts f p w) : p ∈ affineBases ι ℝ F :=
  ⟨h.indep, h.tot⟩

theorem SurroundingPts.coord_eq_w [FiniteDimensional ℝ F] {f : F} {p : ι → F} {w : ι → ℝ}
    (h : SurroundingPts f p w) : (⟨p, h.indep, h.tot⟩ : AffineBasis ι ℝ F).coords f = w := by
  let b : AffineBasis ι ℝ F := ⟨p, h.indep, h.tot⟩
  change b.coords f = w
  ext i
  rw [← h.avg, ← Finset.univ.affineCombination_eq_linear_combination _ w h.w_sum,
    AffineBasis.coords_apply]
  exact AffineBasis.coord_apply_combination_of_mem _ (Finset.mem_univ i) h.w_sum

/-- `f` is surrounded by a set `s` if there is an affine basis `p` in `s` with weighted average `f`.
-/
def Surrounded (f : F) (s : Set F) : Prop :=
  ∃ p w, SurroundingPts f p w ∧ ∀ i, p i ∈ s

theorem surrounded_iff_mem_interior_convexHull_aff_basis [FiniteDimensional ℝ F] {f : F}
    {s : Set F} :
    Surrounded f s ↔
      ∃ b, b ⊆ s ∧ AffineIndependent ℝ ((↑) : b → F) ∧ affineSpan ℝ b = ⊤ ∧
        f ∈ interior (convexHull ℝ b) := by
  constructor
  · rintro ⟨p, w, ⟨⟨indep, w_pos, w_sum, rfl⟩, h_mem⟩⟩
    have h_tot : affineSpan ℝ (range p) = ⊤ :=
      indep.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (Fintype.card_fin _)
    refine ⟨range p, range_subset_iff.mpr h_mem, indep.range, h_tot, ?_⟩
    let basis : AffineBasis ι ℝ F := ⟨p, indep, h_tot⟩
    erw [basis.interior_convexHull]
    intro i
    erw [← Finset.affineCombination_eq_linear_combination _ _ _ w_sum,
      basis.coord_apply_combination_of_mem (Finset.mem_univ i) w_sum]
    exact w_pos i
  · rintro ⟨b, h₀, h₁, h₂, h₃⟩
    haveI : Fintype b := (finite_set_of_fin_dim_affineIndependent ℝ h₁).fintype
    have hb : Fintype.card b = d + 1 := by
      rw [← h₁.affineSpan_eq_top_iff_card_eq_finrank_add_one, Subtype.range_coe_subtype,
        setOf_mem_eq, h₂]
    let p := ((↑) : _ → F) ∘ (Fintype.equivFinOfCardEq hb).symm
    have hp : b = range p := by
      ext x
      exact ⟨by intro h; use Fintype.equivFinOfCardEq hb ⟨x, h⟩; simp [p], by
        rintro ⟨y, rfl⟩; apply Subtype.coe_prop⟩
    rw [hp] at h₀ h₂ h₃
    replace h₁ : AffineIndependent ℝ p :=
      h₁.comp_embedding (Fintype.equivFinOfCardEq hb).symm.toEmbedding
    let basis : AffineBasis ι ℝ F := ⟨_, h₁, h₂⟩
    erw [basis.interior_convexHull, mem_setOf_eq] at h₃
    refine ⟨p, fun i ↦ basis.coord i f, ⟨h₁, h₃, ?_, ?_⟩, fun i ↦ h₀ (mem_range_self i)⟩
    · exact basis.sum_coord_apply_eq_one f
    · erw [← Finset.univ.affineCombination_eq_linear_combination p _
        (basis.sum_coord_apply_eq_one f), basis.affineCombination_coord_eq_self]

--- `prop:surrounded_by_open`
theorem surrounded_of_convexHull [FiniteDimensional ℝ F] {f : F} {s : Set F} (hs : IsOpen s)
    (hsf : f ∈ convexHull ℝ s) : Surrounded f s := by
  rw [surrounded_iff_mem_interior_convexHull_aff_basis]
  obtain ⟨t, hts, hai, hf⟩ :
    ∃ t : Finset F,
      (t : Set F) ⊆ s ∧ AffineIndependent ℝ ((↑) : t → F) ∧ f ∈ convexHull ℝ (t : Set F) := by
    simp_rw [← exists_prop, ← mem_iUnion, ← convexHull_eq_union]
    exact hsf
  have htne : (t : Set F).Nonempty := convexHull_nonempty_iff.mp ⟨f, hf⟩
  obtain ⟨b, hb₁, hb₂, hb₃, hb₄⟩ := hs.exists_between_affineIndependent_span_eq_top hts htne hai
  have hb₀ : b.Finite := finite_set_of_fin_dim_affineIndependent ℝ hb₃
  obtain ⟨c, hc⟩ := interior_convexHull_nonempty_iff_affineSpan_eq_top.mpr hb₄
  rw [← hs.interior_eq] at hb₂
  obtain ⟨ε, hε, hcs⟩ :=
    (eventually_homothety_image_subset_of_finite_subset_interior ℝ c hb₀ hb₂).exists_gt
  have hbε := Convex.subset_interior_image_homothety_of_one_lt (convex_convexHull ℝ _) hc ε hε
  rw [AffineMap.image_convexHull] at hbε
  let t : Units ℝ := Units.mk0 ε (by linarith)
  refine ⟨AffineMap.homothety c (t : ℝ) '' b, hcs, ?_, ?_, hbε (convexHull_mono hb₁ hf)⟩
  · rwa [(AffineEquiv.homothetyUnitsMulHom c t).affineIndependent_set_of_eq_iff]
  · exact (AffineEquiv.homothetyUnitsMulHom c t).span_eq_top_iff.mp hb₄

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
-- `lem:smooth_barycentric_coord`
theorem smooth_surrounding [FiniteDimensional ℝ F] {x : F} {p : ι → F} {w : ι → ℝ}
    (h : SurroundingPts x p w) :
    ∃ W : F → (ι → F) → ι → ℝ, ∀ᶠ yq : F × (ι → F) in 𝓝 (x, p),
      SmoothAt' (uncurry W) yq ∧ (∀ i, 0 < W yq.1 yq.2 i) ∧ ∑ i, W yq.1 yq.2 i = 1 ∧
        ∑ i, W yq.1 yq.2 i • yq.2 i = yq.1 := by
  classical
  use evalBarycentricCoords ι ℝ F
  let V : Set (ι → ℝ) := Set.pi Set.univ fun _ ↦ Ioi (0 : ℝ)
  let W' : F × (ι → F) → ι → ℝ := uncurry (evalBarycentricCoords ι ℝ F)
  let A : Set (F × (ι → F)) := univ ×ˢ affineBases ι ℝ F
  let U : Set (F × (ι → F)) := A ∩ W' ⁻¹' V
  have hι : Fintype.card ι = d + 1 := Fintype.card_fin _
  have hp : p ∈ affineBases ι ℝ F := h.mem_affineBases
  have hV : IsOpen V := isOpen_set_pi finite_univ fun _ _ ↦ isOpen_Ioi
  have hW' : ContinuousOn W' A := (smooth_barycentric ι ℝ F hι (n := 0)).continuousOn
  have hxp : W' (x, p) ∈ V := by simp [W', V, hp, h.coord_eq_w, h.w_pos]
  have hA : IsOpen A := by
    simp only [A, affineBases_findim ι ℝ F hι]
    exact isOpen_univ.prod (isOpen_affineIndependent ℝ F)
  have hU₂ : IsOpen U := hW'.isOpen_inter_preimage hA hV
  have hU₃ : U ∈ 𝓝 (x, p) :=
    mem_nhds_iff.mpr ⟨U, le_refl U, hU₂, Set.mem_inter (by simp [hp, A]) (mem_preimage.mpr hxp)⟩
  apply eventually_of_mem hU₃
  rintro ⟨y, q⟩ hyq
  have hq : q ∈ affineBases ι ℝ F := by simpa [A] using inter_subset_left hyq
  have hyq' : (y, q) ∈ W' ⁻¹' V := inter_subset_right hyq
  refine ⟨⟨U, mem_nhds_iff.mpr ⟨U, le_refl U, hU₂, hyq⟩,
    ((smooth_barycentric ι ℝ F hι).mono inter_subset_left).of_le le_top⟩, ?_, ?_, ?_⟩
  · simpa [V] using hyq'
  · simp [hq]
  · simp [hq]; exact AffineBasis.linear_combination_coord_eq_self _ y

theorem smooth_surroundingPts [FiniteDimensional ℝ F] {x : F} {p : ι → F} {w : ι → ℝ}
    (h : SurroundingPts x p w) :
    ∃ W : F → (ι → F) → ι → ℝ,
      ∀ᶠ yq : F × (ι → F) in 𝓝 (x, p),
        SmoothAt' (uncurry W) yq ∧ SurroundingPts yq.1 yq.2 (W yq.1 yq.2) := by
  refine Exists.imp (fun W hW ↦ ?_) (smooth_surrounding h)
  rw [nhds_prod_eq] at hW ⊢
  have := (IsOpen.eventually_mem (isOpen_affineIndependent ℝ F) h.indep).prod_inr (𝓝 x)
  filter_upwards [hW, this]; rintro ⟨y, q⟩ ⟨hW, h2W, h3W, hq⟩ h2q
  exact ⟨hW, h2q, h2W, h3W, hq⟩

theorem surroundingPts_evalBarycentricCoords_iff (q : F) (v : ι → F)
    [DecidablePred (· ∈ affineBases ι ℝ F)] :
    SurroundingPts q v (evalBarycentricCoords ι ℝ F q v) ↔
      ∀ i, 0 < evalBarycentricCoords ι ℝ F q v i := by
  refine ⟨fun h ↦ h.w_pos, fun h ↦ ?_⟩
  have hv : v ∈ affineBases ι ℝ F := by
    by_contra contra
    simpa [evalBarycentricCoords_apply_of_not_mem_bases ι ℝ F q contra] using h 0
  have hv' : ∑ i, evalBarycentricCoords ι ℝ F q v i = 1 := by
    simp [evalBarycentricCoords_apply_of_mem_bases ι ℝ F q hv]
  refine ⟨hv.1, h, hv', ?_⟩
  simp_rw [← Finset.univ.affineCombination_eq_linear_combination v _ hv',
    evalBarycentricCoords_apply_of_mem_bases ι ℝ F q hv]
  convert AffineBasis.affineCombination_coord_eq_self _ q
  rfl

end SurroundingPoints

section SurroundingPointsLimits

variable {X Y : Type*} [FiniteDimensional ℝ F]

local macro:arg "ι" : term => `(Fin (finrank ℝ F + 1))

theorem eventually_surroundingPts_of_tendsto_of_tendsto {l : Filter X} {m : Filter Y} {v : ι → F}
    {q : F} {p : ι → X → F} {f : Y → F} (hq : ∃ w, SurroundingPts q v w)
    (hp : ∀ i, Tendsto (p i) l (𝓝 (v i))) (hf : Tendsto f m (𝓝 q)) :
    ∀ᶠ z : X × Y in l ×ˢ m, ∃ w, SurroundingPts (f z.2) (fun i ↦ p i z.1) w := by
  classical
  obtain ⟨w, hw⟩ := hq
  let V : Set (ι → ℝ) := Set.pi Set.univ fun _ ↦ Ioi (0 : ℝ)
  let W' : F × (ι → F) → ι → ℝ := uncurry (evalBarycentricCoords ι ℝ F)
  let A : Set (F × (ι → F)) := (univ : Set F) ×ˢ affineBases ι ℝ F
  let S : Set (F × (ι → F)) := W' ⁻¹' V
  have hι : Fintype.card ι = finrank ℝ F + 1 := Fintype.card_fin _
  have hq' : v ∈ affineBases ι ℝ F := hw.mem_affineBases
  have hqv : (q, v) ∈ A := by simp [A, hq']
  have hxp : W' (q, v) ∈ V := by simp [W', V, hq', hw.coord_eq_w, hw.w_pos]
  have hV' : V ∈ 𝓝 (W' (q, v)) := (isOpen_set_pi finite_univ fun _ _ ↦ isOpen_Ioi).mem_nhds hxp
  have hA : IsOpen A := by
    simp only [A, affineBases_findim ι ℝ F hι]
    exact isOpen_univ.prod (isOpen_affineIndependent ℝ F)
  have hW' : ContinuousAt W' (q, v) :=
    (smooth_barycentric ι ℝ F hι (n := 0)).continuousOn.continuousAt
      (mem_nhds_iff.mpr ⟨A, Subset.rfl, hA, hqv⟩)
  have hS : S ∈ 𝓝 (q, v) := hW'.preimage_mem_nhds hV'
  obtain ⟨n₁, hn₁, n₂, hn₂, hS'⟩ := mem_nhds_prod_iff.mp hS
  have hn₁' := tendsto_def.mp hf _ hn₁
  have hn₂' := tendsto_def.mp (tendsto_pi_nhds.mpr hp) _ hn₂
  have come_on : (swap p ⁻¹' n₂) ×ˢ (f ⁻¹' n₁) ∈ l  ×ˢ m :=
    mem_prod_iff.mpr ⟨_, hn₂', _, hn₁', Subset.rfl⟩
  filter_upwards [come_on]
  rintro ⟨y₂, y₁⟩ ⟨hy₂ : swap p y₂ ∈ n₂, hy₁ : f y₁ ∈ n₁⟩
  refine ⟨W' (f y₁, swap p y₂),
    (surroundingPts_evalBarycentricCoords_iff (f y₁) (swap p y₂)).mpr fun i ↦ ?_⟩
  change W' (f y₁, swap p y₂) i ∈ Ioi (0 : ℝ)
  suffices (f y₁, swap p y₂) ∈ S from this i (mem_univ _)
  apply hS'
  simp [hy₁, hy₂]

theorem eventually_surroundingPts_of_tendsto_of_tendsto' {v : ι → F} {q : F} {p : ι → X → F}
    {l : Filter X} {f : X → F} (hq : ∃ w, SurroundingPts q v w)
    (hp : ∀ i, Tendsto (p i) l (𝓝 (v i))) (hf : Tendsto f l (𝓝 q)) :
    ∀ᶠ y in l, ∃ w, SurroundingPts (f y) (fun i ↦ p i y) w := by
  have := eventually_surroundingPts_of_tendsto_of_tendsto hq hp hf
  simp_rw [eventually_iff_exists_mem, mem_prod_iff] at this
  obtain ⟨nnn, ⟨n₁, hn₁, n₂, hn₂, hh⟩, h⟩ := this
  rw [eventually_iff_exists_mem]
  exact ⟨n₁ ∩ n₂, inter_mem hn₁ hn₂, fun y hy ↦ h (y, y) (by apply hh; simpa using hy)⟩

end SurroundingPointsLimits

namespace Loop

variable {γ γ' : Loop F} {x y : F} {t : ℝ}

/-- A loop `γ` surrounds a point `x` if `x` is surrounded by values of `γ`. -/
def Surrounds (γ : Loop F) (x : F) : Prop :=
  ∃ t w : Fin (d + 1) → ℝ, SurroundingPts x (γ ∘ t) w

theorem surrounds_iff_range_subset_range :
    γ.Surrounds x ↔
      ∃ (p : Fin (d + 1) → F) (w : Fin (d + 1) → ℝ), SurroundingPts x p w ∧ range p ⊆ range γ := by
  constructor
  · exact fun ⟨t, w, h⟩ ↦ ⟨γ ∘ t, w, h, range_comp_subset_range _ _⟩
  · rintro ⟨p, w, h₀, h₁⟩
    rw [range_subset_iff] at h₁
    choose t ht using h₁
    have hpt : γ ∘ t = p := funext ht
    exact ⟨t, w, hpt.symm ▸ h₀⟩

theorem affineEquiv_surrounds_iff (e : F ≃ᵃ[ℝ] F) :
    γ.Surrounds x ↔ (γ.transform e).Surrounds (e x) := by
  suffices ∀ (γ : Loop F) (x) (e : F ≃ᵃ[ℝ] F), γ.Surrounds x → (γ.transform e).Surrounds (e x) by
    refine ⟨this γ x e, fun h ↦ ?_⟩
    specialize this (γ.transform e) (e x) e.symm h
    rw [AffineEquiv.symm_apply_apply] at this
    convert this
    ext
    simp
  rintro γ x e ⟨t, w, indep, w_pos, w_sum, rfl⟩
  refine ⟨t, w, ⟨e.affineIndependent_iff.mpr indep, w_pos, w_sum, ?_⟩⟩
  simp only [← Finset.affineCombination_eq_linear_combination _ _ _ w_sum]
  erw [Finset.map_affineCombination _ (γ ∘ t) _ w_sum (e : F →ᵃ[ℝ] F)]
  congr

omit [NormedSpace ℝ F] in
@[simp]
theorem zero_vadd : (0 : F) +ᵥ γ = γ := by
  ext t
  simp

theorem vadd_surrounds : γ.Surrounds x ↔ (y +ᵥ γ).Surrounds (y + x) := by
  rw [add_comm]
  convert affineEquiv_surrounds_iff (AffineEquiv.vaddConst ℝ y) using 2
  ext u
  simp [add_comm y]

theorem Surrounds.vadd (h : γ.Surrounds x) : (y +ᵥ γ).Surrounds (y + x) :=
  vadd_surrounds.mp h

theorem Surrounds.vadd0 (h : γ.Surrounds 0) : (y +ᵥ γ).Surrounds y := by
  convert h.vadd
  rw [add_zero]

theorem Surrounds.smul0 (h : γ.Surrounds 0) (ht : t ≠ 0) : (t • γ).Surrounds 0 := by
  rw [affineEquiv_surrounds_iff (AffineEquiv.homothetyUnitsMulHom (0 : F) (Units.mk0 t ht)⁻¹),
    AffineEquiv.coe_homothetyUnitsMulHom_apply, AffineMap.homothety_apply_same]
  convert h
  ext u
  simp [AffineMap.homothety_apply, smul_smul, inv_mul_cancel₀ ht]

theorem Surrounds.mono (h : γ.Surrounds x) (h2 : range γ ⊆ range γ') : γ'.Surrounds x := by
  revert h; simp_rw [Loop.surrounds_iff_range_subset_range]
  refine Exists.imp fun t ↦ ?_
  refine Exists.imp fun w ↦ ?_
  exact And.imp_right fun h3 ↦ Subset.trans h3 h2

protected theorem Surrounds.reparam (h : γ.Surrounds x) {φ : EquivariantMap} (hφ : Continuous φ) :
    (γ.reparam φ).Surrounds x := by
  refine h.mono ?_
  convert subset_of_eq (range_comp γ φ).symm
  rw [(φ.surjective hφ).range_eq, image_univ]

/-- This is only a stepping stone potentially useful for `SurroundingFamily.surrounds_of_close`,
  but not needed by itself. -/
theorem Surrounds.eventually_surrounds [FiniteDimensional ℝ F] (h : γ.Surrounds x) :
    ∃ ε > 0,
      ∀ (γ' : Loop F) (y : F), (∀ z, dist (γ' z) (γ z) < ε) → dist y x < ε → γ'.Surrounds y := by
  obtain ⟨t, w, h⟩ := h
  obtain ⟨W, hW⟩ := smooth_surroundingPts h
  obtain ⟨ε, hε, h⟩ := Metric.eventually_nhds_iff.mp hW
  refine ⟨ε, hε, fun γ' y hγ' hy ↦ ⟨t, W y (γ' ∘ t), ?_⟩⟩
  refine (@h ⟨y, γ' ∘ t⟩ ?_).2
  simp_rw [Prod.dist_eq, max_lt_iff, dist_pi_lt_iff hε]
  exact ⟨hy, fun b ↦ hγ' (t b)⟩

end Loop

section surroundingLoop

variable {O : Set F} {b : F} {p : Fin (d + 1) → F} (O_conn : IsPathConnected O)
  (hp : ∀ i, p i ∈ O) (hb : b ∈ O)

/-- witness of `surrounding_loop_of_convexHull` -/
def surroundingLoop : ℝ → Loop F :=
  Loop.roundTripFamily <| (O_conn.somePath hb (hp 0)).trans <| O_conn.pathThrough hp d

variable {O_conn hp hb}

/-- TODO: continuity note -/
@[fun_prop]
theorem continuous_surroundingLoop : Continuous ↿(surroundingLoop O_conn hp hb) := by
  unfold surroundingLoop; fun_prop

@[simp]
theorem surroundingLoop_zero_right (t : ℝ) : surroundingLoop O_conn hp hb t 0 = b :=
  Loop.roundTripFamily_based_at t

@[simp]
theorem surroundingLoop_zero_left (s : ℝ) : surroundingLoop O_conn hp hb 0 s = b := by
  simp only [surroundingLoop, Loop.roundTripFamily_zero]; rfl

theorem surroundingLoop_mem (t s : ℝ) : surroundingLoop O_conn hp hb t s ∈ O := by
  revert s
  rw [← range_subset_iff]
  simp only [surroundingLoop, Loop.roundTripFamily, Loop.roundTrip_range,
    cast_coe]
  refine Subset.trans (truncate_range _) ?_
  simp only [trans_range, union_subset_iff, O_conn.range_somePath_subset,
    O_conn.range_pathThrough_subset, true_and]

theorem surroundingLoop_surrounds {f : F} {w : Fin (d + 1) → ℝ} (h : SurroundingPts f p w) :
    (surroundingLoop O_conn hp hb 1).Surrounds f := by
  rw [Loop.surrounds_iff_range_subset_range]
  refine ⟨p, w, h, ?_⟩
  simp only [surroundingLoop, Loop.roundTripFamily_one, Loop.roundTrip_range, trans_range,
    range_subset_iff, mem_union, O_conn.mem_range_pathThrough, or_true, forall_true_iff]

theorem surroundingLoop_projI (t : ℝ) :
    surroundingLoop O_conn hp hb (projI t) = surroundingLoop O_conn hp hb t :=
  Loop.roundTrip_eq fun s ↦ by simp_rw [Path.cast_coe, truncate_projI_right]

-- unused
theorem surroundingLoop_of_le_zero (s : ℝ) {t : ℝ} (ht : t ≤ 0) :
    surroundingLoop O_conn hp hb t s = b := by
  rw [← surroundingLoop_projI, projI_eq_zero.mpr ht, surroundingLoop_zero_left]

-- unused
theorem surroundingLoop_of_ge_one (s : ℝ) {t : ℝ} (ht : 1 ≤ t) :
    surroundingLoop O_conn hp hb t s = surroundingLoop O_conn hp hb 1 s := by
  rw [← surroundingLoop_projI t, projI_eq_one.mpr ht]

theorem surrounding_loop_of_convexHull [FiniteDimensional ℝ F] {f b : F} {O : Set F}
    (O_op : IsOpen O) (O_conn : IsConnected O) (hsf : f ∈ convexHull ℝ O) (hb : b ∈ O) :
    ∃ γ : ℝ → Loop F,
      Continuous ↿γ ∧
        (∀ t, γ t 0 = b) ∧
          (∀ s, γ 0 s = b) ∧
            (∀ s t, γ (projI t) s = γ t s) ∧ (∀ t s, γ t s ∈ O) ∧ (γ 1).Surrounds f := by
  rcases surrounded_of_convexHull O_op hsf with ⟨p, w, h, hp⟩
  rw [O_op.isConnected_iff_isPathConnected] at O_conn
  exact ⟨surroundingLoop O_conn hp hb, continuous_surroundingLoop, surroundingLoop_zero_right,
    surroundingLoop_zero_left, fun s t ↦ by rw [surroundingLoop_projI], surroundingLoop_mem,
    surroundingLoop_surrounds h⟩

end surroundingLoop

/-- `γ` forms a family of loops surrounding `g` with base `b`.
In contrast to the notes we assume that `base` and `t₀` hold universally. -/
structure SurroundingFamily (g b : E → F) (γ : E → ℝ → Loop F) (U : Set E) : Prop where
  protected base : ∀ (x : E) (t : ℝ), γ x t 0 = b x
  protected t₀ : ∀ (x : E) (s : ℝ), γ x 0 s = b x
  protected projI : ∀ (x : E) (t : ℝ) (s : ℝ), γ x (projI t) s = γ x t s
  protected surrounds : ∀ x ∈ U, (γ x 1).Surrounds <| g x
  protected cont : Continuous ↿γ

/-- `γ` forms a family of loops surrounding `g` with base `b` in `Ω`. -/
structure SurroundingFamilyIn (g b : E → F) (γ : E → ℝ → Loop F) (U : Set E)
    (Ω : Set <| E × F) : Prop extends SurroundingFamily g b γ U where
  val_in' : ∀ x ∈ U, ∀ t ∈ I, ∀ s ∈ I, (x, γ x t s) ∈ Ω

namespace SurroundingFamily

variable {g b : E → F} {γ : E → ℝ → Loop F} {U : Set E}

omit [NormedSpace ℝ E]

protected theorem one (h : SurroundingFamily g b γ U) (x : E) (t : ℝ) : γ x t 1 = b x := by
  rw [Loop.one, h.base]

protected theorem t_le_zero (h : SurroundingFamily g b γ U) (x : E) (s : ℝ) {t : ℝ} (ht : t ≤ 0) :
    γ x t s = γ x 0 s := by rw [← h.projI, projI_eq_zero.mpr ht]

protected theorem t_le_zero_eq_b (h : SurroundingFamily g b γ U) (x : E) (s : ℝ) {t : ℝ}
    (ht : t ≤ 0) : γ x t s = b x := by rw [h.t_le_zero x s ht, h.t₀]

protected theorem t_ge_one (h : SurroundingFamily g b γ U) (x : E) (s : ℝ) {t : ℝ} (ht : 1 ≤ t) :
    γ x t s = γ x 1 s := by rw [← h.projI, projI_eq_one.mpr ht]

protected theorem mono (h : SurroundingFamily g b γ U) {V : Set E} (hVU : V ⊆ U) :
    SurroundingFamily g b γ V :=
  ⟨h.base, h.t₀, h.projI, fun x hx ↦ h.surrounds x (hVU hx), h.cont⟩

variable [NormedSpace ℝ E] in
protected theorem surrounds_of_close_univ [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (hg : Continuous g) (h : SurroundingFamily g b γ univ) :
    ∃ ε : E → ℝ,
      (∀ x, 0 < ε x) ∧
        Continuous ε ∧
          ∀ (x) (γ' : Loop F), (∀ z, dist (γ' z) (γ x 1 z) < ε x) → γ'.Surrounds (g x) := by
  let P : E → ℝ → Prop := fun x t ↦
    0 < t ∧ ∀ γ' : Loop F, (∀ z, dist (γ' z) (γ x 1 z) < t) → γ'.Surrounds (g x)
  have hP : ∀ x, Convex ℝ {t | P x t} := by
    intro x
    rw [convex_iff_ordConnected]
    constructor
    rintro ε₁ hε₁ ε₂ hε₂ ε₃ ⟨hε₁₃, hε₃₂⟩
    exact ⟨hε₁.1.trans_le hε₁₃, fun γ hγ ↦ hε₂.2 γ fun z ↦ (hγ z).trans_le hε₃₂⟩
  rsuffices ⟨ε, hε, hPε⟩ : ∃ ε : E → ℝ, 𝒞 0 ε ∧ ∀ x, P x (ε x)
  -- obtain ⟨ε, hε, hPε⟩ := exists_contDiff_of_convex hP _
  · exact ⟨ε, fun x ↦ (hPε x).1, contDiff_zero.mp hε, fun x ↦ (hPε x).2⟩
  refine exists_contDiff_of_convex hP fun x ↦ ?_
  obtain ⟨ε, hε, h2⟩ := (h.surrounds x (mem_univ _)).eventually_surrounds
  have h3 : {y : E | dist (g y) (g x) < ε} ∈ 𝓝 x :=
    (Metric.isOpen_ball.preimage hg).mem_nhds
      (by simp_rw [mem_preimage, Metric.mem_ball, dist_self, hε.lt])
  have h4 : {y : E | ∀ z, dist (γ y 1 z) (γ x 1 z) < ε / 2} ∈ 𝓝 x := by
    refine IsOpen.mem_nhds ?_ fun z ↦ by simp_rw [dist_self, half_pos hε]
    have hc : Continuous ↿fun y s ↦ dist (γ y 1 s) (γ x 1 s) :=
      (h.cont.comp₃ continuous_fst continuous_const continuous_snd).dist
        (h.cont.comp₃ continuous_const continuous_const continuous_snd)
    have : IsOpen {y : E | sSup ((fun z ↦ dist (γ y 1 z) (γ x 1 z)) '' I) < ε / 2} :=
      isOpen_lt (isCompact_Icc.continuous_sSup hc) continuous_const
    have hc : ∀ y, Continuous fun s ↦ dist (γ y 1 s) (γ x 1 s) := fun y ↦
      hc.comp₂ continuous_const continuous_id
    simp_rw [isCompact_Icc.sSup_lt_iff_of_continuous (nonempty_Icc.mpr zero_le_one)
        (hc _).continuousOn] at this
    convert this using 1
    ext y
    refine ⟨fun h z _ ↦ h z, fun h z ↦ ?_⟩
    rw [← (γ y 1).fract_eq, ← (γ x 1).fract_eq]
    exact h _ (unitInterval.fract_mem _)
  refine ⟨_, inter_mem h4 h3, fun _ ↦ ε / 2, contDiffOn_const, fun y hy ↦
      ⟨half_pos hε, fun γ' hγ' ↦ h2 _ _ (fun z ↦ ?_) hy.2⟩⟩
  exact (dist_triangle _ _ _).trans_lt ((add_lt_add (hγ' z) (hy.1 z)).trans_le (add_halves ε).le)

-- proof using `surrounds_of_close`
-- begin
--   obtain ⟨ε, hε, hcε, hγε⟩ := h.surrounds_of_close hg isOpen_univ,
--   exact ⟨ε, λ x, hε x (mem_univ _), continuous_iff_continuous_on_univ.mpr hcε,
--     λ x, hγε x (mem_univ _)⟩
-- end
/-- A surrounding family induces a family of paths from `b x` to `b x`.
We defined the concatenation we need on `path`, so we need to turn a surrounding
family into the family of paths. -/
@[simps]
protected def path (h : SurroundingFamily g b γ U) (x : E) (t : ℝ) : Path (b x) (b x) where
  toFun s := γ x t s
  continuous_toFun :=
    (h.cont.comp₃ continuous_const continuous_const continuous_id).comp continuous_subtype_val
  source' := h.base x t
  target' := h.one x t

@[fun_prop]
theorem continuous_path {X : Type*} [TopologicalSpace X] (h : SurroundingFamily g b γ U)
    {t : X → ℝ} {f : X → E} {s : X → I} (hf : Continuous f) (ht : Continuous t)
    (hs : Continuous s) : Continuous fun x ↦ h.path (f x) (t x) (s x) :=
  h.cont.comp₃ hf ht hs.subtype_val

@[simp]
theorem path_extend_fract (h : SurroundingFamily g b γ U) (t s : ℝ) (x : E) :
    (h.path x t).extend (fract s) = γ x t s := by
  rw [extend_extends _ (unitInterval.fract_mem s), ← Loop.fract_eq]; rfl

@[simp]
theorem range_path (h : SurroundingFamily g b γ U) (x : E) (t : ℝ) :
    range (h.path x t) = range (γ x t) := by
  simp only [Loop.range_eq_image, SurroundingFamily.path, Path.coe_mk_mk]
  erw [range_comp]
  simp only [Subtype.range_coe]

@[simp]
theorem path_t₀ (h : SurroundingFamily g b γ U) (x : E) : h.path x 0 = .refl (b x) := by
  ext t
  exact h.t₀ x t

end SurroundingFamily

variable {g b : E → F} {U K C : Set E} {Ω : Set (E × F)}

namespace SurroundingFamilyIn

variable {γ : E → ℝ → Loop F}

omit [NormedSpace ℝ E]

/-- Abbreviation for `toSurroundingFamily` -/
theorem to_sf (h : SurroundingFamilyIn g b γ U Ω) : SurroundingFamily g b γ U :=
  h.toSurroundingFamily

theorem val_in (h : SurroundingFamilyIn g b γ U Ω) {x : E} (hx : x ∈ U) {t : ℝ} {s : ℝ} :
    (x, γ x t s) ∈ Ω := by
  rw [← Loop.fract_eq, ← h.projI]
  exact h.val_in' x hx (projI t) projI_mem_Icc (fract s) (unitInterval.fract_mem s)

protected theorem mono (h : SurroundingFamilyIn g b γ U Ω) {V : Set E} (hVU : V ⊆ U) :
    SurroundingFamilyIn g b γ V Ω :=
  ⟨h.to_sf.mono hVU, fun x hx ↦ h.val_in' x (hVU hx)⟩

/-- Continuously reparameterize a `surroundingFamilyIn` so that it is constant near
  `s ∈ {0,1}` and `t ∈ {0,1}` -/
protected theorem reparam (h : SurroundingFamilyIn g b γ U Ω) :
    SurroundingFamilyIn g b (fun x t ↦ (γ x (linearReparam t)).reparam linearReparam) U Ω := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro x t; rw [Loop.reparam_apply, linearReparam_zero, h.base]
  · intro x s; rw [Loop.reparam_apply, linearReparam_zero, h.t₀]
  · intro x t s; simp_rw [Loop.reparam_apply, linearReparam_projI, h.projI]
  · intro x hx; rw [linearReparam_one]
    exact (h.surrounds x hx).reparam continuous_linearReparam
  · exact h.cont.comp₃ continuous_fst continuous_linearReparam.fst'.snd'
      continuous_linearReparam.snd'.snd'
  · exact fun x hx t _ s _ ↦ h.val_in hx

end SurroundingFamilyIn

section local_loops

variable {x₀ : E} (hΩ_conn : IsPathConnected (Prod.mk x₀ ⁻¹' Ω)) (hb_in : (x₀, b x₀) ∈ Ω)
  {p : Fin (d + 1) → F} (hp : ∀ i, p i ∈ Prod.mk x₀ ⁻¹' Ω)

omit [NormedSpace ℝ E]

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
-- /-- The witness of `local_loops`. -/
-- def local_loops_def (x : E) (t : ℝ) : loop F :=
-- b x - b x₀ +ᵥ surrounding_loop hΩ_conn hp hb_in t
/-- Note: The conditions in this lemma are currently a bit weaker than the ones mentioned in the
blueprint.
TODO: use `local_loops_def`
-/
theorem local_loops [FiniteDimensional ℝ F] {x₀ : E} (hΩ_op : ∃ U ∈ 𝓝 x₀, IsOpen (Ω ∩ fst ⁻¹' U))
    (hg : ContinuousAt g x₀) (hb : Continuous b)
    (hconv : g x₀ ∈ convexHull ℝ (connectedComponentIn (Prod.mk x₀ ⁻¹' Ω) <| b x₀)) :
    ∃ γ : E → ℝ → Loop F, ∃ U ∈ 𝓝 x₀, SurroundingFamilyIn g b γ U Ω := by
  have hΩ_op_x₀ : IsOpen (connectedComponentIn (Prod.mk x₀ ⁻¹' Ω) <| b x₀) :=
    (isOpen_slice_of_isOpen_over hΩ_op).connectedComponentIn
  have b_in : b x₀ ∈ Prod.mk x₀ ⁻¹' Ω :=
    connectedComponentIn_nonempty_iff.mp (convexHull_nonempty_iff.mp ⟨g x₀, hconv⟩)
  have hΩ_conn : IsConnected (connectedComponentIn (Prod.mk x₀ ⁻¹' Ω) <| b x₀) :=
    isConnected_connectedComponentIn_iff.mpr b_in
  have hb_in : b x₀ ∈ (connectedComponentIn (Prod.mk x₀ ⁻¹' Ω) <| b x₀) :=
    mem_connectedComponentIn b_in
  rcases surrounding_loop_of_convexHull hΩ_op_x₀ hΩ_conn hconv hb_in with
    ⟨γ, h1γ, h2γ, h3γ, h4γ, h5γ, h6γ⟩
  have h5γ : ∀ t s : ℝ, γ t s ∈ mk x₀ ⁻¹' Ω := fun t s ↦ connectedComponentIn_subset _ _ (h5γ t s)
  let δ : E → ℝ → Loop F := fun x t ↦ (b x - b x₀) +ᵥ γ t
  have hδ : Continuous ↿δ := by
    dsimp only [δ, HasUncurry.uncurry, Loop.vadd_apply]
    fun_prop
  have hδx₀ : ∀ t s, δ x₀ t s = γ t s := by
    intro t s
    simp only [δ, zero_add, Loop.vadd_apply, sub_self]
  have hδs0 : ∀ x t, δ x t 0 = b x := by intro x t; simp [δ, h2γ]
  have hδt0 : ∀ x s, δ x 0 s = b x := by intro x s; simp [δ, h3γ]
  have hδt1 : ∀ x t s, δ x (projI t) s = δ x t s := by intro x t s; simp [δ, h4γ]
  have hδΩ : ∀ᶠ x in 𝓝 x₀, ∀ t ∈ I, ∀ s ∈ I, (x, δ x t s) ∈ Ω := by
    rcases hΩ_op with ⟨U, hUx₀, hU⟩
    -- todo: this is nicer with `IsCompact.eventually_forall_of_forall_eventually` twice, but then
    -- we need the continuity of `δ` with the arguments reassociated differently.
    have : ∀ᶠ x : E in 𝓝 x₀, ∀ ts : ℝ × ℝ, ts ∈ I ×ˢ I → (x, δ x ts.1 ts.2) ∈ Ω := by
      apply (isCompact_Icc.prod isCompact_Icc).eventually_forall_mem
      · fun_prop
      · rintro ⟨t, s⟩ _
        rw [hδx₀]
        change Ω ∈ 𝓝 (x₀, γ t s)
        exact mem_nhds_iff.mpr
          ⟨_, inter_subset_left, hU, ⟨h5γ t s, show x₀ ∈ U from mem_of_mem_nhds hUx₀⟩⟩
    refine this.mono ?_; intro x h t ht s hs; exact h (t, s) ⟨ht, hs⟩
  have hδsurr : ∀ᶠ x in 𝓝 x₀, (δ x 1).Surrounds (g x) := by
    rcases h6γ with ⟨p, w, h⟩
    obtain ⟨W, hW⟩ := smooth_surroundingPts h
    let c : E → F × (Fin (d + 1) → F) := fun x ↦ (g x, δ x 1 ∘ p)
    have hc : ContinuousAt c x₀ := by fun_prop
    have hcx₀ : c x₀ = (g x₀, γ 1 ∘ p) := by
      simp [c, δ]
    rw [← hcx₀] at hW
    filter_upwards [hc.tendsto.eventually hW]
    rintro x ⟨_, hx⟩
    exact ⟨_, _, hx⟩
  exact ⟨δ, _, hδΩ.and hδsurr, ⟨⟨hδs0, hδt0, hδt1, fun x ↦ And.right, hδ⟩, fun x ↦ And.left⟩⟩

/-- A tiny reformulation of `local_loops` where the existing `U` is open. -/
theorem local_loops_open [FiniteDimensional ℝ F] {x₀ : E}
    (hΩ_op : ∃ U ∈ 𝓝 x₀, IsOpen (Ω ∩ fst ⁻¹' U)) (hg : ContinuousAt g x₀) (hb : Continuous b)
    (hconv : g x₀ ∈ convexHull ℝ (connectedComponentIn (Prod.mk x₀ ⁻¹' Ω) <| b x₀)) :
    ∃ (γ : E → ℝ → Loop F) (U : Set E), IsOpen U ∧ x₀ ∈ U ∧ SurroundingFamilyIn g b γ U Ω := by
  obtain ⟨γ, U, hU, hγ⟩ := local_loops hΩ_op hg hb hconv
  obtain ⟨V, hVU, hV, hx₀V⟩ := mem_nhds_iff.mp hU
  exact ⟨γ, V, hV, hx₀V, hγ.mono hVU⟩

end local_loops

/-- Function used in `satisfied_or_refund`. Rename. -/
def ρ (t : ℝ) : ℝ :=
  projI <| 2 * (1 - t)

attribute [fun_prop] continuous_projI

@[fun_prop]
theorem continuous_ρ : Continuous ρ := by unfold ρ; fun_prop

@[simp]
theorem ρ_eq_one {x : ℝ} : ρ x = 1 ↔ x ≤ 1 / 2 := by
  rw [ρ, projI_eq_one]
  constructor <;> intros <;> linarith

@[simp]
theorem ρ_eq_one_of_le {x : ℝ} (h : x ≤ 1 / 2) : ρ x = 1 :=
  ρ_eq_one.mpr h

@[simp]
theorem ρ_eq_one_of_nonpos {x : ℝ} (h : x ≤ 0) : ρ x = 1 :=
  ρ_eq_one_of_le <| h.trans <| by norm_num

@[simp]
theorem ρ_eq_zero {x : ℝ} : ρ x = 0 ↔ 1 ≤ x := by
  rw [ρ, projI_eq_zero]
  constructor <;> intros <;> linarith

@[simp]
theorem ρ_eq_zero_of_le {x : ℝ} (h : 1 ≤ x) : ρ x = 0 :=
  ρ_eq_zero.mpr h

theorem ρ_mem_I {x : ℝ} : ρ x ∈ I :=
  projI_mem_Icc

section satisfied_or_refund

variable {γ₀ γ₁ : E → ℝ → Loop F}

variable (h₀ : SurroundingFamily g b γ₀ U) (h₁ : SurroundingFamily g b γ₁ U)

/-- The homotopy of surrounding families of loops used in lemma `satisfied_or_refund`.
  Having this as a separate definition is useful, because the construction actually gives some
  more information about the homotopy than the theorem `satisfied_or_refund` gives. -/
def sfHomotopy (τ : ℝ) (x : E) (t : ℝ) :=
  Loop.ofPath <|
    (h₀.path x <| ρ τ * projI t).strans (h₁.path x <| ρ (1 - τ) * projI t) <|
      projIcc 0 1 zero_le_one (1 - τ)

variable {h₀ h₁}

omit [NormedSpace ℝ E]

@[simp]
theorem sfHomotopy_zero : sfHomotopy h₀ h₁ 0 = γ₀ := by
  ext x t s
  simp only [sfHomotopy, one_mul, ρ_eq_one_of_nonpos le_rfl, SurroundingFamily.path_extend_fract,
             sub_zero, Loop.ofPath_apply, Icc.mk_one, projIcc_right, Path.strans_one, h₀.projI]

@[simp]
theorem sfHomotopy_one : sfHomotopy h₀ h₁ 1 = γ₁ := by
  ext x t s
  simp only [sfHomotopy, Path.strans_zero, Icc.mk_zero, one_mul, ρ_eq_one_of_nonpos le_rfl,
    SurroundingFamily.path_extend_fract, projIcc_left, Loop.ofPath_apply, sub_self, h₁.projI]

attribute [fun_prop] continuous_projIcc

@[fun_prop]
theorem Continuous.sfHomotopy {X : Type*} [UniformSpace X]
    [LocallyCompactSpace X] {τ t s : X → ℝ} {f : X → E} (hτ : Continuous τ) (hf : Continuous f)
    (ht : Continuous t) (hs : Continuous s) :
    Continuous fun x ↦ sfHomotopy h₀ h₁ (τ x) (f x) (t x) (s x) := by
  refine Continuous.ofPath _ _ _ ?_ hs
  refine Continuous.path_strans ?_ ?_ ?_ ?_ ?_ continuous_snd
  · fun_prop
  · fun_prop
  · intro x s hs; simp only [projIcc_eq_zero, sub_nonpos] at hs
    simp only [hs, h₀.t₀, MulZeroClass.zero_mul, SurroundingFamily.path_apply, ρ_eq_zero_of_le]
  · intro x s hs; simp only [projIcc_eq_one] at hs
    simp only [hs, h₁.t₀, MulZeroClass.zero_mul, SurroundingFamily.path_apply, ρ_eq_zero_of_le]
  · fun_prop

/-- In this lemmas and the lemmas below we add `FiniteDimensional ℝ E` so that we can conclude
 `LocallyCompactSpace E`. -/
@[fun_prop]
theorem continuous_sfHomotopy [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    Continuous ↿(sfHomotopy h₀ h₁) := by fun_prop

theorem surroundingFamily_sfHomotopy [NormedSpace ℝ E] [FiniteDimensional ℝ E] (τ : ℝ) :
    SurroundingFamily g b (sfHomotopy h₀ h₁ τ) U := by
  constructor
  · intro x t;
    simp only [sfHomotopy, Icc.mk_zero, zero_le_one, extend_extends, Path.source, Loop.ofPath_apply,
      left_mem_Icc, fract_zero]
  · intro x s
    -- have h2t : ρ τ * t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (ρ_nonneg τ) ht,
    -- have h3t : ρ (1 - τ) * t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (ρ_nonneg _) ht,
    -- have h4t : t ≤ 1 := ht.trans zero_le_one,
    simp [sfHomotopy]
  · intro x t s; simp only [sfHomotopy, projI_projI]
  -- { intros x t s ht, simp only [sfHomotopy, min_eq_left ht, min_self] },
  · intro x hx; obtain (h | h) := le_total τ (1 / 2)
    · have : τ < 1 := h.trans_lt (by norm_num)
      refine (h₀.surrounds x hx).mono ?_
      simp only [mul_one, Loop.range_ofPath, sfHomotopy, projI_one]
      exact Subset.trans (by simp only [SurroundingFamily.range_path, ρ_eq_one_of_le h]; rfl)
        (subset_range_strans_left <| by simp [this])
    · have : 0 < τ := lt_of_lt_of_le (by norm_num) h
      have h : 1 - τ ≤ 1 / 2 := by linarith
      refine (h₁.surrounds x hx).mono ?_
      simp only [mul_one, Loop.range_ofPath, sfHomotopy, projI_one]
      exact Subset.trans (by simp only [SurroundingFamily.range_path, ρ_eq_one_of_le h]; rfl)
        (subset_range_strans_right <| by simp [this])
  · fun_prop

/-- A more precise version of `sfHomotopy_in`. -/
theorem sfHomotopy_in' {ι} (h₀ : SurroundingFamily g b γ₀ U) (h₁ : SurroundingFamily g b γ₁ U)
    (τ : ι → ℝ) (x : ι → E) (i : ι) {V : Set E} (hx : x i ∈ V) {t : ℝ} (ht : t ∈ I) {s : ℝ}
    (h_in₀ : ∀ i, x i ∈ V → ∀ t ∈ I, ∀ (s : ℝ), τ i ≠ 1 → (x i, γ₀ (x i) t s) ∈ Ω)
    (h_in₁ : ∀ i, x i ∈ V → ∀ t ∈ I, ∀ (s : ℝ), τ i ≠ 0 → (x i, γ₁ (x i) t s) ∈ Ω) :
    (x i, sfHomotopy h₀ h₁ (τ i) (x i) t s) ∈ Ω := by
  by_cases hτ0 : τ i = 0; · simp [hτ0]; exact h_in₀ i hx t ht s (by norm_num [hτ0])
  by_cases hτ1 : τ i = 1; · simp [hτ1]; exact h_in₁ i hx t ht s (by norm_num [hτ1])
  generalize hy : sfHomotopy h₀ h₁ (τ i) (x i) t s = y
  have h2y : y ∈ range (sfHomotopy h₀ h₁ (τ i) (x i) t) := by rw [← hy]; exact mem_range_self _
  rw [sfHomotopy, Loop.range_ofPath, projI_eq_self.mpr ht] at h2y
  replace h2y := range_strans_subset h2y
  rcases h2y with (⟨s', rfl⟩ | ⟨s', rfl⟩)
  · exact h_in₀ _ hx _ (unitInterval.mul_mem ρ_mem_I ht) _ hτ1
  · exact h_in₁ _ hx _ (unitInterval.mul_mem ρ_mem_I ht) _ hτ0

theorem sfHomotopy_in (h₀ : SurroundingFamilyIn g b γ₀ U Ω) (h₁ : SurroundingFamilyIn g b γ₁ U Ω)
    (τ : ℝ) ⦃x : E⦄ (hx : x ∈ U) {t : ℝ} (ht : t ∈ I) {s : ℝ} :
    (x, sfHomotopy h₀.to_sf h₁.to_sf τ x t s) ∈ Ω :=
  sfHomotopy_in' h₀.to_sf h₁.to_sf (fun _ ↦ τ) (fun _ ↦ x) () hx ht
    (fun _i hx _t _ _s _ ↦ h₀.val_in hx) fun _i hx _t _ _s _ ↦ h₁.val_in hx

theorem surroundingFamilyIn_sfHomotopy [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (h₀ : SurroundingFamilyIn g b γ₀ U Ω) (h₁ : SurroundingFamilyIn g b γ₁ U Ω) (τ : ℝ) :
    SurroundingFamilyIn g b (sfHomotopy h₀.to_sf h₁.to_sf τ) U Ω :=
  ⟨surroundingFamily_sfHomotopy _, fun _x hx _t ht _s _hs ↦ sfHomotopy_in h₀ h₁ _ hx ht⟩

theorem satisfied_or_refund [NormedSpace ℝ E] [FiniteDimensional ℝ E] {γ₀ γ₁ : E → ℝ → Loop F}
    (h₀ : SurroundingFamilyIn g b γ₀ U Ω) (h₁ : SurroundingFamilyIn g b γ₁ U Ω) :
    ∃ γ : ℝ → E → ℝ → Loop F,
      (∀ τ, SurroundingFamilyIn g b (γ τ) U Ω) ∧ γ 0 = γ₀ ∧ γ 1 = γ₁ ∧ Continuous ↿γ :=
  ⟨sfHomotopy h₀.to_sf h₁.to_sf, surroundingFamilyIn_sfHomotopy h₀ h₁, sfHomotopy_zero,
    sfHomotopy_one, continuous_sfHomotopy⟩

end satisfied_or_refund

section extend_loops

variable [FiniteDimensional ℝ E]

/-
Note: we also want add the condition that `γ = γ₀` outside a neighborhood of `U₁ᶜ`.
This makes it easier to find the limit of a sequence of these constructions.
-/
theorem extend_loops {U₀ U₁ K₀ K₁ : Set E} (hU₀ : IsOpen U₀) (hU₁ : IsOpen U₁) (hK₀ : IsClosed K₀)
    (hK₁ : IsClosed K₁) (hKU₀ : K₀ ⊆ U₀) (hKU₁ : K₁ ⊆ U₁) {γ₀ γ₁ : E → ℝ → Loop F}
    (h₀ : SurroundingFamilyIn g b γ₀ U₀ Ω) (h₁ : SurroundingFamilyIn g b γ₁ U₁ Ω) :
    ∃ U ∈ 𝓝ˢ (K₀ ∪ K₁),
      ∃ γ : E → ℝ → Loop F,
        SurroundingFamilyIn g b γ U Ω ∧
          (∀ᶠ x in 𝓝ˢ K₀, γ x = γ₀ x) ∧ ∀ᶠ x in 𝓝ˢ (U₁ᶜ), γ x = γ₀ x := by
  obtain ⟨V₀, hV₀, hKV₀, hVU₀⟩ := normal_exists_closure_subset hK₀ hU₀ hKU₀
  let L₁ := K₁ \ U₀
  have hL₁ : IsClosed L₁ := hK₁.sdiff hU₀
  have hV₀L₁ : Disjoint (closure V₀) L₁ := disjoint_sdiff_self_right.mono hVU₀ Subset.rfl
  obtain ⟨V₂, hV₂, hLV₂, h2V₂⟩ :=
    normal_exists_closure_subset hL₁ (isClosed_closure.isOpen_compl.inter hU₁)
      (subset_inter (subset_compl_iff_disjoint_left.mpr hV₀L₁) <| diff_subset.trans hKU₁)
  obtain ⟨V₁, hV₁, hLV₁, hV₁₂⟩ := normal_exists_closure_subset hL₁ hV₂ hLV₂
  rw [subset_inter_iff, subset_compl_iff_disjoint_left] at h2V₂
  rcases h2V₂ with ⟨hV₀₂, hV₂U₁⟩
  have hVU₁ : V₁ ⊆ U₁ := subset_closure.trans (hV₁₂.trans <| subset_closure.trans hV₂U₁)
  have hdisj : Disjoint (closure V₀ ∪ V₂ᶜ) (closure V₁) := by
    refine Disjoint.union_left (hV₀₂.mono_right (hV₁₂.trans subset_closure)) ?_
    rw [← subset_compl_iff_disjoint_left, compl_compl]; exact hV₁₂
  refine ⟨V₀ ∪ U₁ ∩ U₀ ∪ V₁, ((hV₀.union <| hU₁.inter hU₀).union hV₁).mem_nhdsSet.mpr ?_, ?_⟩
  · refine union_subset (hKV₀.trans <| subset_union_left.trans <| subset_union_left) ?_
    rw [← inter_union_diff K₁];
    exact union_subset_union ((inter_subset_inter_left _ hKU₁).trans <| subset_union_right) hLV₁
  obtain ⟨ρ, h0ρ, h1ρ, -⟩ :=
    exists_continuous_zero_one_of_isClosed (isClosed_closure.union hV₂.isClosed_compl)
      isClosed_closure hdisj
  let h₀' : SurroundingFamilyIn g b γ₀ (U₁ ∩ U₀) Ω := h₀.mono inter_subset_right
  let h₁' : SurroundingFamilyIn g b γ₁ (U₁ ∩ U₀) Ω := h₁.mono inter_subset_left
  let γ := sfHomotopy h₀'.to_sf h₁'.to_sf
  have hγ : ∀ τ, SurroundingFamilyIn g b (γ τ) (U₁ ∩ U₀) Ω := surroundingFamilyIn_sfHomotopy h₀' h₁'
  have heq1 : ∀ x ∈ closure V₀ ∪ V₂ᶜ, γ (ρ x) x = γ₀ x := by
    intro x hx
    simp_rw [γ, h0ρ hx, Pi.zero_apply, sfHomotopy_zero]
  have heq2 : ∀ x ∈ V₀, γ (ρ x) x = γ₀ x := fun x hx ↦
    heq1 x (subset_closure.trans subset_union_left hx)
  refine ⟨fun x t ↦ γ (ρ x) x t, ?_, ?_, ?_⟩
  · refine ⟨⟨fun x ↦ (hγ <| ρ x).base x, fun x ↦ (hγ <| ρ x).t₀ x, fun x ↦ (hγ <| ρ x).projI x,
      ?_, ?_⟩, ?_⟩
    · rintro x ((hx | hx) | hx)
      · simp_rw [heq2 x hx, h₀.surrounds x (hVU₀ <| subset_closure hx)]
      · simp_rw [γ]
        exact (hγ <| ρ x).surrounds x hx
      · simp_rw [γ, h1ρ (subset_closure hx), Pi.one_apply, sfHomotopy_one, h₁.surrounds x (hVU₁ hx)]
    · fun_prop
    · intro x hx t ht s _; refine sfHomotopy_in' _ _ _ id _ hx ht ?_ ?_
      · intro x hx t _ht s hρx; refine h₀.val_in ?_; rcases hx with ((hx | ⟨-, hx⟩) | hx)
        · exact (subset_closure.trans hVU₀) hx
        · exact hx
        · exact (hρx <| h1ρ <| subset_closure hx).elim
      · intro x hx t _ht s hρx; refine h₁.val_in ?_; rcases hx with ((hx | ⟨hx, -⟩) | hx)
        · exact (hρx <| h0ρ <| subset_closure.trans subset_union_left hx).elim
        · exact hx
        · exact hVU₁ hx
  · exact eventually_of_mem (hV₀.mem_nhdsSet.mpr hKV₀) heq2
  · exact eventually_of_mem
      (isClosed_closure.isOpen_compl.mem_nhdsSet.mpr <| compl_subset_compl.mpr hV₂U₁)
      fun x hx ↦ heq1 x <| mem_union_right _ <| compl_subset_compl.mpr subset_closure hx

end extend_loops

def ContinuousGerm {x : E} (φ : Germ (𝓝 x) (ℝ → Loop F)) : Prop :=
  Quotient.liftOn' φ
    (fun γ ↦ ∀ t s : ℝ, ContinuousAt (fun p : E × ℝ × ℝ ↦ γ p.1 p.2.1 p.2.2) (x, t, s))
    (by
      rintro γ γ' (h : {x | γ x = γ' x} ∈ 𝓝 x)
      ext
      refine forall_congr' fun t ↦ forall_congr' fun s ↦ continuousAt_congr ?_
      rw [nhds_prod_eq]
      apply mem_of_superset (Filter.prod_mem_prod h univ_mem)
      rintro ⟨x', p⟩ ⟨hx' : γ x' = γ' x', -⟩
      simp only [mem_setOf_eq, hx'])

variable (g b Ω)
omit [NormedSpace ℝ E]

structure LoopFamilyGerm (x : E) (φ : Germ (𝓝 x) (ℝ → Loop F)) : Prop where
  base : ∀ t, φ.value t 0 = b x
  t₀ : ∀ s, φ.value 0 s = b x
  projI : ∀ (t : ℝ) (s : ℝ), φ.value (projI t) s = φ.value t s
  cont : ContinuousGerm φ

structure SurroundingFamilyGerm (x : E) (φ : Germ (𝓝 x) (ℝ → Loop F)) : Prop where
  Surrounds : (φ.value 1).Surrounds <| g x
  val_in' : ∀ t ∈ I, ∀ s ∈ I, (x, φ.value t s) ∈ Ω

variable {g b Ω}

/-
The following proof is slightly tedious because the definition of `surroundingFamilyIn`
splits weirdly into `SurroundingFamily` which includes one condition on `C`
and one extra condition on `C` instead of putting everything which does not depend on `C`
on one side and the two conditions depending on `C` on the other side as we do here.
-/
theorem surroundingFamilyIn_iff_germ {γ : E → ℝ → Loop F} :
    SurroundingFamilyIn g b γ C Ω ↔
      (∀ x, LoopFamilyGerm b x γ) ∧ ∀ x ∈ C, SurroundingFamilyGerm g Ω x γ := by
  constructor
  · rintro ⟨⟨base, t₀, projI, family_surrounds, family_cont⟩, H⟩
    exact ⟨fun x ↦ ⟨base x, t₀ x, projI x, fun t s ↦ family_cont.continuousAt⟩, fun x x_in ↦
      ⟨family_surrounds x x_in, H x x_in⟩⟩
  · rintro ⟨h, h'⟩
    refine ⟨⟨fun x ↦ (h x).base, fun x ↦ (h x).t₀, fun x ↦ (h x).projI,
        fun x hx ↦ (h' x hx).Surrounds, ?_⟩,
      fun x hx ↦ (h' x hx).val_in'⟩
    apply continuous_iff_continuousAt.mpr
    rintro ⟨x, t, s⟩
    apply (h x).cont

variable [NormedSpace ℝ E] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [SecondCountableTopology E]

theorem exists_surrounding_loops (hK : IsClosed K) (hΩ_op : IsOpen Ω) (hg : ∀ x, ContinuousAt g x)
    (hb : Continuous b)
    (hconv : ∀ x, g x ∈ convexHull ℝ (connectedComponentIn (Prod.mk x ⁻¹' Ω) <| b x))
    {γ₀ : E → ℝ → Loop F} (hγ₀_surr : ∃ V ∈ 𝓝ˢ K, SurroundingFamilyIn g b γ₀ V Ω) :
    ∃ γ : E → ℝ → Loop F, SurroundingFamilyIn g b γ univ Ω ∧ ∀ᶠ x in 𝓝ˢ K, γ x = γ₀ x := by
  rcases hγ₀_surr with ⟨V, V_in, hV⟩
  obtain ⟨hV, h'V⟩ := surroundingFamilyIn_iff_germ.mp hV
  simp only [surroundingFamilyIn_iff_germ, mem_univ, forall_true_left, ← forall_and]
  apply
    relative_inductive_construction_of_loc (LoopFamilyGerm b) (SurroundingFamilyGerm g Ω) hK hV
      (mem_of_superset V_in h'V)
  · intro x
    rcases local_loops ⟨univ, univ_mem, by simp only [preimage_univ, inter_univ, hΩ_op]⟩ (hg x) hb
        (hconv x) with
      ⟨γ, U, U_in, H⟩
    obtain ⟨H, H'⟩ := surroundingFamilyIn_iff_germ.mp H
    exact ⟨γ, H, mem_of_superset U_in H'⟩
  · intro U₁ U₂ K₁ K₂ γ₁ γ₂ hU₁ hU₂ hK₁ hK₂ hKU₁ hKU₂ hγ₁ hγ₂ h'γ₁ h'γ₂
    rcases extend_loops hU₁ hU₂ hK₁.isClosed hK₂.isClosed hKU₁ hKU₂
      (surroundingFamilyIn_iff_germ.mpr ⟨hγ₁, h'γ₁⟩)
      (surroundingFamilyIn_iff_germ.mpr ⟨hγ₂, h'γ₂⟩) with ⟨U, U_in, γ, H, H''⟩
    rcases surroundingFamilyIn_iff_germ.mp H with ⟨H, H'⟩
    exact ⟨γ, H, mem_of_superset U_in H', Eventually.union_nhdsSet.mpr H''⟩
