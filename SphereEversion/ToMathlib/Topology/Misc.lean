import Mathlib.Algebra.Ring.Periodic
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Tactic.Cases
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.ShrinkingLemma

noncomputable section

open Set Function Filter TopologicalSpace
open scoped unitInterval Topology uniformity

section Maps

variable {α β : Type*} {f : α → β} {g : β → α}

variable [TopologicalSpace α] [TopologicalSpace β]

theorem Function.LeftInverse.isOpenMap {f : α → β} {g : β → α} (hfg : LeftInverse g f)
    (hf : IsOpen (range f)) (hg : ContinuousOn g (range f)) : IsOpenMap f := fun U hU ↦ by
  rw [hfg.image_eq]; exact hg.isOpen_inter_preimage hf hU

end Maps

section

-- TODO: move to Topology.Separation.Basic
theorem Filter.Eventually.closed_neighborhood {α} [TopologicalSpace α] [NormalSpace α] {C : Set α}
    {P : α → Prop} (hP : ∀ᶠ x in 𝓝ˢ C, P x) (hC : IsClosed C) :
    ∃ C' ∈ 𝓝ˢ C, IsClosed C' ∧ ∀ᶠ x in 𝓝ˢ C', P x := by
  obtain ⟨O, hO, hCO, hPO⟩ := mem_nhdsSet_iff_exists.mp hP
  obtain ⟨U, hU, hCU, hUO⟩ := normal_exists_closure_subset hC hO hCO
  exact ⟨closure U, mem_of_superset (hU.mem_nhdsSet.mpr hCU) subset_closure, isClosed_closure,
    eventually_of_mem (hO.mem_nhdsSet.mpr hUO) hPO⟩

end

section

theorem support_norm {α E : Type*} [NormedAddCommGroup E] (f : α → E) :
    (support fun a ↦ ‖f a‖) = support f :=
  Function.support_comp_eq norm norm_eq_zero f

@[to_additive]
theorem hasCompactMulSupport_of_subset {α β : Type*} [TopologicalSpace α] [T2Space α] [One β]
    {f : α → β} {K : Set α} (hK : IsCompact K) (hf : mulSupport f ⊆ K) : HasCompactMulSupport f :=
  hK.of_isClosed_subset (isClosed_mulTSupport f) (closure_minimal hf hK.isClosed)

theorem periodic_const {α β : Type*} [Add α] {a : α} {b : β} : Periodic (fun _ ↦ b) a := fun _ ↦
  rfl

end

section

/-! ## The standard ℤ action on ℝ is properly discontinuous

TODO: use that in ToMathlib.Algebra.Periodic?
-/

instance : VAdd ℤ ℝ :=
  ⟨fun n x ↦ (n : ℝ) + x⟩

instance : ProperlyDiscontinuousVAdd ℤ ℝ :=
  ⟨fun {K L} hK hL ↦ by
    rcases eq_empty_or_nonempty K with (rfl | hK') <;>
        rcases eq_empty_or_nonempty L with (rfl | hL') <;>
      try simp only [image_empty, inter_self, setOf_false, finite_empty, empty_inter, inter_empty,
        Set.not_nonempty_empty, image_inter_nonempty_iff]
    have hSK := (hK.isLUB_sSup hK').1
    have hIK := (hK.isGLB_sInf hK').1
    have hSL := (hL.isLUB_sSup hL').1
    have hIL := (hL.isGLB_sInf hL').1
    apply (finite_Icc ⌈sInf L - sSup K⌉ ⌊sSup L - sInf K⌋).subset
    intro n ⟨x, hk, hnk⟩
    replace hnk : (n : ℝ) + x ∈ L := hnk
    constructor
    · rw [Int.ceil_le]
      linarith [hIL hnk, hSK hk]
    · rw [Int.le_floor]
      linarith [hSL hnk, hIK hk]⟩

end

section Fract

open Int

/- properties of the (dis)continuity of `Int.fract` on `ℝ`.
To be PRed to Topology.Algebra.FloorRing
-/

theorem Ioo_floor_mem_nhds {x : ℝ} (h : x ∉ range Int.cast) : Ioo (⌊x⌋ : ℝ) (⌊x⌋ + 1 : ℝ) ∈ 𝓝 x :=
  Ioo_mem_nhds (floor_lt_self_iff.mpr h) (lt_floor_add_one x)

theorem loc_constant_floor {x : ℝ} (h : x ∉ range Int.cast) : floor =ᶠ[𝓝 x] fun _ ↦ ⌊x⌋ := by
  filter_upwards [Ioo_floor_mem_nhds h]
  intro y hy
  rw [floor_eq_on_Ico]
  exact mem_Ico_of_Ioo hy

theorem fract_eventuallyEq {x : ℝ} (h : fract x ≠ 0) : fract =ᶠ[𝓝 x] fun x' ↦ x' - floor x := by
  rw [Int.fract_ne_zero_iff] at h
  exact EventuallyEq.rfl.sub ((loc_constant_floor h).fun_comp _)

theorem Ioo_inter_Iio {α : Type*} [LinearOrder α] {a b c : α} :
    Ioo a b ∩ Iio c = Ioo a (min b c) := by ext; simp [and_assoc]

theorem fract_lt {x y : ℝ} {n : ℤ} (h1 : (n : ℝ) ≤ x) (h2 : x < n + y) : fract x < y := by
  obtain (hy | hy) := le_total y 1
  · rw [← fract_sub_intCast x n, fract_eq_self.mpr]
    · linarith
    · constructor <;> linarith
  · exact (fract_lt_one x).trans_le hy

theorem one_sub_lt_fract {x y : ℝ} {n : ℤ} (hy : y ≤ 1) (h1 : (n : ℝ) - y < x) (h2 : x < n) :
    1 - y < fract x := by
  have I₁ : 1 - y < x - (n - 1) := by linarith
  have I₂ : x - (n - 1) < 1 := by linarith
  norm_cast at I₁ I₂
  rw [← fract_sub_intCast x (n - 1), fract_eq_self.mpr]
  · exact I₁
  · constructor <;> linarith

theorem IsOpen.preimage_fract' {s : Set ℝ} (hs : IsOpen s) (h2s : 0 ∈ s → s ∈ 𝓝[<] (1 : ℝ)) :
    IsOpen (fract ⁻¹' s) := by
  rw [isOpen_iff_mem_nhds]
  rintro x (hx : fract x ∈ s)
  rcases eq_or_ne (fract x) 0 with (hx' | hx')
  · have H : (0 : ℝ) ∈ s := by rwa [hx'] at hx
    specialize h2s H
    rcases Int.fract_eq_zero_iff.mp hx' with ⟨n, rfl⟩; clear hx hx'
    have s_mem_0 := hs.mem_nhds H
    rcases(nhds_basis_zero_abs_lt ℝ).mem_iff.mp s_mem_0 with ⟨δ, δ_pos, hδ⟩
    rcases(nhdsWithin_hasBasis (nhds_basis_Ioo_pos (1 : ℝ)) _).mem_iff.mp h2s with ⟨ε, ε_pos, hε⟩
    rw [Set.Ioo_inter_Iio, min_eq_right (le_add_of_nonneg_right ε_pos.le)] at hε
    set ε' := min ε (1 / 2)
    have ε'_pos : 0 < ε' := lt_min ε_pos (by norm_num : (0 : ℝ) < 1 / 2)
    have hε' : Ioo (1 - ε') 1 ⊆ s := by
      apply Subset.trans _ hε
      apply Ioo_subset_Ioo_left
      linarith [min_le_left ε (1 / 2)]
    have mem : Ioo ((n : ℝ) - ε') (n + δ) ∈ 𝓝 (n : ℝ) := by apply Ioo_mem_nhds <;> linarith
    apply mem_of_superset mem
    rintro x ⟨hx, hx'⟩
    obtain (hx'' | hx'') := le_or_gt (n : ℝ) x
    · apply hδ
      rw [mem_setOf_eq, abs_eq_self.mpr (fract_nonneg x)]
      exact fract_lt hx'' hx'
    · apply hε'
      exact ⟨one_sub_lt_fract (by linarith [min_le_right ε (1 / 2)]) (by linarith) hx'',
        fract_lt_one x⟩
  · rw [Int.fract_ne_zero_iff] at hx'
    have H : Ico (⌊x⌋ : ℝ) (⌊x⌋ + 1) ∈ 𝓝 x :=
      mem_of_superset (Ioo_floor_mem_nhds hx') Ioo_subset_Ico_self
    exact (continuousOn_fract ⌊x⌋).continuousAt H (hs.mem_nhds hx)

theorem IsOpen.preimage_fract {s : Set ℝ} (hs : IsOpen s) (h2s : (0 : ℝ) ∈ s → (1 : ℝ) ∈ s) :
    IsOpen (fract ⁻¹' s) :=
  hs.preimage_fract' fun h ↦ nhdsWithin_le_nhds <| hs.mem_nhds (h2s h)

-- is `sᶜ ∉ 𝓝[<] (1 : ℝ)` equivalent to something like `ClusterPt (𝓝[Iio (1 : ℝ) ∩ s] (1 : ℝ)` ?
theorem IsClosed.preimage_fract {s : Set ℝ} (hs : IsClosed s)
    (h2s : sᶜ ∉ 𝓝[<] (1 : ℝ) → (0 : ℝ) ∈ s) : IsClosed (fract ⁻¹' s) :=
  isOpen_compl_iff.mp <| hs.isOpen_compl.preimage_fract' fun h ↦ by_contra fun h' ↦ h <| h2s h'

theorem fract_preimage_mem_nhds {s : Set ℝ} {x : ℝ} (h1 : s ∈ 𝓝 (fract x))
    (h2 : fract x = 0 → s ∈ 𝓝 (1 : ℝ)) : fract ⁻¹' s ∈ 𝓝 x := by
  by_cases hx : fract x = 0
  · obtain ⟨u, hus, hu, hxu⟩ := mem_nhds_iff.mp h1
    obtain ⟨v, hvs, hv, h1v⟩ := mem_nhds_iff.mp (h2 hx)
    rw [mem_nhds_iff]
    exact ⟨fract ⁻¹' (u ∪ v), preimage_mono (union_subset hus hvs),
      (hu.union hv).preimage_fract fun _ ↦ subset_union_right h1v, subset_union_left hxu⟩
  · exact (continuousAt_fract (sub_ne_zero.1 hx)).preimage_mem_nhds h1

end Fract

section

-- TODO: move to Mathlib.Topology.Constructions
-- needs classical
variable {α β γ δ ι : Type*} [TopologicalSpace α] [TopologicalSpace β] {x : α}
open scoped Classical in
theorem isOpen_slice_of_isOpen_over {Ω : Set (α × β)} {x₀ : α}
    (hΩ_op : ∃ U ∈ 𝓝 x₀, IsOpen (Ω ∩ Prod.fst ⁻¹' U)) : IsOpen (Prod.mk x₀ ⁻¹' Ω) := by
  rcases hΩ_op with ⟨U, hU, hU_op⟩; convert hU_op.preimage (Continuous.prodMk_right x₀) using 1
  simp_rw [preimage_inter, preimage_preimage, preimage_const, mem_of_mem_nhds hU, if_pos,
    inter_univ]

end

section projI

variable {α β : Type*} [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] {x c : α}

/-- If `α` is a `LinearOrderedSemiring`, then `projI : α → α` projection of `α` onto the unit
interval `[0, 1]`. -/
def projI : α → α := fun x ↦ projIcc (0 : α) 1 zero_le_one x

theorem projI_def : projI x = max 0 (min 1 x) :=
  rfl

theorem projIcc_eq_projI : (projIcc (0 : α) 1 zero_le_one x : α) = projI x :=
  rfl

theorem projI_of_le_zero (hx : x ≤ 0) : projI x = 0 :=
  congr_arg Subtype.val <| projIcc_of_le_left _ hx

@[simp]
theorem projI_zero : projI (0 : α) = 0 :=
  congr_arg Subtype.val <| projIcc_left _

theorem projI_of_one_le (hx : 1 ≤ x) : projI x = 1 :=
  congr_arg Subtype.val <| projIcc_of_right_le _ hx

@[simp]
theorem projI_one : projI (1 : α) = 1 :=
  congr_arg Subtype.val <| projIcc_right _

@[simp]
theorem projI_eq_zero : projI x = 0 ↔ x ≤ 0 := by
  rw [← projIcc_eq_left (zero_lt_one' α), Subtype.ext_iff]; rfl

@[simp]
theorem projI_eq_one : projI x = 1 ↔ 1 ≤ x := by
  rw [← projIcc_eq_right (zero_lt_one' α), Subtype.ext_iff]; rfl

theorem projI_mem_Icc : projI x ∈ Icc (0 : α) 1 :=
  (projIcc (0 : α) 1 zero_le_one x).prop

theorem projI_eq_self : projI x = x ↔ x ∈ Icc (0 : α) 1 :=
  ⟨fun h ↦ h ▸ projI_mem_Icc, fun h ↦ congr_arg Subtype.val <| projIcc_of_mem _ h⟩

@[simp]
theorem projI_projI : projI (projI x) = projI x :=
  projI_eq_self.mpr projI_mem_Icc

@[simp]
theorem projIcc_projI : projIcc (0 : α) 1 zero_le_one (projI x) = projIcc 0 1 zero_le_one x :=
  projIcc_of_mem _ projI_mem_Icc

@[simp]
theorem range_projI : range projI = Icc 0 1 := by
  erw [range_comp, range_projIcc, image_univ, Subtype.range_coe]

theorem monotone_projI : Monotone (projI : α → α) :=
  monotone_projIcc _

theorem strictMonoOn_projI : StrictMonoOn projI (Icc (0 : α) 1) :=
  strictMonoOn_projIcc _

theorem projI_le_max : projI x ≤ max 0 x :=
  max_le_max le_rfl <| min_le_right ..

theorem min_le_projI : min 1 x ≤ projI x :=
  le_max_right ..

theorem projI_le_iff : projI x ≤ c ↔ 0 ≤ c ∧ (1 ≤ c ∨ x ≤ c) := by
  simp_rw [projI_def, max_le_iff, min_le_iff]

@[simp]
theorem projI_eq_min : projI x = min 1 x ↔ 0 ≤ x := by
  simp_rw [projI_def, max_eq_right_iff, le_min_iff, zero_le_one, true_and]

theorem min_projI (h2 : 0 ≤ c) : min c (projI x) = projI (min c x) := by
  obtain (h3 | h3) := le_total c x <;> simp [h2, h3, projI_le_iff, projI_eq_min.mpr]
  simp [projI_eq_min.mpr, h2.trans h3, min_left_comm c, h3]

theorem continuous_projI [TopologicalSpace α] [OrderTopology α] : Continuous (projI : α → α) :=
  continuous_projIcc.subtype_val

theorem projI_mapsto {s : Set α} (h0s : (0 : α) ∈ s)
    (h1s : (1 : α) ∈ s) : MapsTo projI s s := fun x hx ↦
  (le_total 1 x).elim (fun h2x ↦ by rwa [projI_eq_one.mpr h2x]) fun h2x ↦
    (le_total 0 x).elim (fun h3x ↦ by rwa [projI_eq_self.mpr ⟨h3x, h2x⟩]) fun h3x ↦ by
      rwa [projI_eq_zero.mpr h3x]

-- about Path.truncate
theorem truncate_projI_right {X : Type*} [TopologicalSpace X] {a b : X} (γ : Path a b) (t₀ t₁ : ℝ)
    (s : I) : γ.truncate t₀ (projI t₁) s = γ.truncate t₀ t₁ s := by
  simp_rw [Path.truncate, Path.coe_mk_mk, Path.extend, IccExtend, Function.comp_def]
  rw [min_projI (s.prop.1.trans <| le_max_left _ _), ContinuousMap.coe_mk, projIcc_projI]

end projI

section

open Encodable Option

variable {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β]

-- can we restate this nicely?
/-- Given a locally finite sequence of sets indexed by an encodable type, we can naturally reindex
  this sequence to get a sequence indexed by `ℕ` (by adding some `∅` values).
  This new sequence is still locally finite. -/
theorem decode₂_locallyFinite {ι} [Encodable ι] {s : ι → Set α} (hs : LocallyFinite s) :
    LocallyFinite fun i ↦ (s <$> decode₂ ι i).getD ∅ := fun x ↦ by
  obtain ⟨U, hxU, hU⟩ := hs x
  refine ⟨U, hxU, ?_⟩
  have :
      encode ⁻¹' {i : ℕ | ((s <$> decode₂ ι i).getD ∅ ∩ U).Nonempty} =
      {i : ι | (s i ∩ U).Nonempty} := by
    simp_rw [preimage_setOf_eq, decode₂_encode, map_eq_map, map_some, getD_some]
  rw [← this] at hU
  refine finite_of_finite_preimage hU ?_
  intro n hn
  rw [← decode₂_ne_none_iff]
  intro h
  simp_rw [mem_setOf_eq, h, map_eq_map, map_none, getD_none, empty_inter] at hn
  exact (not_nonempty_empty hn).elim

variable {X : Type*} [EMetricSpace X] [LocallyCompactSpace X] [SecondCountableTopology X]

set_option linter.style.cases false in
theorem exists_locallyFinite_subcover_of_locally {C : Set X} (hC : IsClosed C) {P : Set X → Prop}
    (hP : Antitone P) (h0 : P ∅) (hX : ∀ x ∈ C, ∃ V ∈ 𝓝 (x : X), P V) :
    ∃ (K : ℕ → Set X) (W : ℕ → Set X), (∀ n, IsCompact (K n)) ∧ (∀ n, IsOpen (W n)) ∧
      (∀ n, P (W n)) ∧ (∀ n, K n ⊆ W n) ∧ LocallyFinite W ∧ C ⊆ ⋃ n, K n := by
  choose V' hV' hPV' using SetCoe.forall'.mp hX
  choose V hV hVV' hcV using fun x : C ↦ LocallyCompactSpace.local_compact_nhds (↑x) (V' x) (hV' x)
  simp_rw [← mem_interior_iff_mem_nhds] at hV
  have : C ⊆ ⋃ x : C, interior (V x) := fun x hx ↦ by rw [mem_iUnion]; exact ⟨⟨x, hx⟩, hV _⟩
  obtain ⟨s, hs, hsW₂⟩ := isOpen_iUnion_countable (fun x ↦ interior (V x)) fun x ↦ isOpen_interior
  rw [← hsW₂, biUnion_eq_iUnion] at this; clear hsW₂
  obtain ⟨W, hW, hUW, hlW, hWV⟩ :=
    precise_refinement_set hC (fun x : s ↦ interior (V x)) (fun x ↦ isOpen_interior) this
  obtain ⟨K, hCK, hK, hKW⟩ :=
    exists_subset_iUnion_closed_subset hC (fun x : s ↦ hW x) (fun x _ ↦ hlW.point_finite x) hUW
  haveI : Encodable s := hs.toEncodable
  let K' : ℕ → Set X := fun n ↦ (K <$> decode₂ s n).getD ∅
  let W' : ℕ → Set X := fun n ↦ (W <$> decode₂ s n).getD ∅
  refine ⟨K', W', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n; cases' h : decode₂ s n with i
    · simp_rw [K', h, map_eq_map, map_none, getD_none, isCompact_empty]
    · simp_rw [K', h, map_eq_map, map_some, getD_some]
      exact (hcV i).of_isClosed_subset (hK i) ((hKW i).trans <| (hWV i).trans interior_subset)
  · intro n; cases h : decode₂ s n
    · simp_rw [W', h, map_eq_map, map_none, getD_none, isOpen_empty]
    · simp_rw [W', h, map_eq_map, map_some, getD_some, hW]
  · intro n; cases' h : decode₂ s n with i
    · simp_rw [W', h, map_eq_map, map_none, getD_none, h0]
    · simp_rw [W', h, map_eq_map, map_some, getD_some]; refine hP ?_ (hPV' i)
      exact (hWV i).trans (interior_subset.trans <| hVV' i)
  · intro n; cases h : decode₂ s n
    · simp_rw [K', W', h, map_eq_map, map_none]; rfl
    · simp_rw [K', W', h, map_eq_map, map_some, getD_some, hKW]
  · exact decode₂_locallyFinite hlW
  · intro x hx; obtain ⟨i, hi⟩ := mem_iUnion.mp (hCK hx)
    refine mem_iUnion.mpr ⟨encode i, ?_⟩
    simp_rw [K', decode₂_encode, map_eq_map, map_some, getD_some, hi]

end

section

-- TODO: move to Topology.Compactness.Compact
variable {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

theorem IsCompact.eventually_forall_mem {x₀ : α} {K : Set β} (hK : IsCompact K) {f : α → β → γ}
    (hf : Continuous ↿f) {U : Set γ} (hU : ∀ y ∈ K, U ∈ 𝓝 (f x₀ y)) :
    ∀ᶠ x in 𝓝 x₀, ∀ y ∈ K, f x y ∈ U :=
  hK.eventually_forall_of_forall_eventually fun y hy ↦
    (hf.tendsto _).eventually <| show U ∈ 𝓝 ((↿f) (x₀, y)) from hU y hy

end

section

open Metric

attribute [fun_prop] continuous_infDist_pt

theorem Continuous.infDist {α β : Type*} [TopologicalSpace α] [PseudoMetricSpace β] {s : Set β}
    {f : α → β} (hf : Continuous f) : Continuous fun x ↦ infDist (f x) s := by fun_prop

end

section NormedSpace

open Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem isPreconnected_ball (x : E) (r : ℝ) : IsPreconnected (ball x r) :=
  (convex_ball x r).isPreconnected

theorem isConnected_ball {x : E} {r : ℝ} : IsConnected (ball x r) ↔ 0 < r := by
  simp [IsConnected, isPreconnected_ball]

-- todo: make Metric.mem_nhds_iff protected
end NormedSpace

namespace TopologicalSpace

-- TODO: move to Topology.Bases
theorem cover_nat_nhdsWithin {α} [TopologicalSpace α] [SecondCountableTopology α] {f : α → Set α}
    {s : Set α} (hf : ∀ x ∈ s, f x ∈ 𝓝[s] x) (hs : s.Nonempty) :
    ∃ x : ℕ → α, range x ⊆ s ∧ s ⊆ ⋃ n, f (x n) := by
  obtain ⟨t, hts, ht, hsf⟩ := TopologicalSpace.countable_cover_nhdsWithin hf
  rcases t.eq_empty_or_nonempty with rfl | hnt
  · rw [biUnion_empty, subset_empty_iff] at hsf
    exact absurd hsf hs.ne_empty
  obtain ⟨x, rfl⟩ := ht.exists_eq_range hnt
  rw [biUnion_range] at hsf
  exact ⟨x, hts, hsf⟩

open scoped Classical in
/-- A version of `TopologicalSpace.cover_nat_nhdsWithin` where `f` is only defined on `s`. -/
theorem cover_nat_nhdsWithin' {α} [TopologicalSpace α] [SecondCountableTopology α] {s : Set α}
    {f : ∀ x ∈ s, Set α} (hf : ∀ (x) (hx : x ∈ s), f x hx ∈ 𝓝[s] x) (hs : s.Nonempty) :
    ∃ (x : ℕ → α) (hx : range x ⊆ s), s ⊆ ⋃ n, f (x n) (range_subset_iff.mp hx n) := by
  let g x := if hx : x ∈ s then f x hx else ∅
  have hg : ∀ x ∈ s, g x ∈ 𝓝[s] x := fun x hx ↦ by simp_rw [g, dif_pos hx]; exact hf x hx
  obtain ⟨x, hx, h⟩ := TopologicalSpace.cover_nat_nhdsWithin hg hs
  simp_rw [g, dif_pos (range_subset_iff.mp hx _)] at h
  exact ⟨x, hx, h⟩

end TopologicalSpace

open Subtype

namespace Set

namespace Subtype

variable {α : Type*}

theorem image_coe_eq_iff_eq_univ {s : Set α} {t : Set s} : ((↑) : s → α) '' t = s ↔ t = univ := by
  convert coe_injective.image_injective.eq_iff; rw [coe_image_univ]

theorem preimage_coe_eq_univ {s t : Set α} : ((↑) : s → α) ⁻¹' t = univ ↔ s ⊆ t := by
  simp only [preimage_eq_univ_iff, range_coe_subtype, setOf_mem_eq]

end Subtype

end Set

section ParacompactSpace

-- a version of `precise_refinement_set` for open `s`.
/-- When `s : Set X` is open and paracompact, we can find a precise refinement on `s`. Note that
 in this case we only get the locally finiteness condition on `s`, which is weaker than the local
 finiteness condition on all of `X` (the collection might not be locally finite on the boundary of
 `s`). -/
theorem precise_refinement_set' {ι X : Type*} [TopologicalSpace X] {s : Set X} [ParacompactSpace s]
    (hs : IsOpen s) (u : ι → Set X) (uo : ∀ i, IsOpen (u i)) (us : s ⊆ ⋃ i, u i) :
    ∃ v : ι → Set X, (∀ i, IsOpen (v i)) ∧ (s ⊆ ⋃ i, v i) ∧
      (LocallyFinite fun i ↦ ((↑) : s → X) ⁻¹' v i) ∧ (∀ i, v i ⊆ s) ∧ ∀ i, v i ⊆ u i := by
  obtain ⟨v, vo, vs, vl, vu⟩ :=
    precise_refinement (fun i ↦ ((↑) : s → X) ⁻¹' u i)
      (fun i ↦ (uo i).preimage continuous_subtype_val)
      (by rwa [← preimage_iUnion, Subtype.preimage_coe_eq_univ])
  exact ⟨fun i ↦ (↑) '' v i, fun i ↦ hs.isOpenMap_subtype_val _ (vo i), by
      rw [← image_iUnion, vs, Subtype.coe_image_univ], by
      simp_rw [preimage_image_eq _ Subtype.coe_injective, vl], fun i ↦
      Subtype.coe_image_subset _ _, by intro i; rw [image_subset_iff]; exact vu i⟩

theorem point_finite_of_locallyFinite_coe_preimage {ι X : Type*} [TopologicalSpace X] {s : Set X}
    {f : ι → Set X} (hf : LocallyFinite fun i ↦ ((↑) : s → X) ⁻¹' f i) (hfs : ∀ i, f i ⊆ s)
    {x : X} : {i | x ∈ f i}.Finite := by
  by_cases hx : x ∈ s
  · exact hf.point_finite ⟨x, hx⟩
  · have : ∀ i, x ∉ f i := fun i hxf ↦ hx (hfs i hxf)
    simp only [this, setOf_false, finite_empty]

end ParacompactSpace

section ShrinkingLemma

variable {ι X : Type*} [TopologicalSpace X]

variable {u : ι → Set X} {s : Set X} [NormalSpace s]

-- this lemma is currently formulated a little weirdly, since we have a collection of open sets
-- as the input and a collection of closed/compact sets as output.
-- Perhaps we can formulate it so that the input is a collection of compact sets whose interiors
-- cover s.
theorem exists_subset_iUnion_interior_of_isOpen (hs : IsOpen s) (uo : ∀ i, IsOpen (u i))
    (uc : ∀ i, IsCompact (closure (u i))) (us : ∀ i, closure (u i) ⊆ s)
    (uf : ∀ x ∈ s, {i | x ∈ u i}.Finite) (uU : s ⊆ ⋃ i, u i) :
    ∃ v : ι → Set X, (s ⊆ ⋃ i, interior (v i)) ∧ (∀ i, IsCompact (v i)) ∧ ∀ i, v i ⊆ u i := by
  obtain ⟨v, vU, vo, hv⟩ :=
    exists_iUnion_eq_closure_subset
      (fun i ↦ (uo i).preimage (continuous_subtype_val : Continuous ((↑) : s → X)))
      (fun x ↦ uf x x.prop) (by simp_rw [← preimage_iUnion, Subtype.preimage_coe_eq_univ, uU])
  have : ∀ i, IsCompact (closure (((↑) : _ → X) '' v i)) := by
    intro i; refine (uc i).of_isClosed_subset isClosed_closure ?_
    apply closure_mono; rw [image_subset_iff]; exact subset_closure.trans (hv i)
  refine ⟨fun i ↦ closure ((↑) '' v i), ?_, this, ?_⟩
  · refine Subset.trans ?_
      (iUnion_mono fun i ↦ interior_maximal subset_closure (hs.isOpenMap_subtype_val _ (vo i)))
    simp_rw [← image_iUnion, vU, Subtype.coe_image_univ]; rfl
  · intro i
    have : (↑) '' v i ⊆ u i := by rintro _ ⟨x, hx, rfl⟩; exact hv i (subset_closure hx)
    intro x hx
    have hxs : x ∈ s := us i (closure_mono this hx)
    have : (⟨x, hxs⟩ : s) ∈ closure (v i) := by
      rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image (v i)]; exact hx
    exact hv i this

end ShrinkingLemma

theorem Filter.EventuallyEq.slice {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {f g : α × β → γ} {a : α} {b : β} (h : f =ᶠ[𝓝 (a, b)] g) :
    (fun y ↦ f (a, y)) =ᶠ[𝓝 b] fun y ↦ g (a, y) :=
  h.curry_nhds.self_of_nhds

theorem exists_compact_between' {α : Type*} [TopologicalSpace α] [LocallyCompactSpace α]
    {K U : Set α} (hK : IsCompact K) (hU : IsOpen U) (h_KU : K ⊆ U) :
    ∃ L, IsCompact L ∧ L ∈ 𝓝ˢ K ∧ L ⊆ U :=
  let ⟨L, L_cpct, L_in, LU⟩ := exists_compact_between hK hU h_KU
  ⟨L, L_cpct, subset_interior_iff_mem_nhdsSet.mp L_in, LU⟩
