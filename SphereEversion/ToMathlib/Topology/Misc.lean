import Mathbin.Topology.PathConnected
import Mathbin.Topology.UrysohnsLemma
import Mathbin.Topology.UniformSpace.Separation
import Mathbin.LinearAlgebra.AffineSpace.Independent
import Mathbin.Analysis.NormedSpace.FiniteDimension
import Mathbin.Topology.Algebra.Order.Floor
import Mathbin.Topology.ShrinkingLemma
import Mathbin.Topology.MetricSpace.EmetricParacompact
import Mathbin.Analysis.Convex.Normed

noncomputable section

open Set Function Filter TopologicalSpace

open scoped unitInterval Topology uniformity Filter Classical

section Maps

open Function Set

variable {α β : Type _} [TopologicalSpace α] [TopologicalSpace β] {f : α → β} {g : β → α}

theorem Function.LeftInverse.mem_preimage_iff (hfg : LeftInverse g f) {s : Set α} {x : α} :
    f x ∈ g ⁻¹' s ↔ x ∈ s := by rw [Set.mem_preimage, hfg x]

-- to set.basic
theorem Function.LeftInverse.image_eq (hfg : LeftInverse g f) (s : Set α) :
    f '' s = range f ∩ g ⁻¹' s :=
  by
  -- begin
  --   simp_rw [set.ext_iff, mem_image, mem_inter_iff, mem_range, and_comm (_ ∈ _),
  --     @eq_comm _ (f _), ← exists_and_distrib_right, ← exists_prop],
  --   simp only [hfg _, iff_true_intro iff.rfl, implies_true_iff, hfg.mem_preimage_iff] {contextual := tt},
  -- end
  ext x;
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨mem_range_self x, hfg.mem_preimage_iff.mpr hx⟩
  · rintro ⟨⟨x, rfl⟩, b⟩; exact mem_image_of_mem f (hfg.mem_preimage_iff.mp b)

theorem Function.LeftInverse.isOpenMap {f : α → β} {g : β → α} (hfg : LeftInverse g f)
    (hf : IsOpen (range f)) (hg : ContinuousOn g (range f)) : IsOpenMap f := by intro U hU;
  rw [hfg.image_eq]; exact hg.preimage_open_of_open hf hU

end Maps

section

-- to separation
theorem Filter.Eventually.closed_neighborhood {α} [TopologicalSpace α] [NormalSpace α] {C : Set α}
    {P : α → Prop} (hP : ∀ᶠ x in 𝓝ˢ C, P x) (hC : IsClosed C) :
    ∃ C' ∈ 𝓝ˢ C, IsClosed C' ∧ ∀ᶠ x in 𝓝ˢ C', P x :=
  by
  obtain ⟨O, hO, hCO, hPO⟩ := mem_nhds_set_iff_exists.mp hP
  obtain ⟨U, hU, hCU, hUO⟩ := normal_exists_closure_subset hC hO hCO
  exact
    ⟨closure U, mem_of_superset (hU.mem_nhds_set.mpr hCU) subset_closure, isClosed_closure,
      eventually_of_mem (hO.mem_nhds_set.mpr hUO) hPO⟩

end

section

variable {α β : Type _} [TopologicalSpace α] [TopologicalSpace β]

theorem ContinuousAt.eventually {f : α → β} {a₀ : α} (hf : ContinuousAt f a₀) (P : β → Prop)
    (hP : IsOpen {b | P b}) (ha₀ : P (f a₀)) : ∀ᶠ a in 𝓝 a₀, P (f a) :=
  hf (isOpen_iff_mem_nhds.mp hP _ ha₀)

theorem ContinuousAt.eventually' {f : α → β} {a₀ : α} (hf : ContinuousAt f a₀) (P : β → Prop)
    (hP : ∀ᶠ y in 𝓝 (f a₀), P y) : ∀ᶠ a in 𝓝 a₀, P (f a) :=
  by
  rw [ContinuousAt, tendsto_iff_comap] at hf 
  exact eventually.filter_mono hf (hP.comap f)

theorem Continuous.eventually {f : α → β} {a₀ : α} (hf : Continuous f) (P : β → Prop)
    (hP : IsOpen {b | P b}) (ha₀ : P (f a₀)) : ∀ᶠ a in 𝓝 a₀, P (f a) :=
  hf.ContinuousAt.Eventually P hP ha₀

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
-- (unused)
theorem nhdsSet_prod_le {s : Set α} {t : Set β} : 𝓝ˢ (s ×ˢ t) ≤ (𝓝ˢ s).Prod (𝓝ˢ t) :=
  by
  intro w hw
  obtain ⟨u, hu, v, hv, huv⟩ := mem_prod_iff.mp hw
  rw [← subset_interior_iff_mem_nhdsSet] at hu hv ⊢
  refine' (prod_mono hu hv).trans _
  rw [← interior_prod_eq]
  exact interior_mono huv

end

section

theorem support_norm {α E : Type _} [NormedAddCommGroup E] (f : α → E) :
    (support fun a => ‖f a‖) = support f :=
  Function.support_comp_eq norm (fun x => norm_eq_zero) f

@[to_additive]
theorem hasCompactMulSupport_of_subset {α β : Type _} [TopologicalSpace α] [T2Space α] [One β]
    {f : α → β} {K : Set α} (hK : IsCompact K) (hf : mulSupport f ⊆ K) : HasCompactMulSupport f :=
  isCompact_of_isClosed_subset hK (isClosed_mulTSupport f) (closure_minimal hf hK.IsClosed)

theorem periodic_const {α β : Type _} [Add α] {a : α} {b : β} : Periodic (fun x => b) a := fun x =>
  rfl

theorem Real.ball_zero_eq (r : ℝ) : Metric.ball (0 : ℝ) r = Ioo (-r) r := by simp [Real.ball_eq_Ioo]

end

section

/-! ## The standard ℤ action on ℝ is properly discontinuous

TODO: use that in to_mathlib.topology.periodic?
-/


instance : VAdd ℤ ℝ :=
  ⟨fun n x => (n : ℝ) + x⟩

instance : ProperlyDiscontinuousVAdd ℤ ℝ :=
  ⟨by
    intro K L hK hL
    rcases eq_empty_or_nonempty K with (rfl | hK') <;>
        rcases eq_empty_or_nonempty L with (rfl | hL') <;>
      try simp
    have hSK := (hK.is_lub_Sup hK').1
    have hIK := (hK.is_glb_Inf hK').1
    have hSL := (hL.is_lub_Sup hL').1
    have hIL := (hL.is_glb_Inf hL').1
    apply (finite_Icc ⌈Inf L - Sup K⌉ ⌊Sup L - Inf K⌋).Subset
    rintro n (hn : VAdd.vadd n '' K ∩ L ≠ ∅)
    rcases nonempty_iff_ne_empty.mpr hn with ⟨l, ⟨k, hk, rfl⟩, hnk : (n : ℝ) + k ∈ L⟩
    constructor
    · rw [Int.ceil_le]
      linarith [hIL hnk, hSK hk]
    · rw [Int.le_floor]
      linarith [hSL hnk, hIK hk]⟩

end

section Fract

open Int

/- properties of the (dis)continuity of `int.fract` on `ℝ`.
To be PRed to topology.algebra.floor_ring
-/
theorem floor_eq_self_iff {x : ℝ} : (⌊x⌋ : ℝ) = x ↔ ∃ n : ℤ, x = n :=
  by
  constructor
  · intro h
    exact ⟨⌊x⌋, h.symm⟩
  · rintro ⟨n, rfl⟩
    rw [floor_int_cast]

theorem fract_eq_zero_iff {x : ℝ} : fract x = 0 ↔ ∃ n : ℤ, x = n := by
  rw [fract, sub_eq_zero, eq_comm, floor_eq_self_iff]

theorem fract_ne_zero_iff {x : ℝ} : fract x ≠ 0 ↔ ∀ n : ℤ, x ≠ n := by
  rw [← not_exists, not_iff_not, fract_eq_zero_iff]

theorem Ioo_floor_mem_nhds {x : ℝ} (h : ∀ n : ℤ, x ≠ n) : Ioo (⌊x⌋ : ℝ) (⌊x⌋ + 1 : ℝ) ∈ 𝓝 x :=
  Ioo_mem_nhds ((floor_le x).eq_or_lt.elim (fun H => (h ⌊x⌋ H.symm).elim) id) (lt_floor_add_one x)

theorem loc_constant_floor {x : ℝ} (h : ∀ n : ℤ, x ≠ n) : floor =ᶠ[𝓝 x] fun x' => ⌊x⌋ :=
  by
  filter_upwards [Ioo_floor_mem_nhds h]
  intro y hy
  rw [floor_eq_on_Ico]
  exact mem_Ico_of_Ioo hy

theorem fract_eventuallyEq {x : ℝ} (h : fract x ≠ 0) : fract =ᶠ[𝓝 x] fun x' => x' - floor x :=
  by
  rw [fract_ne_zero_iff] at h 
  exact eventually_eq.rfl.sub ((loc_constant_floor h).fun_comp _)

#print continuousAt_fract /-
-- todo: make iff
theorem continuousAt_fract {x : ℝ} (h : fract x ≠ 0) : ContinuousAt fract x :=
  (continuousAt_id.sub continuousAt_const).congr (fract_eventuallyEq h).symm
-/

theorem Ioo_inter_Iio {α : Type _} [LinearOrder α] {a b c : α} :
    Ioo a b ∩ Iio c = Ioo a (min b c) := by ext; simp [and_assoc']

theorem fract_lt {x y : ℝ} {n : ℤ} (h1 : (n : ℝ) ≤ x) (h2 : x < n + y) : fract x < y :=
  by
  cases' le_total y 1 with hy hy
  · rw [← fract_sub_int x n, fract_eq_self.mpr]
    linarith
    constructor <;> linarith
  · exact (fract_lt_one x).trans_le hy

theorem one_sub_lt_fract {x y : ℝ} {n : ℤ} (hy : y ≤ 1) (h1 : (n : ℝ) - y < x) (h2 : x < n) :
    1 - y < fract x := by
  have I₁ : 1 - y < x - (n - 1) := by linarith
  have I₂ : x - (n - 1) < 1 := by linarith
  norm_cast at I₁ I₂ 
  rw [← fract_sub_int x (n - 1), fract_eq_self.mpr]
  exact I₁
  constructor <;> linarith

theorem IsOpen.preimage_fract' {s : Set ℝ} (hs : IsOpen s) (h2s : 0 ∈ s → s ∈ 𝓝[<] (1 : ℝ)) :
    IsOpen (fract ⁻¹' s) := by
  rw [isOpen_iff_mem_nhds]
  rintro x (hx : fract x ∈ s)
  rcases eq_or_ne (fract x) 0 with (hx' | hx')
  · have H : (0 : ℝ) ∈ s := by rwa [hx'] at hx 
    specialize h2s H
    rcases fract_eq_zero_iff.mp hx' with ⟨n, rfl⟩; clear hx hx'
    have s_mem_0 := hs.mem_nhds H
    rcases(nhds_basis_zero_abs_sub_lt ℝ).mem_iff.mp s_mem_0 with ⟨δ, δ_pos, hδ⟩
    rcases(nhdsWithin_hasBasis (nhds_basis_Ioo_pos (1 : ℝ)) _).mem_iff.mp h2s with ⟨ε, ε_pos, hε⟩
    rw [Ioo_inter_Iio, min_eq_right (le_add_of_nonneg_right ε_pos.le)] at hε 
    set ε' := min ε (1 / 2)
    have ε'_pos : 0 < ε' := lt_min ε_pos (by norm_num : (0 : ℝ) < 1 / 2)
    have hε' : Ioo (1 - ε') 1 ⊆ s := by
      apply subset.trans _ hε
      apply Ioo_subset_Ioo_left
      linarith [min_le_left ε (1 / 2)]
    have mem : Ioo ((n : ℝ) - ε') (n + δ) ∈ 𝓝 (n : ℝ) := by apply Ioo_mem_nhds <;> linarith
    apply mem_of_superset mem
    rintro x ⟨hx, hx'⟩
    cases' le_or_gt (n : ℝ) x with hx'' hx''
    · apply hδ
      rw [mem_set_of_eq, abs_eq_self.mpr (fract_nonneg x)]
      exact fract_lt hx'' hx'
    · apply hε'
      constructor
      · refine' one_sub_lt_fract (by linarith [min_le_right ε (1 / 2)]) (by linarith) hx''
      · exact fract_lt_one x
  · rw [fract_ne_zero_iff] at hx' 
    have H : Ico (⌊x⌋ : ℝ) (⌊x⌋ + 1) ∈ 𝓝 x :=
      mem_of_superset (Ioo_floor_mem_nhds hx') Ioo_subset_Ico_self
    exact (continuousOn_fract ⌊x⌋).ContinuousAt H (hs.mem_nhds hx)

theorem IsOpen.preimage_fract {s : Set ℝ} (hs : IsOpen s) (h2s : (0 : ℝ) ∈ s → (1 : ℝ) ∈ s) :
    IsOpen (fract ⁻¹' s) :=
  hs.preimage_fract' fun h => nhdsWithin_le_nhds <| hs.mem_nhds (h2s h)

-- is `sᶜ ∉ 𝓝[<] (1 : ℝ)` equivalent to something like `cluster_pt (𝓝[Iio (1 : ℝ) ∩ s] (1 : ℝ)` ?
theorem IsClosed.preimage_fract {s : Set ℝ} (hs : IsClosed s)
    (h2s : sᶜ ∉ 𝓝[<] (1 : ℝ) → (0 : ℝ) ∈ s) : IsClosed (fract ⁻¹' s) :=
  isOpen_compl_iff.mp <| hs.isOpen_compl.preimage_fract' fun h => by_contra fun h' => h <| h2s h'

theorem fract_preimage_mem_nhds {s : Set ℝ} {x : ℝ} (h1 : s ∈ 𝓝 (fract x))
    (h2 : fract x = 0 → s ∈ 𝓝 (1 : ℝ)) : fract ⁻¹' s ∈ 𝓝 x :=
  by
  by_cases hx : fract x = 0
  · obtain ⟨u, hus, hu, hxu⟩ := mem_nhds_iff.mp h1
    obtain ⟨v, hvs, hv, h1v⟩ := mem_nhds_iff.mp (h2 hx)
    rw [mem_nhds_iff]
    refine'
      ⟨fract ⁻¹' (u ∪ v), preimage_mono (union_subset hus hvs),
        (hu.union hv).preimage_fract fun _ => subset_union_right _ _ h1v, subset_union_left _ _ hxu⟩
  · exact (continuousAt_fract hx).preimage_mem_nhds h1

end Fract

section

-- to normed_space
variable {E F : Type _} [NormedAddCommGroup E] [NormedAddCommGroup F]

variable [NormedSpace ℝ E] [NormedSpace ℝ F]

theorem dist_smul_add_one_sub_smul_le {r : ℝ} {x y : E} (h : r ∈ I) :
    dist (r • x + (1 - r) • y) x ≤ dist y x :=
  calc
    dist (r • x + (1 - r) • y) x = ‖1 - r‖ * ‖x - y‖ := by
      simp_rw [dist_eq_norm', ← norm_smul, sub_smul, one_smul, smul_sub, ← sub_sub, ← sub_add,
        sub_right_comm]
    _ = (1 - r) * dist y x := by
      rw [Real.norm_eq_abs, abs_eq_self.mpr (sub_nonneg.mpr h.2), dist_eq_norm']
    _ ≤ (1 - 0) * dist y x := (mul_le_mul_of_nonneg_right (sub_le_sub_left h.1 _) dist_nonneg)
    _ = dist y x := by rw [sub_zero, one_mul]

end

section

-- to ???
-- needs classical
variable {α β γ δ ι : Type _} [TopologicalSpace α] [TopologicalSpace β] {x : α}

theorem isOpen_slice_of_isOpen_over {Ω : Set (α × β)} {x₀ : α}
    (hΩ_op : ∃ U ∈ 𝓝 x₀, IsOpen (Ω ∩ Prod.fst ⁻¹' U)) : IsOpen (Prod.mk x₀ ⁻¹' Ω) :=
  by
  rcases hΩ_op with ⟨U, hU, hU_op⟩; convert hU_op.preimage (Continuous.Prod.mk x₀) using 1
  simp_rw [preimage_inter, preimage_preimage, preimage_const, mem_of_mem_nhds hU, if_pos,
    inter_univ]

end

section projI

variable {α β : Type _} [LinearOrderedSemiring α] {x c : α}

/-- If `α` is a `linear_ordered_semiring`, then `proj_I : α → α` projection of `α` onto the unit
interval `[0, 1]`. -/
def projI : α → α := fun x => projIcc (0 : α) 1 zero_le_one x

theorem projI_def : projI x = max 0 (min 1 x) :=
  rfl

theorem projIcc_eq_projI : (projIcc (0 : α) 1 zero_le_one x : α) = projI x :=
  rfl

theorem projI_of_le_zero (hx : x ≤ 0) : projI x = 0 :=
  congr_arg coe <| projIcc_of_le_left _ hx

@[simp]
theorem projI_zero : projI (0 : α) = 0 :=
  congr_arg coe <| projIcc_left _

theorem projI_of_one_le (hx : 1 ≤ x) : projI x = 1 :=
  congr_arg coe <| projIcc_of_right_le _ hx

@[simp]
theorem projI_one : projI (1 : α) = 1 :=
  congr_arg coe <| projIcc_right _

@[simp]
theorem projI_eq_zero [Nontrivial α] : projI x = 0 ↔ x ≤ 0 := by
  rw [← proj_Icc_eq_left (zero_lt_one' α), Subtype.ext_iff]; rfl

@[simp]
theorem projI_eq_one : projI x = 1 ↔ 1 ≤ x := by
  rw [← proj_Icc_eq_right (zero_lt_one' α), Subtype.ext_iff]; rfl

theorem projI_mem_Icc : projI x ∈ Icc (0 : α) 1 :=
  (projIcc (0 : α) 1 zero_le_one x).Prop

theorem projI_eq_self : projI x = x ↔ x ∈ Icc (0 : α) 1 :=
  ⟨fun h => h ▸ projI_mem_Icc, fun h => congr_arg coe <| projIcc_of_mem _ h⟩

@[simp]
theorem projI_projI : projI (projI x) = projI x :=
  projI_eq_self.mpr projI_mem_Icc

@[simp]
theorem projIcc_projI : projIcc (0 : α) 1 zero_le_one (projI x) = projIcc 0 1 zero_le_one x :=
  projIcc_of_mem _ projI_mem_Icc

@[simp]
theorem range_projI : range projI = Icc 0 1 := by
  rw [projI, range_comp, range_proj_Icc, image_univ, Subtype.range_coe]

theorem monotone_projI : Monotone (projI : α → α) :=
  monotone_projIcc _

theorem strictMonoOn_projI : StrictMonoOn projI (Icc (0 : α) 1) :=
  strictMonoOn_projIcc _

theorem projI_le_max : projI x ≤ max 0 x :=
  max_le_max le_rfl <| min_le_right _ _

theorem min_le_projI : min 1 x ≤ projI x :=
  le_max_right _ _

theorem projI_le_iff : projI x ≤ c ↔ 0 ≤ c ∧ (1 ≤ c ∨ x ≤ c) := by
  simp_rw [projI_def, max_le_iff, min_le_iff]

@[simp]
theorem projI_eq_min : projI x = min 1 x ↔ 0 ≤ x := by
  simp_rw [projI_def, max_eq_right_iff, le_min_iff, zero_le_one, true_and_iff]

theorem min_projI (h2 : 0 ≤ c) : min c (projI x) = projI (min c x) :=
  by
  cases' le_total c x with h3 h3 <;> simp [h2, h3, projI_le_iff, proj_I_eq_min.mpr]
  simp [proj_I_eq_min.mpr, h2.trans h3, min_left_comm c, h3]

theorem continuous_projI [TopologicalSpace α] [OrderTopology α] : Continuous (projI : α → α) :=
  continuous_projIcc.subtype_val

theorem projI_mapsto {α : Type _} [LinearOrderedSemiring α] {s : Set α} (h0s : (0 : α) ∈ s)
    (h1s : (1 : α) ∈ s) : MapsTo projI s s := fun x hx =>
  (le_total 1 x).elim (fun h2x => by rwa [proj_I_eq_one.mpr h2x]) fun h2x =>
    (le_total 0 x).elim (fun h3x => by rwa [proj_I_eq_self.mpr ⟨h3x, h2x⟩]) fun h3x => by
      rwa [proj_I_eq_zero.mpr h3x]

-- about path.truncate
theorem truncate_projI_right {X : Type _} [TopologicalSpace X] {a b : X} (γ : Path a b) (t₀ t₁ : ℝ)
    (s : I) : γ.truncate t₀ (projI t₁) s = γ.truncate t₀ t₁ s :=
  by
  simp_rw [Path.truncate, Path.coe_mk_mk, Path.extend, Icc_extend, Function.comp]
  rw [min_projI (s.prop.1.trans <| le_max_left _ _), projIcc_projI]

end projI

section

open Encodable Option

variable {α β γ : Type _} [TopologicalSpace α] [TopologicalSpace β]

-- can we restate this nicely?
/-- Given a locally finite sequence of sets indexed by an encodable type, we can naturally reindex
  this sequence to get a sequence indexed by `ℕ` (by adding some `∅` values).
  This new sequence is still locally finite. -/
theorem decode₂_locallyFinite {ι} [Encodable ι] {s : ι → Set α} (hs : LocallyFinite s) :
    LocallyFinite fun i => (s <$> decode₂ ι i).getD ∅ :=
  by
  intro x
  obtain ⟨U, hxU, hU⟩ := hs x
  refine' ⟨U, hxU, _⟩
  have :
    encode ⁻¹' {i : ℕ | ((s <$> decode₂ ι i).getD ∅ ∩ U).Nonempty} = {i : ι | (s i ∩ U).Nonempty} :=
    by simp_rw [preimage_set_of_eq, decode₂_encode, map_some, get_or_else_some]
  rw [← this] at hU 
  refine' finite_of_finite_preimage hU _
  intro n hn
  rw [← decode₂_ne_none_iff]
  intro h
  simp_rw [mem_set_of_eq, h, map_none, get_or_else_none, empty_inter] at hn 
  exact (not_nonempty_empty hn).elim

open TopologicalSpace

variable {X : Type _} [EMetricSpace X] [LocallyCompactSpace X] [SecondCountableTopology X]

theorem exists_locallyFinite_subcover_of_locally {C : Set X} (hC : IsClosed C) {P : Set X → Prop}
    (hP : Antitone P) (h0 : P ∅) (hX : ∀ x ∈ C, ∃ V ∈ 𝓝 (x : X), P V) :
    ∃ (K : ℕ → Set X) (W : ℕ → Set X),
      (∀ n, IsCompact (K n)) ∧
        (∀ n, IsOpen (W n)) ∧ (∀ n, P (W n)) ∧ (∀ n, K n ⊆ W n) ∧ LocallyFinite W ∧ C ⊆ ⋃ n, K n :=
  by
  choose V' hV' hPV' using set_coe.forall'.mp hX
  choose V hV hVV' hcV using fun x : C => LocallyCompactSpace.local_compact_nhds (↑x) (V' x) (hV' x)
  simp_rw [← mem_interior_iff_mem_nhds] at hV 
  have : C ⊆ ⋃ x : C, interior (V x) := fun x hx => by rw [mem_Union]; exact ⟨⟨x, hx⟩, hV _⟩
  obtain ⟨s, hs, hsW₂⟩ := is_open_Union_countable (fun x => interior (V x)) fun x => isOpen_interior
  rw [← hsW₂, bUnion_eq_Union] at this ; clear hsW₂
  obtain ⟨W, hW, hUW, hlW, hWV⟩ :=
    precise_refinement_set hC (fun x : s => interior (V x)) (fun x => isOpen_interior) this
  obtain ⟨K, hCK, hK, hKW⟩ :=
    exists_subset_iUnion_closed_subset hC (fun x : s => hW x) (fun x _ => hlW.point_finite x) hUW
  haveI : Encodable s := hs.to_encodable
  let K' : ℕ → Set X := fun n => (K <$> decode₂ s n).getD ∅
  let W' : ℕ → Set X := fun n => (W <$> decode₂ s n).getD ∅
  refine' ⟨K', W', _, _, _, _, _, _⟩
  · intro n; cases' h : decode₂ s n with i
    · simp_rw [K', h, map_none, get_or_else_none, isCompact_empty]
    · simp_rw [K', h, map_some, get_or_else_some]
      exact
        isCompact_of_isClosed_subset (hcV i) (hK i) ((hKW i).trans <| (hWV i).trans interior_subset)
  · intro n; cases h : decode₂ s n
    · simp_rw [W', h, map_none, get_or_else_none, isOpen_empty]
    · simp_rw [W', h, map_some, get_or_else_some, hW]
  · intro n; cases' h : decode₂ s n with i
    · simp_rw [W', h, map_none, get_or_else_none, h0]
    · simp_rw [W', h, map_some, get_or_else_some]; refine' hP _ (hPV' i)
      refine' (hWV i).trans (interior_subset.trans <| hVV' i)
  · intro n; cases h : decode₂ s n
    · simp_rw [K', W', h, map_none]
    · simp_rw [K', W', h, map_some, get_or_else_some, hKW]
  · exact decode₂_locallyFinite hlW
  · intro x hx; obtain ⟨i, hi⟩ := mem_Union.mp (hCK hx)
    refine' mem_Union.mpr ⟨encode i, _⟩
    simp_rw [K', decode₂_encode, map_some, get_or_else_some, hi]

end

section

-- to subset_properties
variable {α β γ : Type _} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

theorem IsCompact.eventually_forall_mem {x₀ : α} {K : Set β} (hK : IsCompact K) {f : α → β → γ}
    (hf : Continuous ↿f) {U : Set γ} (hU : ∀ y ∈ K, U ∈ 𝓝 (f x₀ y)) :
    ∀ᶠ x in 𝓝 x₀, ∀ y ∈ K, f x y ∈ U :=
  hK.eventually_forall_of_forall_eventually fun y hy =>
    (hf.Tendsto _).Eventually <| show U ∈ 𝓝 ((↿f) (x₀, y)) from hU y hy

end

section

-- to separation
variable {α : Type _} [TopologicalSpace α]

/-
needs
import linear_algebra.affine_space.independent
import analysis.normed_space.finite_dimension
-/
theorem isOpen_affineIndependent (𝕜 E : Type _) {ι : Type _} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace 𝕜] [Finite ι] :
    IsOpen {p : ι → E | AffineIndependent 𝕜 p} := by
  classical
  cases isEmpty_or_nonempty ι
  · skip; exact isOpen_discrete _
  obtain ⟨i₀⟩ := h
  simp_rw [affineIndependent_iff_linearIndependent_vsub 𝕜 _ i₀]
  let ι' := { x // x ≠ i₀ }
  cases nonempty_fintype ι
  haveI : Fintype ι' := Subtype.fintype _
  convert_to
    IsOpen ((fun (p : ι → E) (i : ι') => p i -ᵥ p i₀) ⁻¹' {p : ι' → E | LinearIndependent 𝕜 p})
  refine' IsOpen.preimage _ isOpen_setOf_linearIndependent
  refine' continuous_pi fun i' => Continuous.vsub (continuous_apply i') <| continuous_apply i₀

end

section

open Metric

theorem Continuous.infDist {α β : Type _} [TopologicalSpace α] [PseudoMetricSpace β] {s : Set β}
    {f : α → β} (hf : Continuous f) : Continuous fun x => infDist (f x) s :=
  (continuous_infDist_pt _).comp hf

end

section NormedSpace

open Metric

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem isPreconnected_ball (x : E) (r : ℝ) : IsPreconnected (ball x r) :=
  (convex_ball x r).IsPreconnected

theorem isConnected_ball {x : E} {r : ℝ} : IsConnected (ball x r) ↔ 0 < r := by
  simp [IsConnected, isPreconnected_ball]

-- todo: make metric.mem_nhds_iff protected
end NormedSpace

section connectedComponentIn

variable {α β : Type _} [TopologicalSpace α] [TopologicalSpace β]

theorem Continuous.image_connectedComponentIn_subset {f : α → β} {s : Set α} {x : α}
    (hf : Continuous f) (hx : x ∈ s) :
    f '' connectedComponentIn s x ⊆ connectedComponentIn (f '' s) (f x) :=
  (isPreconnected_connectedComponentIn.image _ hf.ContinuousOn).subset_connectedComponentIn
    (mem_image_of_mem _ <| mem_connectedComponentIn hx)
    (image_subset _ <| connectedComponentIn_subset _ _)

theorem Homeomorph.image_connectedComponentIn (f : α ≃ₜ β) {s : Set α} {x : α} (hx : x ∈ s) :
    f '' connectedComponentIn s x = connectedComponentIn (f '' s) (f x) :=
  by
  refine' (f.continuous.image_connected_component_in_subset hx).antisymm _
  have := f.symm.continuous.image_connected_component_in_subset (mem_image_of_mem _ hx)
  rwa [image_subset_iff, f.preimage_symm, f.image_symm, f.preimage_image, f.symm_apply_apply] at
    this 

end connectedComponentIn

namespace TopologicalSpace

-- to topology.bases
theorem cover_nat_nhdsWithin {α} [TopologicalSpace α] [SecondCountableTopology α] {f : α → Set α}
    {s : Set α} (hf : ∀ x ∈ s, f x ∈ 𝓝[s] x) (hs : s.Nonempty) :
    ∃ x : ℕ → α, range x ⊆ s ∧ s ⊆ ⋃ n, f (x n) :=
  by
  obtain ⟨t, hts, ht, hsf⟩ := TopologicalSpace.countable_cover_nhdsWithin hf
  have hnt : t.nonempty := by
    by_contra
    rw [not_nonempty_iff_eq_empty] at h 
    rw [h, bUnion_empty, subset_empty_iff] at hsf 
    exact hs.ne_empty hsf
  obtain ⟨x, rfl⟩ := ht.exists_eq_range hnt
  rw [bUnion_range] at hsf 
  exact ⟨x, hts, hsf⟩

/-- A version of `topological_space.cover_nat_nhds_within` where `f` is only defined on `s`. -/
theorem cover_nat_nhds_within' {α} [TopologicalSpace α] [SecondCountableTopology α] {s : Set α}
    {f : ∀ x ∈ s, Set α} (hf : ∀ (x) (hx : x ∈ s), f x hx ∈ 𝓝[s] x) (hs : s.Nonempty) :
    ∃ (x : ℕ → α) (hx : range x ⊆ s), s ⊆ ⋃ n, f (x n) (range_subset_iff.mp hx n) :=
  by
  let g x := if hx : x ∈ s then f x hx else ∅
  have hg : ∀ x ∈ s, g x ∈ 𝓝[s] x := by intro x hx; simp_rw [g, dif_pos hx]; exact hf x hx
  obtain ⟨x, hx, h⟩ := TopologicalSpace.cover_nat_nhdsWithin hg hs
  simp_rw [g, dif_pos (range_subset_iff.mp hx _)] at h 
  refine' ⟨x, hx, h⟩

end TopologicalSpace

namespace Set

namespace Subtype

open _Root_.Subtype

variable {α : Type _}

theorem image_coe_eq_iff_eq_univ {s : Set α} {t : Set s} : (coe : s → α) '' t = s ↔ t = univ := by
  convert coe_injective.image_injective.eq_iff; rw [coe_image_univ]

@[simp]
theorem preimage_coe_eq_univ {s t : Set α} : (coe : s → α) ⁻¹' t = univ ↔ s ⊆ t := by
  rw [← inter_eq_right_iff_subset, ← image_preimage_coe, image_coe_eq_iff_eq_univ]

end Subtype

end Set

open Set

section ParacompactSpace

-- a version of `precise_refinement_set` for open `s`.
/-- When `s : set X` is open and paracompact, we can find a precise refinement on `s`. Note that
 in this case we only get the locally finiteness condition on `s`, which is weaker than the local
 finiteness condition on all of `X` (the collection might not be locally finite on the boundary of
 `s`). -/
theorem precise_refinement_set' {ι X : Type _} [TopologicalSpace X] {s : Set X} [ParacompactSpace s]
    (hs : IsOpen s) (u : ι → Set X) (uo : ∀ i, IsOpen (u i)) (us : s ⊆ ⋃ i, u i) :
    ∃ v : ι → Set X,
      (∀ i, IsOpen (v i)) ∧
        (s ⊆ ⋃ i, v i) ∧
          (LocallyFinite fun i => (coe : s → X) ⁻¹' v i) ∧ (∀ i, v i ⊆ s) ∧ ∀ i, v i ⊆ u i :=
  by
  obtain ⟨v, vo, vs, vl, vu⟩ :=
    precise_refinement (fun i => (coe : s → X) ⁻¹' u i)
      (fun i => (uo i).Preimage continuous_subtype_val)
      (by rwa [← preimage_Union, subtype.preimage_coe_eq_univ])
  refine'
    ⟨fun i => coe '' v i, fun i => hs.is_open_map_subtype_coe _ (vo i), by
      rw [← image_Union, vs, Subtype.coe_image_univ], by
      simp_rw [preimage_image_eq _ Subtype.coe_injective, vl], fun i =>
      Subtype.coe_image_subset _ _, by intro i; rw [image_subset_iff]; exact vu i⟩

theorem point_finite_of_locallyFinite_coe_preimage {ι X : Type _} [TopologicalSpace X] {s : Set X}
    {f : ι → Set X} (hf : LocallyFinite fun i => (coe : s → X) ⁻¹' f i) (hfs : ∀ i, f i ⊆ s)
    {x : X} : {i | x ∈ f i}.Finite := by
  by_cases hx : x ∈ s
  · exact hf.point_finite ⟨x, hx⟩
  · have : ∀ i, x ∉ f i := fun i hxf => hx (hfs i hxf)
    simp only [this, set_of_false, finite_empty]

end ParacompactSpace

section ShrinkingLemma

variable {ι X : Type _} [TopologicalSpace X]

variable {u : ι → Set X} {s : Set X} [NormalSpace s]

-- this lemma is currently formulated a little weirdly, since we have a collection of open sets
-- as the input and a collection of closed/compact sets as output.
-- Perhaps we can formulate it so that the input is a collection of compact sets whose interiors
-- cover s.
theorem exists_subset_iUnion_interior_of_isOpen (hs : IsOpen s) (uo : ∀ i, IsOpen (u i))
    (uc : ∀ i, IsCompact (closure (u i))) (us : ∀ i, closure (u i) ⊆ s)
    (uf : ∀ x ∈ s, {i | x ∈ u i}.Finite) (uU : s ⊆ ⋃ i, u i) :
    ∃ v : ι → Set X, (s ⊆ ⋃ i, interior (v i)) ∧ (∀ i, IsCompact (v i)) ∧ ∀ i, v i ⊆ u i :=
  by
  obtain ⟨v, vU, vo, hv⟩ :=
    exists_iUnion_eq_closure_subset
      (fun i => (uo i).Preimage (continuous_subtype_val : Continuous (coe : s → X)))
      (fun x => uf x x.Prop) (by simp_rw [← preimage_Union, subtype.preimage_coe_eq_univ, uU])
  have : ∀ i, IsCompact (closure ((coe : _ → X) '' v i)) :=
    by
    intro i; refine' isCompact_of_isClosed_subset (uc i) isClosed_closure _
    apply closure_mono; rw [image_subset_iff]; refine' subset_closure.trans (hv i)
  refine' ⟨fun i => closure (coe '' v i), _, this, _⟩
  · refine'
      subset.trans _
        (Union_mono fun i => interior_maximal subset_closure (hs.is_open_map_subtype_coe _ (vo i)))
    simp_rw [← image_Union, vU, Subtype.coe_image_univ]
  · intro i
    have : coe '' v i ⊆ u i := by rintro _ ⟨x, hx, rfl⟩; exact hv i (subset_closure hx)
    intro x hx
    have hxs : x ∈ s := us i (closure_mono this hx)
    have : (⟨x, hxs⟩ : s) ∈ closure (v i) := by
      rw [embedding_subtype_coe.closure_eq_preimage_closure_image (v i)]; exact hx
    exact hv i this

end ShrinkingLemma

open scoped Filter

theorem Filter.EventuallyEq.slice {α β γ : Type _} [TopologicalSpace α] [TopologicalSpace β]
    {f g : α × β → γ} {a : α} {b : β} (h : f =ᶠ[𝓝 (a, b)] g) :
    (fun y => f (a, y)) =ᶠ[𝓝 b] fun y => g (a, y) :=
  h.curry_nhds.self_of_nhds

theorem exists_compact_between' {α : Type _} [TopologicalSpace α] [LocallyCompactSpace α]
    {K U : Set α} (hK : IsCompact K) (hU : IsOpen U) (h_KU : K ⊆ U) :
    ∃ L, IsCompact L ∧ L ∈ 𝓝ˢ K ∧ L ⊆ U :=
  let ⟨L, L_cpct, L_in, LU⟩ := exists_compact_between hK hU h_KU
  ⟨L, L_cpct, subset_interior_iff_mem_nhdsSet.mp L_in, LU⟩

section

-- to topology/basic
@[simp]
theorem Finset.isClosed_bUnion {α} [TopologicalSpace α] {ι : Type _} (s : Finset ι) (f : ι → Set α)
    (hf : ∀ i ∈ s, IsClosed (f i)) : IsClosed (⋃ i ∈ s, f i) :=
  isClosed_biUnion s.finite_toSet hf

end

