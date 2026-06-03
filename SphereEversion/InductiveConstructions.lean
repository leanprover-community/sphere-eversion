import Mathlib.Topology.Germ
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.RCLike.Basic
import SphereEversion.ToMathlib.Topology.Misc
import SphereEversion.Indexing
import SphereEversion.Notations

-- set_option trace.filter_inst_type true

open Set Filter Function
open scoped Topology unitInterval

/-!
Notes by Patrick:

The goal of this file is to explore how to prove `exists_surrounding_loops` and the local to global
inductive homotopy construction in a way that uncouples the general
topological argument from the things specific to loops or homotopies of jet sections.

First there is a lemma `inductive_construction` which abstracts the locally ultimately constant
arguments, assuming we work with a fixed covering. It builds on
`LocallyFinite.exists_forall_eventually_of_indexType`.

From `inductive_construction` alone we deduce `inductive_htpy_construction` which builds a homotopy
in a similar context. This is meant to be used to go from Chapter 2 to Chapter 3.

Combining `inductive_construction` with an argument using local existence and exhaustions, we
get `inductive_construction_of_loc` building a function from local existence and patching
assumptions. It also has a version `relative_inductive_construction_of_loc` which does this
relative to a closed set. This is used for `exists_surrounding_loops`.

This file also contains supporting lemmas about `IndexType`. A short term goal will be to
get rid of the `indexing` abstraction and do everything in terms of `IndexType`, unless
`indexing` makes those supporting lemmas really cleaner to prove.
-/


section inductive_construction

theorem LocallyFinite.exists_forall_eventually_of_indexType {α X : Type*} [TopologicalSpace X]
    {N : ℕ} {f : IndexType N → X → α} {V : IndexType N → Set X} (hV : LocallyFinite V)
    (h : ∀ n : IndexType N, ¬IsMax n → ∀ x ∉ (V n.succ), f n.succ x = f n x) :
    ∃ F : X → α, ∀ x : X, ∀ᶠ n in Filter.atTop, f n =ᶠ[𝓝 x] F := by
  choose U hUx hU using hV
  choose i₀ hi₀ using fun x ↦ (hU x).bddAbove
  have key : ∀ {x} {n}, n ≥ i₀ x → ∀ {y}, y ∈ U x → f n y = f (i₀ x) y := fun {x} ↦ by
    refine @IndexType.induction_from N (fun i ↦ ∀ {y}, y ∈ U x → f i y = f (i₀ x) y) _ ?_ ?_
    · exact fun _ ↦ rfl
    · intro i hi h'i ih y hy
      rw [h i h'i, ih hy]
      intro h'y
      replace hi₀ := mem_upperBounds.mp (hi₀ x) i.succ ⟨y, h'y, hy⟩
      exact lt_irrefl _ (((i.lt_succ h'i).trans_le hi₀).trans_le hi)
  refine ⟨fun x ↦ f (i₀ x) x, fun x ↦ ?_⟩
  refine (eventually_ge_atTop (i₀ x)).mono fun n hn ↦ ?_
  refine mem_of_superset (hUx x) fun y hy ↦ ?_
  calc
    f n y = f (i₀ x) y := key hn hy
    _ = f (max (i₀ x) (i₀ y)) y := (key (le_max_left ..) hy).symm
    _ = f (i₀ y) y := key (le_max_right ..) (mem_of_mem_nhds <| hUx y)

@[inherit_doc] local notation "𝓘" => IndexType

theorem inductive_construction {X Y : Type*} [TopologicalSpace X] {N : ℕ} {U : IndexType N → Set X}
    (P₀ : ∀ x : X, Germ (𝓝 x) Y → Prop) (P₁ : ∀ _i : IndexType N, ∀ x : X, Germ (𝓝 x) Y → Prop)
    (P₂ : IndexType N → (X → Y) → Prop) (U_fin : LocallyFinite U)
    (init : ∃ f : X → Y, (∀ x, P₀ x f) ∧ P₂ 0 f)
    (ind : ∀ (i : IndexType N) (f : X → Y), (∀ x, P₀ x f) → P₂ i f → (∀ j < i, ∀ x, P₁ j x f) →
      ∃ f' : X → Y, (∀ x, P₀ x f') ∧ (¬IsMax i → P₂ i.succ f') ∧ (∀ j ≤ i, ∀ x, P₁ j x f') ∧
        ∀ x ∉ U i, f' x = f x) :
    ∃ f : X → Y, (∀ x, P₀ x f) ∧ ∀ j, ∀ x, P₁ j x f := by
  let P : 𝓘 N → (X → Y) → Prop := fun n f ↦
    (∀ x, P₀ x f) ∧ (¬IsMax n → P₂ n.succ f) ∧ ∀ j ≤ n, ∀ x, P₁ j x f
  let Q : 𝓘 N → (X → Y) → (X → Y) → Prop := fun n f f' ↦ ∀ x ∉ (U n.succ), f' x = f x
  obtain ⟨f, hf⟩ : ∃ f : 𝓘 N → X → Y, ∀ n, P n (f n) ∧ (¬IsMax n → Q n (f n) (f n.succ)) := by
    apply IndexType.exists_by_induction
    · rcases init with ⟨f₀, h₀f₀, h₁f₀⟩
      rcases ind 0 f₀ h₀f₀ h₁f₀ (by simp [IndexType.not_lt_zero]) with ⟨f', h₀f', h₂f', h₁f', -⟩
      exact ⟨f', h₀f', h₂f', h₁f'⟩
    · rintro n f ⟨h₀f, h₂f, h₁f⟩ hn
      rcases ind _ f h₀f (h₂f hn) fun j hj ↦ h₁f _ <| j.le_of_lt_succ hj with
        ⟨f', h₀f', h₂f', h₁f', hf'⟩
      exact ⟨f', ⟨h₀f', h₂f', h₁f'⟩, hf'⟩
  dsimp only [P] at hf
  simp only [forall_and] at hf
  rcases hf with ⟨⟨h₀f, -, h₁f⟩, hfU⟩
  rcases U_fin.exists_forall_eventually_of_indexType hfU with ⟨F, hF⟩
  refine ⟨F, fun x ↦ ?_, fun j ↦ ?_⟩
  · rcases(hF x).exists with ⟨n₀, hn₀⟩
    simp only [Germ.coe_eq.mpr hn₀.symm, h₀f n₀ x]
  · intro x
    rcases((hF x).and <| eventually_ge_atTop j).exists with ⟨n₀, hn₀, hn₀'⟩
    convert (h₁f _ _ hn₀' x) using 1
    exact Germ.coe_eq.mpr hn₀.symm

theorem inductive_construction_of_loc' {X Y : Type*} [EMetricSpace X] [LocallyCompactSpace X]
    [SecondCountableTopology X] (P₀ P₀' P₁ : ∀ x : X, Germ (𝓝 x) Y → Prop) {f₀ : X → Y}
    (hP₀f₀ : ∀ x, P₀ x f₀ ∧ P₀' x f₀)
    (loc : ∀ x, ∃ f : X → Y, (∀ x, P₀ x f) ∧ ∀ᶠ x' in 𝓝 x, P₁ x' f)
    (ind : ∀ {U₁ U₂ K₁ K₂ : Set X} {f₁ f₂ : X → Y}, IsOpen U₁ → IsOpen U₂ →
      IsCompact K₁ → IsCompact K₂ → K₁ ⊆ U₁ → K₂ ⊆ U₂ →
      (∀ x, P₀ x f₁ ∧ P₀' x f₁) → (∀ x, P₀ x f₂) → (∀ x ∈ U₁, P₁ x f₁) → (∀ x ∈ U₂, P₁ x f₂) →
      ∃ f : X → Y, (∀ x, P₀ x f ∧ P₀' x f) ∧
        (∀ᶠ x near K₁ ∪ K₂, P₁ x f) ∧ ∀ᶠ x near K₁ ∪ U₂ᶜ, f x = f₁ x) :
    ∃ f : X → Y, ∀ x, P₀ x f ∧ P₀' x f ∧ P₁ x f := by
  let P : Set X → Prop := fun U ↦ ∃ f : X → Y, (∀ x, P₀ x f) ∧ ∀ x ∈ U, P₁ x f
  have hP₁ : Antitone P := by
    rintro U V hUV ⟨f, h, h'⟩
    exact ⟨f, h, fun x hx ↦ h' x (hUV hx)⟩
  have hP₂ : P ∅ := ⟨f₀, fun x ↦ (hP₀f₀ x).1, fun x h ↦ h.elim⟩
  have hP₃ : ∀ x : X, x ∈ univ → ∃ V ∈ 𝓝 x, P V := fun x _ ↦ by
    rcases loc x with ⟨f, h₀f, h₁f⟩
    exact ⟨_, h₁f, f, h₀f, fun x ↦ id⟩
  rcases exists_locallyFinite_subcover_of_locally isClosed_univ hP₁ hP₂ hP₃ with
    ⟨K, U : IndexType 0 → Set X, K_cpct, U_op, hU, hKU, U_loc, hK⟩
  have ind' : ∀ (i : 𝓘 0) (f : X → Y), (∀ x, P₀ x f ∧ P₀' x f) →
      (∀ j < i, ∀ x, RestrictGermPredicate P₁ (K j) x ↑f) →
      ∃ f' : X → Y, (∀ x : X, P₀ x ↑f' ∧ P₀' x ↑f') ∧
        (∀ j ≤ i, ∀ x, RestrictGermPredicate P₁ (K j) x f') ∧ ∀ x, x ∉ U i → f' x = f x := by
    simp_rw [forall_restrictGermPredicate_iff, ← eventually_nhdsSet_iUnion₂]
    rintro (i : ℕ) f h₀f h₁f
    have cpct : IsCompact (⋃ j < i, K j) :=
      (finite_lt_nat i).isCompact_biUnion fun j _ ↦ K_cpct j
    rcases hU i with ⟨f', h₀f', h₁f'⟩
    rcases mem_nhdsSet_iff_exists.mp h₁f with ⟨V, V_op, hKV, h₁V⟩
    rcases ind V_op (U_op i) cpct (K_cpct i) hKV (hKU i) h₀f h₀f' h₁V h₁f' with
      ⟨F, h₀F, h₁F, hF⟩
    rw [← biUnion_le] at h₁F
    exact ⟨F, h₀F, h₁F, fun x hx ↦ hF.self_of_nhdsSet x (Or.inr hx)⟩
  have :=
    inductive_construction (fun x φ ↦ P₀ x φ ∧ P₀' x φ)
      (fun j : 𝓘 0 ↦ RestrictGermPredicate P₁ (K j)) (fun _ _ ↦ True) U_loc ⟨f₀, hP₀f₀, trivial⟩
  simp only [IndexType.not_isMax, not_false_iff, forall_true_left, true_and] at this
  rcases this ind' with ⟨f, h, h'⟩
  refine ⟨f, fun x ↦ ⟨(h x).1, (h x).2, ?_⟩⟩
  rcases mem_iUnion.mp (hK trivial : x ∈ ⋃ j, K j) with ⟨j, hj⟩
  exact (h' j x hj).self_of_nhds


/-- We are given a suitably nice extended metric space `X` and three local constraints `P₀`,`P₀'`
and `P₁` on maps from `X` to some type `Y`. All maps entering the discussion are required to
statisfy `P₀` everywhere. The goal is to turn a map `f₀` satisfying `P₁` near a compact set `K` into
one satisfying everywhere without changing `f₀` near `K`. The assumptions are:
* For every `x` in `X` there is a map which satisfies `P₁` near `x`
* One can patch two maps `f₁ f₂` satisfying `P₁` on open sets `U₁` and `U₂` respectively
  and such that `f₁` satisfies `P₀'` everywhere into a map satisfying `P₁` on `K₁ ∪ K₂` for any
  compact sets `Kᵢ ⊆ Uᵢ` and `P₀'` everywhere. -/
theorem inductive_construction_of_loc {X Y : Type*} [EMetricSpace X] [LocallyCompactSpace X]
    [SecondCountableTopology X] (P₀ P₀' P₁ : ∀ x : X, Germ (𝓝 x) Y → Prop) {f₀ : X → Y}
    (hP₀f₀ : ∀ x, P₀ x f₀ ∧ P₀' x f₀)
    (loc : ∀ x, ∃ f : X → Y, (∀ x, P₀ x f) ∧ ∀ᶠ x' in 𝓝 x, P₁ x' f)
    (ind : ∀ {U₁ U₂ K₁ K₂ : Set X} {f₁ f₂ : X → Y}, IsOpen U₁ → IsOpen U₂ →
      IsCompact K₁ → IsCompact K₂ → K₁ ⊆ U₁ → K₂ ⊆ U₂ →
      (∀ x, P₀ x f₁ ∧ P₀' x f₁) → (∀ x, P₀ x f₂) → (∀ x ∈ U₁, P₁ x f₁) → (∀ x ∈ U₂, P₁ x f₂) →
      ∃ f : X → Y, (∀ x, P₀ x f ∧ P₀' x f) ∧
        (∀ᶠ x near K₁ ∪ K₂, P₁ x f) ∧ ∀ᶠ x near K₁ ∪ U₂ᶜ, f x = f₁ x) :
    ∃ f : X → Y, ∀ x, P₀ x f ∧ P₀' x f ∧ P₁ x f := by
  apply inductive_construction_of_loc' P₀ P₀' P₁ hP₀f₀ loc
  intro U₁ U₂ K₁ K₂ f₁ f₂ hU₁ hU₂ hK₁ hK₂
  solve_by_elim

theorem set_juggling {X : Type*} [TopologicalSpace X] [NormalSpace X] [T2Space X]
    {K : Set X} (hK : IsClosed K) {U₁ U₂ K₁ K₂ : Set X} (U₁_op : IsOpen U₁)
    (U₂_op : IsOpen U₂) (K₁_cpct : IsCompact K₁) (K₂_cpct : IsCompact K₂) (hK₁U₁ : K₁ ⊆ U₁)
    (hK₂U₂ : K₂ ⊆ U₂) (U : Set X) (U_op : IsOpen U) (hKU : K ⊆ U) :
    ∃ K₁' K₂' U₁' U₂',
      IsOpen U₁' ∧ IsOpen U₂' ∧ IsCompact K₁' ∧ IsCompact K₂' ∧ K₁ ⊆ K₁' ∧ K₁' ⊆ U₁' ∧ K₂' ⊆ U₂' ∧
      K₁' ∪ K₂' = K₁ ∪ K₂ ∧ K ⊆ U₂'ᶜ ∧ U₁' ⊆ U ∪ U₁ ∧ U₂' ⊆ U₂ := by
  obtain ⟨U', U'_op, hKU', hU'U⟩ : ∃ U' : Set X, IsOpen U' ∧ K ⊆ U' ∧ closure U' ⊆ U :=
    normal_exists_closure_subset hK U_op hKU
  refine ⟨K₁ ∪ closure (K₂ ∩ U'), K₂ \ U', U₁ ∪ U, U₂ \ K,
    U₁_op.union U_op, U₂_op.sdiff hK, ?_, K₂_cpct.diff U'_op, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact K₁_cpct.union (K₂_cpct.closure_of_subset inter_subset_left)
  · exact subset_union_left
  · apply union_subset_union hK₁U₁ (subset_trans _ hU'U)
    gcongr
    exact inter_subset_right
  · exact diff_subset_diff hK₂U₂ hKU'
  · rw [union_assoc]
    congr
    apply subset_antisymm
    · exact union_subset (K₂_cpct.isClosed.closure_subset_iff.mpr inter_subset_left) diff_subset
    · calc K₂ = K₂ ∩ U' ∪ K₂ \ U' := (inter_union_diff K₂ U').symm
        _     ⊆ closure (K₂ ∩ U') ∪ K₂ \ U' := union_subset_union_left (K₂ \ U') subset_closure
  · exact fun x hx hx' ↦ hx'.2 hx
  · rw [union_comm]
  · exact diff_subset

/-- We are given a suitably nice extended metric space `X` and three local constraints `P₀`,`P₀'`
and `P₁` on maps from `X` to some type `Y`. All maps entering the discussion are required to
statisfy `P₀` everywhere. The goal is to turn a map `f₀` satisfying `P₁` near a compact set `K` into
one satisfying everywhere without changing `f₀` near `K`. The assumptions are:
* For every `x` in `X` there is a map which satisfies `P₁` near `x`
* One can patch two maps `f₁ f₂` satisfying `P₁` on open sets `U₁` and `U₂` respectively
  into a map satisfying `P₁` on `K₁ ∪ K₂` for any compact sets `Kᵢ ⊆ Uᵢ`.
This is deduced this version from the version where `K` is empty but adding some `P'₀`, see
`inductive_construction_of_loc`. -/
theorem relative_inductive_construction_of_loc {X Y : Type*} [EMetricSpace X]
    [LocallyCompactSpace X] [SecondCountableTopology X] (P₀ P₁ : ∀ x : X, Germ (𝓝 x) Y → Prop)
    {K : Set X} (hK : IsClosed K) {f₀ : X → Y} (hP₀f₀ : ∀ x, P₀ x f₀) (hP₁f₀ : ∀ᶠ x near K, P₁ x f₀)
    (loc : ∀ x, ∃ f : X → Y, (∀ x, P₀ x f) ∧ ∀ᶠ x' in 𝓝 x, P₁ x' f)
    (ind : ∀ {U₁ U₂ K₁ K₂ : Set X} {f₁ f₂ : X → Y},
      IsOpen U₁ → IsOpen U₂ → IsCompact K₁ → IsCompact K₂ → K₁ ⊆ U₁ → K₂ ⊆ U₂ →
      (∀ x, P₀ x f₁) → (∀ x, P₀ x f₂) → (∀ x ∈ U₁, P₁ x f₁) → (∀ x ∈ U₂, P₁ x f₂) →
      ∃ f : X → Y, (∀ x, P₀ x f) ∧ (∀ᶠ x near K₁ ∪ K₂, P₁ x f) ∧ ∀ᶠ x near K₁ ∪ U₂ᶜ, f x = f₁ x) :
    ∃ f : X → Y, (∀ x, P₀ x f ∧ P₁ x f) ∧ ∀ᶠ x near K, f x = f₀ x := by
  let P₀' : ∀ x : X, Germ (𝓝 x) Y → Prop := RestrictGermPredicate (fun x φ ↦ φ.value = f₀ x) K
  have hf₀ : ∀ x, P₀ x f₀ ∧ P₀' x f₀ := fun x ↦
    ⟨hP₀f₀ x, fun _ ↦ Eventually.of_forall fun x' ↦ rfl⟩
  have ind' : ∀ {U₁ U₂ K₁ K₂ : Set X} {f₁ f₂ : X → Y},
      IsOpen U₁ → IsOpen U₂ → IsCompact K₁ → IsCompact K₂ → K₁ ⊆ U₁ → K₂ ⊆ U₂ →
      (∀ x, P₀ x f₁ ∧ P₀' x f₁) → (∀ x, P₀ x f₂) → (∀ x ∈ U₁, P₁ x f₁) → (∀ x ∈ U₂, P₁ x f₂) →
      ∃ f : X → Y, (∀ x, P₀ x f ∧ P₀' x f) ∧
        (∀ᶠ x near K₁ ∪ K₂, P₁ x f) ∧ ∀ᶠ x near K₁ ∪ U₂ᶜ, f x = f₁ x := by
    intro U₁ U₂ K₁ K₂ f₁ f₂ U₁_op U₂_op K₁_cpct K₂_cpct hK₁U₁ hK₂U₂ hf₁ hf₂ hf₁U₁ hf₂U₂
    obtain ⟨h₀f₁, h₀'f₁⟩ := forall_and.mp hf₁
    rw [forall_restrictGermPredicate_iff] at h₀'f₁
    rcases(hasBasis_nhdsSet K).mem_iff.mp (hP₁f₀.germ_congr_set h₀'f₁) with ⟨U,
      ⟨U_op, hKU⟩, hU : ∀ {x}, x ∈ U → P₁ x f₁⟩
    obtain ⟨K₁', K₂', U₁', U₂', U₁'_op, U₂'_op, K₁'_cpct, K₂'_cpct, hK₁K₁', hK₁'U₁', hK₂'U₂',
        hK₁'K₂', hKU₂', hU₁'U, hU₂'U₂⟩ : ∃ (K₁' K₂' U₁' U₂' : Set X),
        IsOpen U₁' ∧ IsOpen U₂' ∧ IsCompact K₁' ∧ IsCompact K₂' ∧
        K₁ ⊆ K₁' ∧ K₁' ⊆ U₁' ∧ K₂' ⊆ U₂' ∧ K₁' ∪ K₂' = K₁ ∪ K₂ ∧ K ⊆ U₂'ᶜ ∧
        U₁' ⊆ U ∪ U₁ ∧ U₂' ⊆ U₂ := by
      apply set_juggling <;> assumption
    have hU₁'P₁ : ∀ x ∈ U₁', P₁ x ↑f₁ :=
      fun x hx ↦ (hU₁'U hx).casesOn (fun h _ ↦ hU h) (fun h _ ↦ hf₁U₁ x h) (hU₁'U hx)
    rcases ind U₁'_op U₂'_op K₁'_cpct K₂'_cpct hK₁'U₁' hK₂'U₂' h₀f₁ hf₂ hU₁'P₁
      (fun x hx ↦ hf₂U₂ x (hU₂'U₂ hx)) with ⟨f, h₀f, hf, h'f⟩
    refine ⟨f, fun x ↦ ⟨h₀f x, restrictGermPredicate_congr (hf₁ x).2 ?_⟩, ?_, ?_⟩
    · exact h'f.filter_mono (nhdsSet_mono <| subset_union_of_subset_right hKU₂' K₁')
    · rwa [hK₁'K₂'] at hf
    · apply h'f.filter_mono; gcongr
  rcases inductive_construction_of_loc P₀ P₀' P₁ hf₀ loc ind' with ⟨f, hf⟩
  simp only [forall_and, forall_restrictGermPredicate_iff, P₀'] at hf ⊢
  exact ⟨f, ⟨hf.1, hf.2.2⟩, hf.2.1⟩

end inductive_construction

section Htpy

private noncomputable def T : ℕ → ℝ := fun n ↦ Nat.rec 0 (fun k x ↦ x + 1 / (2 : ℝ) ^ (k + 1)) n

-- Note this is more painful than Patrick hoped for. Maybe this should be the definition of T.
private theorem T_eq (n : ℕ) : T n = 1 - (1 / 2 : ℝ) ^ n := by
  unfold T
  induction n with
  | zero => simp
  | succ n ihn =>
    simp_rw [ihn, pow_succ', one_div, inv_pow]
    field_simp
    ring

private theorem T_lt (n : ℕ) : T n < 1 := by
  rw [T_eq]
  have : (0 : ℝ) < (1 / 2 : ℝ) ^ n := by positivity
  linarith

private theorem T_lt_succ (n : ℕ) : T n < T (n + 1) :=
  lt_add_of_le_of_pos le_rfl (one_div_pos.mpr (pow_pos zero_lt_two _))

private theorem T_le_succ (n : ℕ) : T n ≤ T (n + 1) :=
  (T_lt_succ n).le

private theorem T_succ_sub (n : ℕ) : T (n + 1) - T n = 1 / (2 : ℝ) ^ (n + 1) :=
  add_sub_cancel_left ..

private theorem mul_T_succ_sub (n : ℕ) : (2 : ℝ) ^ (n + 1) * (T (n + 1) - T n) = 1 := by
  rw [T_succ_sub]
  field_simp

private theorem T_one : T 1 = 1 / 2 := by simp [T]

private theorem T_pos {n : ℕ} (hn : n ≠ 0) : 0 < T n := by
  rw [T_eq, sub_pos]
  apply pow_lt_one₀ <;> first | assumption | norm_num

private theorem T_nonneg (n : ℕ) : 0 ≤ T n := by
  rw [T_eq, sub_nonneg]
  apply pow_le_one₀ <;> norm_num

private theorem not_T_succ_le (n : ℕ) : ¬T (n + 1) ≤ 0 :=
  (T_pos n.succ_ne_zero).not_ge

theorem inductive_htpy_construction' {X Y : Type*} [TopologicalSpace X] {N : ℕ}
    {U K : IndexType N → Set X} (P₀ P₁ : ∀ x : X, Germ (𝓝 x) Y → Prop)
    (P₂ : ∀ p : ℝ × X, Germ (𝓝 p) Y → Prop)
    (hP₂ : ∀ (a b) (p : ℝ × X) (f : ℝ × X → Y), P₂ (a * p.1 + b, p.2) f →
      P₂ p fun p : ℝ × X ↦ f (a * p.1 + b, p.2))
    (U_fin : LocallyFinite U) (K_cover : (⋃ i, K i) = univ) {f₀ : X → Y} (init : ∀ x, P₀ x f₀)
    (init' : ∀ p, P₂ p fun p : ℝ × X ↦ f₀ p.2)
    -- Not in the original version
    (ind : ∀ (i : IndexType N) (f : X → Y), (∀ x, P₀ x f) → (∀ᶠ x near ⋃ j < i, K j, P₁ x f) →
      ∃ F : ℝ → X → Y, (∀ t, ∀ x, P₀ x <| F t) ∧ (∀ᶠ x near ⋃ j ≤ i, K j, P₁ x <| F 1) ∧
        (∀ p, P₂ p ↿F) ∧ (∀ t, ∀ x ∉ (U i), F t x = f x) ∧
          (∀ᶠ t near Iic 0, F t = f) ∧ ∀ᶠ t near Ici 1, F t = F 1) :
    ∃ F : ℝ → X → Y, F 0 = f₀ ∧ (∀ t x, P₀ x (F t)) ∧ (∀ x, P₁ x (F 1)) ∧ ∀ p, P₂ p ↿F := by
  let PP₀ : ∀ p : ℝ × X, Germ (𝓝 p) Y → Prop := fun p φ ↦
    P₀ p.2 φ.sliceRight ∧ (p.1 = 0 → φ.value = f₀ p.2) ∧ P₂ p φ
  let PP₁ : IndexType N → ∀ p : ℝ × X, Germ (𝓝 p) Y → Prop := fun i p φ ↦
    p.1 = 1 → RestrictGermPredicate P₁ (K i) p.2 φ.sliceRight
  let PP₂ : IndexType N → (ℝ × X → Y) → Prop := fun i f ↦
    ∀ x, ∀ t ≥ T i.toNat, f (t, x) = f (T i.toNat, x)
  have hPP₀ : ∀ p : ℝ × X, PP₀ p fun p : ℝ × X ↦ f₀ p.2 := fun (t, x) ↦
    ⟨init x, fun _ ↦ rfl, init' _⟩
  have ind' : ∀ (i) (f : ℝ × X → Y), (∀ p, PP₀ p f) → PP₂ i f → (∀ j < i, ∀ p, PP₁ j p f) →
      ∃ f' : ℝ × X → Y, (∀ p, PP₀ p f') ∧ (¬IsMax i → PP₂ i.succ f') ∧
        (∀ j ≤ i, ∀ p, PP₁ j p f') ∧ ∀ p ∉ Ici (T i.toNat) ×ˢ U i, f' p = f p := by
    rintro i F h₀F h₂F h₁F
    replace h₁F : ∀ᶠ x : X near ⋃ j < i, K j, P₁ x fun x ↦ F (T i.toNat, x) := by
      rw [eventually_nhdsSet_iUnion₂]
      intro j hj
      have : ∀ x : X, RestrictGermPredicate P₁ (K j) x fun x' ↦ F (1, x') := fun x ↦
        h₁F j hj (1, x) rfl
      apply (forall_restrictGermPredicate_iff.mp this).germ_congr_set
      filter_upwards with x
      rw [h₂F _ _ (T_lt _).le]
    rcases ind i (fun x ↦ F (T i.toNat, x)) (fun x ↦ (h₀F (_, x)).1) h₁F with
        ⟨F', h₀F', h₁F', h₂F', hUF', hpast_F', hfutur_F'⟩
    clear ind
    let F'' : ℝ × X → Y := fun p : ℝ × X ↦
      if p.1 ≤ T i.toNat then F p else F' ((2 : ℝ) ^ (i.toNat + 1) * (p.1 - T i.toNat)) p.2
    have loc₁ : ∀ p : ℝ × X, p.1 ≤ T i.toNat → (F'' : Germ (𝓝 p) Y) = F := by
      dsimp only [PP₂] at h₂F
      rintro ⟨t, x⟩ (ht : t ≤ _)
      rcases eq_or_lt_of_le ht with (rfl | ht)
      · apply Quotient.sound
        replace hpast_F' : ↿F' =ᶠ[𝓝 (0, x)] fun q : ℝ × X ↦ F (T i.toNat, q.2) := by
          have : 𝓝 (0 : ℝ) ≤ 𝓝ˢ (Iic 0) := nhds_le_nhdsSet self_mem_Iic
          apply mem_of_superset (prod_mem_nhds (hpast_F'.filter_mono this) univ_mem)
          rintro ⟨t', x'⟩ ⟨ht', -⟩
          exact (congr_fun ht' x' : _)
        have lim : Tendsto (fun x : ℝ × X ↦ ((2 : ℝ) ^ (i.toNat + 1) * (x.1 - T i.toNat), x.2))
            (𝓝 (T i.toNat, x)) (𝓝 (0, x)) := by
          rw [nhds_prod_eq, nhds_prod_eq]
          have limt : Tendsto (fun t ↦ (2 : ℝ) ^ (i.toNat + 1) * (t - T i.toNat))
              (𝓝 (T i.toNat)) (𝓝 0) :=
            Continuous.tendsto' (by fun_prop) _ _ (by simp)
          exact limt.prodMap tendsto_id
        filter_upwards [hpast_F'.comp_tendsto lim]
        dsimp [F'']
        rintro ⟨t, x⟩ h'
        split_ifs with h
        · rfl
        · push Not at h
          change (↿F') ((2 : ℝ) ^ (i.toNat + 1) * (t - T i.toNat), x) = _
          rw [h', h₂F x t h.le]
      · have hp : ∀ᶠ p : ℝ × X in 𝓝 (t, x), p.1 ≤ T i.toNat :=
          continuousAt_fst (p := (t, x)) (Iic_mem_nhds ht)
        apply Quotient.sound
        exact hp.mono fun p hp ↦ if_pos hp
    have loc₂ : ∀ p : ℝ × X, p.1 > T i.toNat →
        (F'' : Germ (𝓝 p) Y) = fun p : ℝ × X ↦
          F' ((2 : ℝ) ^ (i.toNat + 1) * (p.1 - T i.toNat)) p.2 := fun (t, x) ht ↦ by
      apply Quotient.sound
      have hp : ∀ᶠ p : ℝ × X in 𝓝 (t, x), ¬p.1 ≤ T i.toNat := by
        apply mem_of_superset (prod_mem_nhds (Ioi_mem_nhds ht) univ_mem)
        rintro ⟨t', x'⟩ ⟨ht', -⟩
        simpa using ht'
      exact hp.mono fun q hq ↦ if_neg hq
    refine ⟨F'', ?_, ?_, ?_, ?_⟩
    · intro p
      by_cases! ht : p.1 ≤ T i.toNat
      · rw [loc₁ _ ht]
        apply h₀F
      · obtain ⟨t, x⟩ :=p
        rw [loc₂ _ ht]
        refine ⟨h₀F' ((2 : ℝ) ^ (i.toNat + 1) * (t - T i.toNat)) x, ?_, ?_⟩
        · rintro (rfl : t = 0)
          exact (lt_irrefl _ ((T_nonneg i.toNat).trans_lt ht)).elim
        · simpa only [mul_sub, neg_mul]
            using hP₂ ((2 : ℝ) ^ (i.toNat + 1)) (-(2 : ℝ) ^ (i.toNat + 1) * T i.toNat)
              (t, x) (↿F') (h₂F' _)
    · intro hi x t ht
      rw [i.toNat_succ hi] at ht ⊢
      have h₂t : ¬t ≤ T i.toNat := ((T_lt_succ i.toNat).trans_le ht).not_ge
      dsimp only [F'']
      rw [if_neg h₂t, if_neg]
      · rw [hfutur_F'.self_of_nhdsSet, mul_T_succ_sub]
        conv =>
          rw [mem_Ici]
          congr
          rw [← mul_T_succ_sub i.toNat]
        gcongr
      · push Not
        apply T_lt_succ
    · rintro j hj ⟨t, x⟩ (rfl : t = 1)
      replace h₁F' := eventually_nhdsSet_iUnion₂.mp h₁F' j hj
      rw [loc₂ (1, x) (T_lt i.toNat)]
      revert x
      change ∀ x : X, RestrictGermPredicate P₁ (K j) x fun x' : X ↦
          F' ((2 : ℝ) ^ (i.toNat + 1) * (1 - T i.toNat)) x'
      rw [forall_restrictGermPredicate_iff]
      apply h₁F'.germ_congr_set
      filter_upwards
      apply congr_fun (hfutur_F'.self_of_nhdsSet ..)
      rw [mem_Ici]
      conv => congr; skip; rw [← mul_T_succ_sub i.toNat]
      gcongr
      exact (T_lt _).le
    · rintro ⟨t, x⟩ htx
      simp only [prodMk_mem_set_prod_eq, mem_Ici, not_and_or, not_le] at htx
      obtain (ht | hx) := htx
      · change (↑F'' : Germ (𝓝 (t, x)) Y).value = (↑F : Germ (𝓝 (t, x)) Y).value
        rw [loc₁ (t, x) ht.le]
      · dsimp only [F'']
        split_ifs with ht
        · rfl
        · rw [hUF' _ x hx]
          push Not at ht
          rw [h₂F x _ ht.le]
  rcases inductive_construction PP₀ PP₁ PP₂ (U_fin.prod_left fun i ↦ Ici (T i.toNat))
      ⟨fun p ↦ f₀ p.2, hPP₀, fun x t _ ↦ rfl⟩ ind' with
    ⟨F, hF, h'F⟩
  clear ind ind' hPP₀
  refine ⟨curry F, ?_, ?_, ?_, ?_⟩
  · exact funext fun x ↦ (hF (0, x)).2.1 rfl
  · exact fun t x ↦ (hF (t, x)).1
  · intro x
    obtain ⟨j, hj⟩ : ∃ j, x ∈ K j := by simpa using (by simp [K_cover] : x ∈ ⋃ j, K j)
    exact (h'F j (1, x) rfl hj).self_of_nhds
  · exact fun p ↦ (hF p).2.2

theorem inductive_htpy_construction {X Y : Type*}
    [EMetricSpace X] [LocallyCompactSpace X] [SecondCountableTopology X]
    (P₀ P₁ : ∀ x : X, Germ (𝓝 x) Y → Prop)
    (P₂ : ∀ p : ℝ × X, Germ (𝓝 p) Y → Prop)
    (hP₂ : ∀ (a b) (p : ℝ × X) (f : ℝ × X → Y), P₂ (a * p.1 + b, p.2) f →
      P₂ p fun p : ℝ × X ↦ f (a * p.1 + b, p.2))
    (hP₂' : ∀ t x (f : X → Y), P₀ x f → P₂ (t, x) fun p : ℝ × X ↦ f p.2)
    {f₀ : X → Y} (init : ∀ x, P₀ x f₀)
    (ind : ∀ x, ∃ V ∈ 𝓝 x, ∀ K₁ ⊆ V, ∀ K₀ ⊆ interior K₁, IsCompact K₀ → IsCompact K₁ →
      ∀ (C : Set X) (f : X → Y), IsClosed C → (∀ x, P₀ x f) →
      (∀ᶠ x near C, P₁ x f) → ∃ F : ℝ → X → Y, (∀ t, ∀ x, P₀ x <| F t)
        ∧ (∀ᶠ x near C ∪ K₀, P₁ x <| F 1) ∧
      (∀ p, P₂ p ↿F) ∧ (∀ t, ∀ x ∉ K₁, F t x = f x) ∧
      (∀ᶠ t near Iic 0, F t = f) ∧ ∀ᶠ t near Ici 1, F t = F 1) :
    ∃ F : ℝ → X → Y, F 0 = f₀ ∧ (∀ t x, P₀ x (F t)) ∧ (∀ x, P₁ x (F 1)) ∧ ∀ p, P₂ p ↿F := by
  let P (V : Set X) : Prop :=  ∀ K₁ ⊆ V, ∀ K₀ ⊆ interior K₁, IsCompact K₀ → IsCompact K₁ →
      ∀ (C : Set X) (f : X → Y), IsClosed C → (∀ x, P₀ x f) →
      (∀ᶠ x near C, P₁ x f) → ∃ F : ℝ → X → Y, (∀ t, ∀ x, P₀ x <| F t)
        ∧ (∀ᶠ x near C ∪ K₀, P₁ x <| F 1) ∧
      (∀ p, P₂ p ↿F) ∧ (∀ t, ∀ x ∉ K₁, F t x = f x) ∧
      (∀ᶠ t near Iic 0, F t = f) ∧ ∀ᶠ t near Ici 1, F t = F 1
  have P_anti : Antitone P := fun U V UV hV K₁ K₁U ↦ hV K₁ (K₁U.trans UV)
  have P_empty : P ∅ := by
    intro K₁ K₁V K₀ K₀K₁ _ _ C f _ hf hf'
    have K₀_eq : K₀ = ∅ := subset_empty_iff.mp <| K₀K₁.trans interior_subset |>.trans K₁V
    use fun _ x ↦ f x
    simp [hf, hf', K₀_eq]
    tauto
  rcases exists_locallyFinite_subcover_of_locally isClosed_univ P_anti P_empty
    (by simpa only [mem_univ, forall_true_left] using ind) with
    ⟨K : IndexType 0 → Set X, W : IndexType 0 → Set X, K_cpct, W_op, hW, K_subW, W_fin, K_cover⟩
  apply inductive_htpy_construction' P₀ P₁ P₂ hP₂ W_fin (univ_subset_iff.mp K_cover) init
    (fun ⟨t, x⟩ ↦  hP₂' t x f₀ (init x))
  intro i f hf₀ hf₁
  obtain ⟨K₁, K₁_cpct, KiK₁, K₁W⟩ : ∃ K₁, IsCompact K₁ ∧ K i ⊆ interior K₁ ∧ K₁ ⊆ W i :=
    exists_compact_between (K_cpct i) (W_op i) (K_subW i)
  rcases hW i K₁ K₁W (K i) KiK₁ (K_cpct i) K₁_cpct (⋃ j < i, K j) f
    ((finite_lt_nat i).isClosed_biUnion fun j _ ↦ (K_cpct j).isClosed) hf₀ hf₁
    with ⟨F, hF₀, hF₁, hF₂, hFK₁, ht⟩
  refine ⟨F, hF₀, ?_, hF₂, ?_, ht⟩
  · apply hF₁.filter_mono
    gcongr
    rw [biUnion_le]
  · exact fun t x hx ↦ hFK₁ t x (notMem_subset K₁W hx)
end Htpy
