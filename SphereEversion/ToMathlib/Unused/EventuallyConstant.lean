/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

! This file was ported from Lean 3 source module to_mathlib.unused.eventually_constant
-/
import Mathbin.Data.Nat.Lattice
import Mathbin.Topology.Separation

/-!
# Eventually constant sequences

Related: `monotonic_sequence_limit_index`
-/


-- in mathlib, this should probably import
-- import order.filter.at_top_bot
-- and topology.separation should import this
-- import topology.basic
open scoped Topology

-- move
theorem ContinuousWithinAt.congr_nhds {α β} [TopologicalSpace α] [TopologicalSpace β] {f f₁ : α → β}
    {s : Set α} {x : α} (h : ContinuousWithinAt f s x) (h₁ : f₁ =ᶠ[𝓝 x] f) :
    ContinuousWithinAt f₁ s x :=
  h.congr_of_eventuallyEq (nhdsWithin_le_nhds h₁) h₁.self_of_nhds

namespace Set

-- move
variable {α β γ : Type _} {s t : Set α} {f : s → β} {g : t → β} {x : α}

/-- The union `f ∪ g` of two functions `f : s → β` and `g : t → β`.
  On the intersection `s ∩ t`, the function `f ∪ g` corresponds to `f`. -/
def unionElim [DecidablePred (· ∈ s)] (f : s → β) (g : t → β) (x : s ∪ t) : β :=
  if h : (x : α) ∈ s then f ⟨x, h⟩ else g ⟨x, x.Prop.resolve_left h⟩

theorem unionElim_eq_left [DecidablePred (· ∈ s)] (hx : x ∈ s) :
    unionElim f g ⟨x, mem_union_left _ hx⟩ = f ⟨x, hx⟩ :=
  dif_pos hx

theorem unionElim_eq_right [DecidablePred (· ∈ s)] (h1x : x ∈ s ∪ t) (h2x : x ∉ s) :
    unionElim f g ⟨x, h1x⟩ = g ⟨x, h1x.resolve_left h2x⟩ :=
  dif_neg h2x

theorem unionElim_eq_right_of_eq [DecidablePred (· ∈ s)] (hxt : x ∈ t)
    (hfg : ∀ (x) (hxs : x ∈ s) (hxt : x ∈ t), f ⟨x, hxs⟩ = g ⟨x, hxt⟩) :
    unionElim f g ⟨x, mem_union_right _ hxt⟩ = g ⟨x, hxt⟩ :=
  if hxs : x ∈ s then (unionElim_eq_left hxs).trans (hfg x hxs hxt) else unionElim_eq_right _ hxs

theorem unionElim_restrict [DecidablePred (· ∈ s)] (f : α → β) :
    unionElim (s.restrict f) (t.restrict f) = (s ∪ t).restrict f :=
  by
  ext ⟨x, hx⟩
  cases (mem_union _ _ _).mp hx <;> simp [union_elim_eq_left, union_elim_eq_right_of_eq, h]

end Set

open scoped Classical

open Set

namespace Filter

variable {α β γ : Type _} {g : α → β} {f : Filter α} {x : α} {y : β}

/-- The proposition that a function is eventually constant along a fitler on the domain. -/
def EventuallyConstant (g : α → β) (f : Filter α) : Prop :=
  ∃ y : β, ∀ᶠ x in f, g x = y

theorem eventuallyConstant_iff_tendsto : EventuallyConstant g f ↔ ∃ x : β, Tendsto g f (pure x) :=
  by simp_rw [eventually_constant, tendsto_pure]

theorem EventuallyConstant.nonempty (h : EventuallyConstant g f) : Nonempty β :=
  nonempty_of_exists h

theorem eventuallyConstant_const (y₀ : β) : EventuallyConstant (fun x => y₀) f :=
  ⟨y₀, eventually_of_forall fun x => rfl⟩

theorem eventuallyConstant_of_unique [Unique β] : EventuallyConstant g f :=
  ⟨default, eventually_of_forall fun x => Unique.uniq _ _⟩

theorem eventuallyConstant_atTop [SemilatticeSup α] [Nonempty α] :
    (∃ i, ∀ j, i ≤ j → g j = g i) ↔ EventuallyConstant g atTop :=
  by
  simp_rw [eventually_constant, eventually_at_top]
  constructor
  · rintro ⟨i, hi⟩; refine' ⟨g i, i, hi⟩
  · rintro ⟨y, i, hi⟩; use i; simp_rw [hi i le_rfl]; exact hi

theorem eventuallyConstant_atTop_nat {g : ℕ → α} :
    (∃ n, ∀ m, n ≤ m → g (m + 1) = g m) ↔ EventuallyConstant g atTop :=
  by
  rw [← eventually_constant_at_top]
  apply exists_congr; intro n
  constructor
  · intro h m hm; induction' hm with m hm ih; rfl; rw [Nat.succ_eq_add_one, h m hm, ih]
  · intro h m hm; rw [h m hm, h (m + 1) hm.step]

theorem EventuallyConstant.compose (h : EventuallyConstant g f) (g' : β → γ) :
    EventuallyConstant (g' ∘ g) f := by cases' h with y hy;
  exact ⟨g' y, hy.mono fun x => congr_arg g'⟩

theorem EventuallyConstant.apply {ι : Type _} {p : ι → Type _} {g : α → ∀ x, p x}
    (h : EventuallyConstant g f) (i : ι) : EventuallyConstant (fun x => g x i) f :=
  h.compose fun p => p i

/-- The eventual value of an eventually-constant function.

For convenience, `eventual_value` may be applied to any function; if the input is not
eventually-constant the result should be regarded as a "junk" value. -/
noncomputable def eventualValue [Nonempty β] (g : α → β) (f : Filter α) : β :=
  Classical.epsilon fun x : β => ∀ᶠ i in f, g i = x

theorem eventually_eq_eventualValue (h : EventuallyConstant g f) :
    ∀ᶠ i in f, g i = @eventualValue _ _ h.Nonempty g f :=
  Classical.epsilon_spec h

theorem eventualValue_unique [f.ne_bot] {y : β} (hy : ∀ᶠ i in f, g i = y) :
    y = @eventualValue _ _ ⟨y⟩ g f := by
  obtain ⟨x, rfl, hx⟩ := (hy.and <| eventually_eq_eventual_value ⟨y, hy⟩).exists; exact hx

/-- This lemma is sometimes useful if the elaborator uses the nonempty instance in
  `eventual_value_unique` to find the implicit argument `y`. -/
theorem eventualValue_unique' [f.ne_bot] {hβ : Nonempty β} {y : β} (hy : ∀ᶠ i in f, g i = y) :
    eventualValue g f = y :=
  (eventualValue_unique hy).symm

theorem eventualValue_eq_fn {g : ℕ → β} {hβ : Nonempty β} {n : ℕ} (h : ∀ m, n ≤ m → g m = g n) :
    eventualValue g atTop = g n :=
  eventualValue_unique' <| eventually_of_mem (mem_atTop _) h

theorem EventuallyConstant.exists_eventualValue_eq [f.ne_bot] (h : EventuallyConstant g f) :
    ∃ i, @eventualValue _ _ h.Nonempty g f = g i :=
  by
  obtain ⟨y, hy⟩ := h
  obtain ⟨x, rfl⟩ := hy.exists
  exact ⟨x, (eventual_value_unique hy).symm⟩

theorem EventuallyConstant.tendsto [Nonempty β] (h : EventuallyConstant g f) :
    Tendsto g f (pure (eventualValue g f)) := by rw [tendsto_pure];
  exact eventually_eq_eventual_value h

theorem eventualValue_compose [f.ne_bot] (h : EventuallyConstant g f) (g' : β → γ) :
    @eventualValue _ _ (h.compose g').Nonempty (g' ∘ g) f =
      g' (@eventualValue _ _ h.Nonempty g f) :=
  (eventualValue_unique <| (eventually_eq_eventualValue h).mono fun x => congr_arg g').symm

theorem eventualValue_apply {ι : Type _} {p : ι → Type _} [f.ne_bot] {g : α → ∀ x, p x}
    (h : EventuallyConstant g f) (i : ι) :
    @eventualValue _ _ h.Nonempty g f i =
      @eventualValue _ _ (h.apply i).Nonempty (fun x => g x i) f :=
  (eventualValue_compose h fun p => p i).symm

theorem EventuallyConstant.tendsto_nhds [Nonempty β] [TopologicalSpace β]
    (h : EventuallyConstant g f) : Tendsto g f (𝓝 (eventualValue g f)) :=
  h.Tendsto.mono_right <| pure_le_nhds _

/-- todo: generalize to `t1_space`. -/
theorem eventualValue_eq_limUnder [f.ne_bot] [Nonempty β] [TopologicalSpace β] [T2Space β]
    (h : EventuallyConstant g f) : eventualValue g f = limUnder f g :=
  h.tendsto_nhds.limUnder_eq.symm

-- the following can be generalized a lot using `eventually_constant.exists_eventual_value_eq`.
-- /-- The index from where a function `g : ℕ → α` is eventually constant. Equals `0` if `g` is not
--   eventually constant. -/
-- noncomputable def eventual_index (g : ℕ → α) : ℕ :=
-- Inf {n : ℕ | ∀ m, n ≤ m → g m = g n}
-- lemma eventually_constant.eq_eventual_index {g : ℕ → α} (hg : eventually_constant g at_top) {n : ℕ}
--   (hn : eventual_index g ≤ n) : g n = g (eventual_index g) :=
-- nat.Inf_mem (eventually_constant_at_top.mpr hg) n hn
-- lemma eventually_constant.fn_eventual_index {g : ℕ → α} (hg : eventually_constant g at_top) :
--   g (eventual_index g) = @eventual_value _ _ ⟨g 0⟩ g at_top :=
-- (eventual_value_eq_fn $ λ n hn, (hg.eq_eventual_index hn : _)).symm
-- lemma eventually_constant.eq_eventual_value_of_eventual_index_le {g : ℕ → α}
--   (hg : eventually_constant g at_top) {n : ℕ}
--   (hn : eventual_index g ≤ n) : g n = @eventual_value _ _ ⟨g 0⟩ g at_top :=
-- (hg.eq_eventual_index hn).trans hg.fn_eventual_index
-- lemma foo {g : α → β → γ} {s : set β} (hg : eventually_constant (λ n, s.restrict (g n)) f)
--   (hy : y ∈ s) :
-- unproved
end Filter

open Filter

variable {α β γ δ : Type _} {g : α → β → γ} {f : Filter α} {O U : Set β} {i : α} {x : β}

section EventuallyConstantOn

/-- A sequence of functions `g` is eventually constant on `O` w.r.t. filter `f` if
  `g` restricted to `O` is eventually constant.
-/
def EventuallyConstantOn (g : α → β → γ) (f : Filter α) (O : Set β) : Prop :=
  EventuallyConstant (fun n => O.restrict (g n)) f

theorem EventuallyConstantOn.eventuallyConstant (hg : EventuallyConstantOn g f O) (hx : x ∈ O) :
    EventuallyConstant (fun n => g n x) f := by cases' hg with y hg;
  exact ⟨y ⟨x, hx⟩, hg.mono fun n hn => (function.funext_iff.mp hn ⟨x, hx⟩ : _)⟩

theorem EventuallyConstantOn.nonempty (hg : EventuallyConstantOn g f O) (hx : x ∈ O) : Nonempty γ :=
  (hg.EventuallyConstant hx).Nonempty

theorem eventuallyConstantOn_atTop [SemilatticeSup α] [Nonempty α] :
    (∃ x, ∀ x', x ≤ x' → ∀ y ∈ O, g x' y = g x y) ↔ EventuallyConstantOn g atTop O := by
  simp_rw [EventuallyConstantOn, ← eventually_constant_at_top, restrict_eq_restrict_iff, eq_on]

theorem EventuallyConstantOn.exists_eventualValue_eq [f.ne_bot] (hg : EventuallyConstantOn g f O) :
    ∃ i, ∀ (x) (hx : x ∈ O), @eventualValue _ _ (hg.Nonempty hx) (fun n => g n x) f = g i x := by
  simpa only [@eq_restrict_iff β fun _ => γ, eventual_value_apply hg] using
    hg.exists_eventual_value_eq

-- lemma eventually_constant_on.exists_eventual_value_eq [f.ne_bot] (h : eventually_constant g f) :
--   ∃ x, @eventual_value _ _ h.nonempty g f = g x :=
-- begin
--   obtain ⟨y, hy⟩ := h,
--   obtain ⟨x, rfl⟩ := hy.exists,
--   exact ⟨x, (eventual_value_unique hy).symm⟩
-- end
end EventuallyConstantOn

variable [TopologicalSpace β]

section LocallyEventuallyConstant

/-- A sequence of functions `g` is locally eventually constant on `U` w.r.t. filter `f` if
  every point in `U` has a neighborhood `O` such that `g` restricted to `O` is eventually constant.
-/
def LocallyEventuallyConstantOn (g : α → β → γ) (f : Filter α) (U : Set β) : Prop :=
  ∀ x ∈ U, ∃ O ∈ 𝓝 x, EventuallyConstantOn g f O

theorem LocallyEventuallyConstantOn.eventuallyConstant (hgf : LocallyEventuallyConstantOn g f U)
    (hx : x ∈ U) : EventuallyConstant (fun n => g n x) f := by obtain ⟨O, hO, hg⟩ := hgf x hx;
  exact hg.eventually_constant (mem_of_mem_nhds hO)

theorem LocallyEventuallyConstantOn.nonempty (hg : LocallyEventuallyConstantOn g f U) (hx : x ∈ U) :
    Nonempty γ :=
  (hg.EventuallyConstant hx).Nonempty

theorem LocallyEventuallyConstantOn.continuousWithinAt [TopologicalSpace δ] [f.ne_bot] [Nonempty δ]
    (F : γ → δ) (hgf : LocallyEventuallyConstantOn g f U) (hxU : x ∈ U)
    (hg : ∀ i, ContinuousWithinAt (F ∘ g i) U x) :
    ContinuousWithinAt (fun x => eventualValue (fun i => F (g i x)) f) U x :=
  by
  obtain ⟨O, hO, hgO⟩ := hgf x hxU
  obtain ⟨i, hi⟩ := (eventually_eq_eventual_value hgO).exists
  simp_rw [Function.funext_iff, eventual_value_apply hgO] at hi 
  refine' (hg i).congr_nhds (eventually_of_mem hO fun y (hy : y ∈ O) => _)
  refine' Eq.trans _ (congr_arg F <| hi ⟨y, hy⟩).symm
  apply eventual_value_compose

theorem LocallyEventuallyConstantOn.exists_nhdsSet_of_isCompact
    (hgf : LocallyEventuallyConstantOn g f U) {K : Set β} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ O ∈ 𝓝ˢ K, EventuallyConstantOn g f O :=
  by
  refine' IsCompact.induction_on hK ⟨∅, mem_nhdsSet_empty, eventually_constant_of_unique⟩ _ _ _
  · rintro s t hst ⟨O, hO, hgO⟩; refine' ⟨O, _, hgO⟩; exact monotone_nhdsSet hst hO
  · rintro s t ⟨O, hO, y, hgO⟩ ⟨O', hO', y', hgO'⟩
    refine' ⟨O ∪ O', union_mem_nhdsSet hO hO', union_elim y y', _⟩
    filter_upwards [hgO, hgO']; rintro x rfl rfl
    rw [union_elim_restrict]
  · intro x hx; rcases hgf x (hKU hx) with ⟨O, hO, hgO⟩
    exact
      ⟨interior O, mem_nhdsWithin_of_mem_nhds <| interior_mem_nhds.mpr hO, O, mem_nhdsSet_interior,
        hgO⟩

/-- A neighborhood around `x` where `g` is locally constant. -/
def LocallyEventuallyConstantOn.nhd (hgf : LocallyEventuallyConstantOn g f U) (hx : x ∈ U) :
    Set β :=
  Classical.choose <| hgf x hx

theorem LocallyEventuallyConstantOn.nhd_mem_nhds (hgf : LocallyEventuallyConstantOn g f U)
    (hx : x ∈ U) : hgf.nhd hx ∈ 𝓝 x :=
  Classical.choose <| Classical.choose_spec <| hgf x hx

theorem LocallyEventuallyConstantOn.eventually_constant_nhd
    (hgf : LocallyEventuallyConstantOn g f U) (hx : x ∈ U) :
    EventuallyConstantOn g f (hgf.nhd hx) :=
  Classical.choose_spec <| Classical.choose_spec <| hgf x hx

end LocallyEventuallyConstant

