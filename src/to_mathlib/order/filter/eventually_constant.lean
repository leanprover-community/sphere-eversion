/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
-- in mathlib, this should probably import
-- import order.filter.at_top_bot
-- and topology.separation should import this
-- import topology.basic

import data.nat.lattice
import topology.separation
import to_mathlib.topology.nhds_set
/-!
# Eventually constant sequences

Related: `monotonic_sequence_limit_index`
-/

open_locale topological_space
-- move
lemma continuous_within_at.congr_nhds {α β} [topological_space α] [topological_space β]
  {f f₁ : α → β} {s : set α} {x : α} (h : continuous_within_at f s x)
  (h₁ : f₁ =ᶠ[𝓝 x] f) : continuous_within_at f₁ s x :=
h.congr_of_eventually_eq (nhds_within_le_nhds h₁) h₁.self_of_nhds

namespace set
-- move
variables {α β γ : Type*} {s t : set α} {f : s → β} {g : t → β} {x : α}

@[simp]
lemma restrict_eq_iff {f : α → β} {g : s → β} :
  restrict f s = g ↔ ∀ x (hx : x ∈ s), f x = g ⟨x, hx⟩ :=
by simp_rw [function.funext_iff, set_coe.forall, restrict_apply, subtype.coe_mk]

@[simp]
lemma eq_restrict_iff {g : α → β} : f = restrict g s ↔ ∀ x (hx : x ∈ s), f ⟨x, hx⟩ = g x :=
by simp_rw [@eq_comm _ f, restrict_eq_iff, eq_comm]

@[simp]
lemma restrict_eq_restrict_iff {f g : α → β} : restrict f s = restrict g s ↔ ∀ x ∈ s, f x = g x :=
by simp_rw [restrict_eq_iff, restrict_apply, subtype.coe_mk]

/-- The union `f ∪ g` of two functions `f : s → β` and `g : t → β`.
  On the intersection `s ∩ t`, the function `f ∪ g` corresponds to `f`. -/
def union_elim [decidable_pred (∈ s)] (f : s → β) (g : t → β) (x : s ∪ t) : β :=
if h : (x : α) ∈ s then f ⟨x, h⟩ else g ⟨x, x.prop.resolve_left h⟩

lemma union_elim_eq_left [decidable_pred (∈ s)] (hx : x ∈ s) :
  union_elim f g ⟨x, mem_union_left _ hx⟩ = f ⟨x, hx⟩ :=
dif_pos hx

lemma union_elim_eq_right [decidable_pred (∈ s)] (h1x : x ∈ s ∪ t) (h2x : x ∉ s) :
  union_elim f g ⟨x, h1x⟩ = g ⟨x, h1x.resolve_left h2x⟩ :=
dif_neg h2x

lemma union_elim_eq_right_of_eq [decidable_pred (∈ s)] (hxt : x ∈ t)
  (hfg : ∀ x (hxs : x ∈ s) (hxt : x ∈ t), f ⟨x, hxs⟩ = g ⟨x, hxt⟩) :
  union_elim f g ⟨x, mem_union_right _ hxt⟩ = g ⟨x, hxt⟩ :=
if hxs : x ∈ s then (union_elim_eq_left hxs).trans (hfg x hxs hxt) else union_elim_eq_right _ hxs

lemma union_elim_restrict [decidable_pred (∈ s)] (f : α → β) :
  union_elim (restrict f s) (restrict f t) = restrict f (s ∪ t) :=
begin
  ext ⟨x, hx⟩,
  cases (mem_union _ _ _).mp hx; simp [union_elim_eq_left, union_elim_eq_right_of_eq, h]
end

end set

open_locale classical
open set

namespace filter

variables {α β γ : Type*} {g : α → β} {f : filter α} {x : α} {y : β}

def eventually_constant (g : α → β) (f : filter α) : Prop :=
∃ y : β, ∀ᶠ x in f, g x = y

lemma eventually_constant_iff_tendsto : eventually_constant g f ↔ ∃ x : β, tendsto g f (pure x) :=
by simp_rw [eventually_constant, tendsto_pure]

lemma eventually_constant.nonempty (h : eventually_constant g f) : nonempty β :=
nonempty_of_exists h

lemma eventually_constant_const (y₀ : β) : eventually_constant (λ x, y₀) f :=
⟨y₀, eventually_of_forall $ λ x, rfl⟩

lemma eventually_constant_of_unique [unique β] : eventually_constant g f :=
⟨default, eventually_of_forall $ λ x, unique.uniq _ _⟩

lemma eventually_constant_at_top [semilattice_sup α] [nonempty α] :
  (∃ i, ∀ j ≥ i, g j = g i) ↔ eventually_constant g at_top :=
begin
  simp_rw [eventually_constant, eventually_at_top],
  split,
  { rintro ⟨i, hi⟩, refine ⟨g i, i, hi⟩ },
  { rintro ⟨y, i, hi⟩, use i, simp_rw [hi i le_rfl], exact hi },
end

lemma eventually_constant_at_top_nat {g : ℕ → α} :
  (∃ n, ∀ m ≥ n, g (m + 1) = g m) ↔ eventually_constant g at_top :=
begin
  rw [← eventually_constant_at_top],
  apply exists_congr, intro n,
  split,
  { intros h m hm, induction hm with m hm ih, refl, rw [nat.succ_eq_add_one, h m hm, ih] },
  { intros h m hm, rw [h m hm, h (m + 1) hm.step] }
end

lemma eventually_constant.compose (h : eventually_constant g f) (g' : β → γ) :
  eventually_constant (g' ∘ g) f :=
by { cases h with y hy, exact ⟨g' y, hy.mono $ λ x, congr_arg g'⟩ }

lemma eventually_constant.apply {ι : Type*} {p : ι → Type*} {g : α → ∀ x, p x}
  (h : eventually_constant g f) (i : ι) : eventually_constant (λ x, g x i) f :=
h.compose $ λ p, p i

noncomputable def eventual_value [nonempty β] (g : α → β) (f : filter α) : β :=
classical.epsilon $ λ x : β, ∀ᶠ i in f, g i = x

lemma eventually_eq_eventual_value (h : eventually_constant g f) :
  ∀ᶠ i in f, g i = @eventual_value _ _ h.nonempty g f :=
classical.epsilon_spec h

lemma eventual_value_unique [f.ne_bot] {y : β} (hy : ∀ᶠ i in f, g i = y) :
  y = @eventual_value _ _ ⟨y⟩ g f :=
by { obtain ⟨x, rfl, hx⟩ := (hy.and $ eventually_eq_eventual_value ⟨y, hy⟩).exists, exact hx }

/-- This lemma is sometimes useful if the elaborator uses the nonempty instance in
  `eventual_value_unique` to find the implicit argument `y`. -/
lemma eventual_value_unique' [f.ne_bot] {hβ : nonempty β} {y : β} (hy : ∀ᶠ i in f, g i = y) :
  eventual_value g f = y  :=
(eventual_value_unique hy).symm

lemma eventual_value_eq_fn {g : ℕ → β} {hβ : nonempty β} {n : ℕ} (h : ∀ m, n ≤ m → g m = g n) :
  eventual_value g at_top = g n :=
eventual_value_unique' $ eventually_of_mem (mem_at_top _) h

lemma eventually_constant.exists_eventual_value_eq [f.ne_bot] (h : eventually_constant g f) :
  ∃ x, @eventual_value _ _ h.nonempty g f = g x :=
begin
  obtain ⟨y, hy⟩ := h,
  obtain ⟨x, rfl⟩ := hy.exists,
  exact ⟨x, (eventual_value_unique hy).symm⟩
end

lemma eventually_constant.tendsto [nonempty β] (h : eventually_constant g f) :
  tendsto g f (pure (eventual_value g f)) :=
by { rw [tendsto_pure], exact eventually_eq_eventual_value h }

lemma eventual_value_compose [f.ne_bot] (h : eventually_constant g f) (g' : β → γ) :
  @eventual_value _ _ (h.compose g').nonempty (g' ∘ g) f =
  g' (@eventual_value _ _ h.nonempty g f) :=
(eventual_value_unique $ (eventually_eq_eventual_value h).mono $ λ x, congr_arg g').symm

lemma eventual_value_apply {ι : Type*} {p : ι → Type*} [f.ne_bot] {g : α → ∀ x, p x}
  (h : eventually_constant g f) (i : ι) :
  @eventual_value _ _ h.nonempty g f i = @eventual_value _ _ (h.apply i).nonempty (λ x, g x i) f :=
(eventual_value_compose h $ λ p, p i).symm

lemma eventually_constant.tendsto_nhds [nonempty β] [topological_space β]
  (h : eventually_constant g f) : tendsto g f (𝓝 (eventual_value g f)) :=
h.tendsto.mono_right $ pure_le_nhds _

lemma eventual_value_eq_lim [f.ne_bot] [nonempty β] [topological_space β] [t2_space β]
  (h : eventually_constant g f) : eventual_value g f = lim f g :=
h.tendsto_nhds.lim_eq.symm

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
-- sorry := sorry

end filter
open filter

variables {α β γ δ : Type*} {g : α → β → γ}
  {f : filter α} {O U : set β} {i : α} {x : β}

section eventually_constant_on

/--
  A sequence of functions `g` is eventually constant on `O` w.r.t. filter `f` if
  `g` restricted to `O` is eventually constant.
-/
def eventually_constant_on (g : α → β → γ) (f : filter α) (O : set β) : Prop :=
eventually_constant (λ n, O.restrict (g n)) f

lemma eventually_constant_on.eventually_constant (hg : eventually_constant_on g f O) (hx : x ∈ O) :
  eventually_constant (λ n, g n x) f :=
begin
  cases hg with y hg, exact ⟨y ⟨x, hx⟩, hg.mono $ λ n hn, (function.funext_iff.mp hn ⟨x, hx⟩ : _)⟩
end

lemma eventually_constant_on.nonempty (hg : eventually_constant_on g f O) (hx : x ∈ O) :
  nonempty γ :=
(hg.eventually_constant hx).nonempty

lemma eventually_constant_on_at_top [semilattice_sup α] [nonempty α] :
  (∃ x, ∀ x' ≥ x, ∀ y ∈ O, g x' y = g x y) ↔ eventually_constant_on g at_top O :=
by simp_rw [eventually_constant_on, ← eventually_constant_at_top, restrict_eq_restrict_iff]

lemma eventually_constant_on.exists_eventual_value_eq [f.ne_bot]
  (hg : eventually_constant_on g f O) :
  ∃ i, ∀ x (hx : x ∈ O), @eventual_value _ _ (hg.nonempty hx) (λ n, g n x) f = g i x :=
by simpa only [eq_restrict_iff, eventual_value_apply hg] using hg.exists_eventual_value_eq

-- lemma eventually_constant_on.exists_eventual_value_eq [f.ne_bot] (h : eventually_constant g f) :
--   ∃ x, @eventual_value _ _ h.nonempty g f = g x :=
-- begin
--   obtain ⟨y, hy⟩ := h,
--   obtain ⟨x, rfl⟩ := hy.exists,
--   exact ⟨x, (eventual_value_unique hy).symm⟩
-- end

end eventually_constant_on

variables [topological_space β]

section locally_eventually_constant

/--
  A sequence of functions `g` is locally eventually constant on `U` w.r.t. filter `f` if
  every point in `U` has a neighborhood `O` such that `g` restricted to `O` is eventually constant.
-/
def locally_eventually_constant_on (g : α → β → γ) (f : filter α) (U : set β) : Prop :=
∀ x ∈ U, ∃ O ∈ 𝓝 x, eventually_constant_on g f O

lemma locally_eventually_constant_on.eventually_constant
  (hgf : locally_eventually_constant_on g f U) (hx : x ∈ U) :
  eventually_constant (λ n, g n x) f :=
by { obtain ⟨O, hO, hg⟩ := hgf x hx, exact hg.eventually_constant (mem_of_mem_nhds hO) }

lemma locally_eventually_constant_on.nonempty (hg : locally_eventually_constant_on g f U)
  (hx : x ∈ U) : nonempty γ :=
(hg.eventually_constant hx).nonempty

lemma locally_eventually_constant_on.continuous_within_at
  [topological_space δ] [f.ne_bot] [nonempty δ]
  (F : γ → δ)
  (hgf : locally_eventually_constant_on g f U) (hxU : x ∈ U)
  (hg : ∀ i, continuous_within_at (F ∘ g i) U x) :
  continuous_within_at (λ x, eventual_value (λ i, F (g i x)) f) U x :=
begin
  obtain ⟨O, hO, hgO⟩ := hgf x hxU,
  obtain ⟨i, hi⟩ := (eventually_eq_eventual_value hgO).exists,
  simp_rw [function.funext_iff, eventual_value_apply hgO] at hi,
  refine (hg i).congr_nhds (eventually_of_mem hO $ λ y (hy : y ∈ O), _),
  refine eq.trans _ (congr_arg F $ hi ⟨y, hy⟩).symm,
  apply eventual_value_compose,
end

lemma locally_eventually_constant_on.exists_nhds_set_of_is_compact
  (hgf : locally_eventually_constant_on g f U)
  {K : set β} (hK : is_compact K) (hKU : K ⊆ U) :
  ∃ O ∈ nhds_set K, eventually_constant_on g f O :=
begin
  refine is_compact.induction_on hK ⟨∅, mem_nhds_set_empty, eventually_constant_of_unique⟩ _ _ _,
  { rintro s t hst ⟨O, hO, hgO⟩, refine ⟨O, _, hgO⟩, exact monotone_nhds_set hst hO },
  { rintro s t ⟨O, hO, y, hgO⟩ ⟨O', hO', y', hgO'⟩,
    refine ⟨O ∪ O', union_mem_nhds_set hO hO', union_elim y y', _⟩,
    filter_upwards [hgO, hgO'], rintro x rfl rfl,
    rw union_elim_restrict },
  { intros x hx, rcases hgf x (hKU hx) with ⟨O, hO, hgO⟩,
    exact ⟨interior O, mem_nhds_within_of_mem_nhds $ interior_mem_nhds.mpr hO, O,
      mem_nhds_interior, hgO⟩ }
end

/-- A neighborhood around `x` where `g` is locally constant. -/
def locally_eventually_constant_on.nhd (hgf : locally_eventually_constant_on g f U) (hx : x ∈ U) :
  set β :=
classical.some $ hgf x hx

lemma locally_eventually_constant_on.nhd_mem_nhds (hgf : locally_eventually_constant_on g f U)
  (hx : x ∈ U) : hgf.nhd hx ∈ 𝓝 x :=
classical.some $ classical.some_spec $ hgf x hx

lemma locally_eventually_constant_on.eventually_constant_nhd
  (hgf : locally_eventually_constant_on g f U) (hx : x ∈ U) :
  eventually_constant_on g f (hgf.nhd hx) :=
classical.some_spec $ classical.some_spec $ hgf x hx

end locally_eventually_constant

/-
A bunch of lemmas formulated for t2_space also hold for t1_space.
tendsto_const_nhds_iff'
eventual_value_eq_lim
nhds_eq_nhds_iff
nhds_le_nhds_iff
-/
