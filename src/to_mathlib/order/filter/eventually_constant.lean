/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
-- in mathlib, this should probably import
-- import order.filter.at_top_bot
-- and topology.separation should import this
-- import topology.basic
import topology.separation
/-!
# Eventually constant sequences

Related: `monotonic_sequence_limit_index`
-/

open_locale topological_space

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

lemma eventually_constant_at_top [semilattice_sup α] [nonempty α] :
  (∃ x, ∀ y ≥ x, g y = g x) ↔ eventually_constant g at_top :=
begin
  simp_rw [eventually_constant, eventually_at_top],
  split,
  { rintro ⟨x, hx⟩, refine ⟨g x, x, hx⟩ },
  { rintro ⟨y, x, hx⟩, use x, simp_rw [hx x le_rfl], exact hx },
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

end filter
open filter

variables {α β γ δ : Type*} [topological_space β] {g : α → β → γ}
  {f : filter α} {U : set β} {i : α} {x : β}

section locally_eventually_constant


def locally_eventually_constant_on (g : α → β → γ) (f : filter α) (U : set β) : Prop :=
∀ x ∈ U, ∃ (O ∈ 𝓝 x), eventually_constant (λ n, (O : set β).restrict (g n)) f

-- def locally_eventually_constant_on (g : α → β → γ) (f : filter α) (U : set β) (x : β) : Prop

lemma continuous_within_at.congr_nhds {α β} [topological_space α] [topological_space β]
  {f f₁ : α → β} {s : set α} {x : α} (h : continuous_within_at f s x)
  (h₁ : f₁ =ᶠ[𝓝 x] f) : continuous_within_at f₁ s x :=
h.congr_of_eventually_eq (nhds_within_le_nhds h₁) h₁.self_of_nhds

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
  refine (hg i).congr_nhds (eventually_of_mem hO $ λ y hy, _),
  refine eq.trans _ (congr_arg F $ hi ⟨y, hy⟩).symm,
  apply eventual_value_compose,
end

end locally_eventually_constant

/-
A bunch of lemmas formulated for t2_space also hold for t1_space.
tendsto_const_nhds_iff'
eventual_value_eq_lim
nhds_eq_nhds_iff
nhds_le_nhds_iff
-/
