import algebra.periodic
import analysis.normed_space.basic

import to_mathlib.topology.tsupport
/-!

# Boundedness property of periodic function

The main purpose of that file it to prove
```
lemma continuous.bounded_of_one_periodic_of_compact {f : X → ℝ → E} (cont : continuous ↿f)
  (hper : ∀ x, one_periodic (f x)) {K : set X} (hK : is_compact K) (hfK : ∀ x ∉ K, f x = 0) :
  ∃ C, ∀ x t, ∥f x t∥ ≤ C
```

This is done by introducing the quotient 𝕊₁ = ℝ/ℤ as a compact topological space. Patrick is not sure
this is the optimal version.

In the first part, generalize many lemmas to any period and add to algebra/periodic.lean?

-/


noncomputable theory

open set function  filter topological_space int
open_locale topological_space


section one_periodic

variables {α : Type*}

def ℤ_sub_ℝ : add_subgroup ℝ := add_monoid_hom.range (int.cast_add_hom ℝ)

def trans_one : setoid ℝ := quotient_add_group.left_rel ℤ_sub_ℝ

def one_periodic (f : ℝ → α) : Prop := periodic f 1

lemma one_periodic.add_nat {f : ℝ → α} (h : one_periodic f) : ∀ k : ℕ, ∀ x, f (x + k) = f x :=
begin
  intros k x,
  induction k with k hk,
  { simp },
  change f (x + (k + 1)) = _,
  rw [← hk, ← add_assoc, h]
end

lemma one_periodic.add_int {f : ℝ → α} (h : one_periodic f) : ∀ k : ℤ, ∀ x, f (x + k) = f x :=
begin
  intros k x,
  induction k with k k,
  { erw h.add_nat },
  have : x + -[1+ k] + (k + 1 : ℕ) = x, by { simp, ring },
  rw [← h.add_nat (k+1) (x + -[1+ k]), this]
end

/-- The circle `𝕊₁ := ℝ/ℤ`. -/
@[derive [topological_space, inhabited]]
def 𝕊₁ := quotient trans_one

lemma trans_one_rel_iff {a b : ℝ} : trans_one.rel a b ↔ ∃ k : ℤ, b = a + k :=
begin
  apply exists_congr,
  intro k,
  change (k : ℝ) = _ ↔ _,
  split ; intro h ; linarith [h]
end

section
local attribute [instance] trans_one

def proj_𝕊₁ : ℝ → 𝕊₁ := quotient.mk

@[simp]
lemma proj_𝕊₁_add_int (t : ℝ) (k : ℤ) : proj_𝕊₁ (t + k) = proj_𝕊₁ t :=
begin
  symmetry,
  apply quotient.sound,
  exact (trans_one_rel_iff.mpr ⟨k, rfl⟩)
end

def 𝕊₁.repr (x : 𝕊₁) : ℝ := let t := quotient.out x in fract t

lemma 𝕊₁.repr_mem (x : 𝕊₁) : x.repr ∈ (Ico 0 1 : set ℝ) :=
⟨fract_nonneg _, fract_lt_one _⟩

lemma 𝕊₁.proj_repr (x : 𝕊₁) : proj_𝕊₁ (x.repr) = x :=
begin
  symmetry,
  conv_lhs { rw ← quotient.out_eq x },
  rw ← fract_add_floor (quotient.out x),
  apply proj_𝕊₁_add_int
end

lemma image_proj_𝕊₁_Ico : proj_𝕊₁ '' (Ico 0 1) = univ :=
begin
  rw eq_univ_iff_forall,
  intro x,
  use [x.repr, x.repr_mem, x.proj_repr],
end

lemma image_proj_𝕊₁_Icc : proj_𝕊₁ '' (Icc 0 1) = univ :=
eq_univ_of_subset (image_subset proj_𝕊₁ Ico_subset_Icc_self) image_proj_𝕊₁_Ico

@[continuity]
lemma continuous_proj_𝕊₁ : continuous proj_𝕊₁ := continuous_quotient_mk

lemma is_open_map_proj_𝕊₁ : is_open_map proj_𝕊₁ :=
quotient_add_group.is_open_map_coe ℤ_sub_ℝ

lemma quotient_map_id_proj_𝕊₁ {X : Type*} [topological_space X] :
  quotient_map (λ p : X × ℝ, (p.1, proj_𝕊₁ p.2)) :=
(is_open_map.id.prod is_open_map_proj_𝕊₁).to_quotient_map (continuous_id.prod_map continuous_proj_𝕊₁)
  (surjective_id.prod_map quotient.exists_rep)


def one_periodic.lift {f : ℝ → α} (h : one_periodic f) : 𝕊₁ → α :=
quotient.lift f (by { intros a b hab, rcases trans_one_rel_iff.mp hab with ⟨k, rfl⟩, rw h.add_int })

end

local notation `π` := proj_𝕊₁

instance : compact_space 𝕊₁ :=
⟨by { rw ← image_proj_𝕊₁_Icc, exact is_compact_Icc.image continuous_proj_𝕊₁ }⟩

variables {X E : Type*} [topological_space X] [normed_group E]

lemma continuous.bounded_of_one_periodic_of_compact {f : X → ℝ → E} (cont : continuous ↿f)
  (hper : ∀ x, one_periodic (f x)) {K : set X} (hK : is_compact K) (hfK : ∀ x ∉ K, f x = 0) :
  ∃ C, ∀ x t, ∥f x t∥ ≤ C :=
begin
  let F : X × 𝕊₁ → E := λ p : X × 𝕊₁, (hper p.1).lift p.2,
  have Fcont : continuous F,
  { have qm : quotient_map (λ p : X × ℝ, (p.1, π p.2)) := quotient_map_id_proj_𝕊₁,
    let φ := ↿f, -- avoid weird elaboration issue
    have : φ = F ∘ (λ p : X × ℝ, (p.1, π p.2)), by { ext p, refl },
    dsimp [φ] at this,
    rwa [this,  ← qm.continuous_iff] at cont },
  have hFK : ∀ x : X × 𝕊₁, x ∉ (K.prod (univ : set 𝕊₁)) → F x = 0,
  { rintros ⟨x, ⟨t⟩⟩ hxt,
    have : ∀ a, f x a = 0, by simpa using congr_fun (hfK x $ λ hx, hxt (by simp [hx])),
    apply this },
  obtain ⟨C, hC⟩ : ∃ C, ∀ (x : X × 𝕊₁), ∥F x∥ ≤ C :=
    Fcont.bounded_of_vanishing_outside_compact (hK.prod compact_univ) hFK,
  exact ⟨C, λ x t, hC (x, π t)⟩,
end

end one_periodic