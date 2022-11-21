import algebra.periodic
import analysis.normed_space.basic

import to_mathlib.topology.separation

/-!

# Boundedness property of periodic function

The main purpose of that file it to prove
```
lemma continuous.bounded_of_one_periodic_of_compact {f : X → ℝ → E} (cont : continuous ↿f)
  (hper : ∀ x, one_periodic (f x)) {K : set X} (hK : is_compact K) (hfK : ∀ x ∉ K, f x = 0) :
  ∃ C, ∀ x t, ‖f x t‖ ≤ C
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

/-- The integers as an additive subgroup of the reals. -/
def ℤ_sub_ℝ : add_subgroup ℝ := add_monoid_hom.range (int.cast_add_hom ℝ)

/-- The equivalence relation on `ℝ` corresponding to its partition as cosets of `ℤ`. -/
def trans_one : setoid ℝ := quotient_add_group.left_rel ℤ_sub_ℝ

/-- The proposition that a function on `ℝ` is periodic with period `1`. -/
def one_periodic (f : ℝ → α) : Prop := periodic f 1

lemma one_periodic.add_nat {f : ℝ → α} (h : one_periodic f) : ∀ k : ℕ, ∀ x, f (x + k) = f x :=
begin
  intros k x,
  induction k with k hk,
  { simp },
  rw [nat.cast_succ, ← add_assoc, h, hk]
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
  refine quotient_add_group.left_rel_apply.trans _,
  refine exists_congr (λ k, _),
  rw [coe_cast_add_hom, eq_neg_add_iff_add_eq, eq_comm]
end

section
local attribute [instance] trans_one

/-- The quotient map from the reals to the circle `ℝ ⧸ ℤ`. -/
def proj_𝕊₁ : ℝ → 𝕊₁ := quotient.mk

@[simp]
lemma proj_𝕊₁_add_int (t : ℝ) (k : ℤ) : proj_𝕊₁ (t + k) = proj_𝕊₁ t :=
begin
  symmetry,
  apply quotient.sound,
  exact (trans_one_rel_iff.mpr ⟨k, rfl⟩)
end

/-- The unique representative in the half-open interval `[0, 1)` for each coset of `ℤ` in `ℝ`,
regarded as a map from the circle `𝕊₁ → ℝ`. -/
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

/-- A one-periodic function on `ℝ` descends to a function on the circle `ℝ ⧸ ℤ`. -/
def one_periodic.lift {f : ℝ → α} (h : one_periodic f) : 𝕊₁ → α :=
quotient.lift f (by { intros a b hab, rcases trans_one_rel_iff.mp hab with ⟨k, rfl⟩, rw h.add_int })

end

local notation `π` := proj_𝕊₁

instance : compact_space 𝕊₁ :=
⟨by { rw ← image_proj_𝕊₁_Icc, exact is_compact_Icc.image continuous_proj_𝕊₁ }⟩

lemma is_closed_int : is_closed (range (coe : ℤ → ℝ)) :=
begin
  refine is_closed_of_spaced_out (metric.uniformity_basis_dist.mem_of_mem $ zero_lt_one) _,
  rintros - ⟨p, rfl⟩ - ⟨q, rfl⟩ h (H : dist p q < 1),
  rw [int.dist_eq] at H,
  norm_cast at *,
  exact h (eq_of_sub_eq_zero $ int.abs_lt_one_iff.mp H)
end

instance : t2_space 𝕊₁ :=
begin
  have πcont : continuous π, from continuous_quotient_mk,
  rw t2_space_iff_of_continuous_surjective_open πcont quotient.surjective_quotient_mk' is_open_map_proj_𝕊₁,
  have : {q : ℝ × ℝ | π q.fst = π q.snd} = {q : ℝ × ℝ | ∃ k : ℤ, q.2 = q.1 + k},
  { ext ⟨a, b⟩,
    simp only [proj_𝕊₁, quotient.eq, mem_set_of_eq],
    exact trans_one_rel_iff },
  have : {q : ℝ × ℝ | π q.fst = π q.snd} = (λ q : ℝ × ℝ , q.2 - q.1) ⁻¹' (range $ (coe : ℤ → ℝ)),
  { rw this,
    ext ⟨a, b⟩,
    apply exists_congr (λ k, _),
    conv_rhs {rw [eq_comm, sub_eq_iff_eq_add'] } },
  rw this,
  exact is_closed.preimage (continuous_snd.sub continuous_fst) is_closed_int
end

variables {X E : Type*} [topological_space X] [normed_add_comm_group E]

lemma continuous.bounded_on_compact_of_one_periodic {f : X → ℝ → E} (cont : continuous ↿f)
  (hper : ∀ x, one_periodic (f x)) {K : set X} (hK : is_compact K) :
  ∃ C, ∀ x ∈ K, ∀ t, ‖f x t‖ ≤ C :=
begin
  let F : X × 𝕊₁ → E := λ p : X × 𝕊₁, (hper p.1).lift p.2,
  have Fcont : continuous F,
  { have qm : quotient_map (λ p : X × ℝ, (p.1, π p.2)) := quotient_map_id_proj_𝕊₁,
    let φ := ↿f, -- avoid weird elaboration issue
    have : φ = F ∘ (λ p : X × ℝ, (p.1, π p.2)), by { ext p, refl },
    dsimp [φ] at this,
    rwa [this,  ← qm.continuous_iff] at cont },
  obtain ⟨C, hC⟩ := (hK.prod is_compact_univ).bdd_above_image (continuous_norm.comp Fcont).continuous_on,
  exact ⟨C, λ x x_in t, hC ⟨(x, π t), ⟨x_in, mem_univ _⟩, rfl⟩⟩
end

lemma continuous.bounded_of_one_periodic_of_compact {f : X → ℝ → E} (cont : continuous ↿f)
  (hper : ∀ x, one_periodic (f x)) {K : set X} (hK : is_compact K) (hfK : ∀ x ∉ K, f x = 0) :
  ∃ C, ∀ x t, ‖f x t‖ ≤ C :=
begin
  obtain ⟨C, hC⟩ := cont.bounded_on_compact_of_one_periodic hper hK,
  use max C 0,
  intros x t,
  by_cases hx : x ∈ K,
  { exact le_max_of_le_left (hC x hx t) },
  { simp [hfK, hx] },
end


end one_periodic
