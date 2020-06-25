import data.real.basic
import linear_algebra.basic
import linear_algebra.finite_dimensional
import category_theory.endomorphism
import topology.algebra.module
import topology.instances.real
import analysis.convex.caratheodory

noncomputable theory

-- This is intended as a Lean roadmap for the `int_cvx` lemma, currently Lemma 1.5 of loops.tex.
-- Rather than a "human readable" proof of a single lemma,
-- it is a longer sequence of lemmas, facts, and constructions, for now all sorried.

-- TODO everything in this file could be generalised to arbitrary affine spaces over ℝ.
-- The development of convexity in mathlib is being ported to the affine setting,
-- and work on this could either occur in parallel, or wait under that is settled.
variables {V : Type*} [add_comm_group V] [vector_space ℝ V]

/-- The dilation about `c` with scale factor `r`. -/
def dilation (c : V) (r : ℝ) : V → V := λ v, r • (v - c) + c

/-- The dilations about `c` give a multiplicative homomorphism from ℝ to End V. -/
-- In fact, dilations preserve the affine structure,
-- so one could strengthen this to `ℝ →* End (Aff.of V)`,
-- if we define `Aff`.
@[simps]
def dilations (c : V) : ℝ →* category_theory.End V :=
{ to_fun := dilation c,
  map_one' :=
  begin
    dsimp [dilation],
    ext1 v,
    simp,
  end,
  map_mul' := λ x y,
  begin
    ext1 v,
    change (x * y) • (v - c) + c = x • (y • (v - c) + c - c) + c,
    simp [mul_smul],
  end }

/-- A dilation with nonzero scale factor gives an equivalence. -/
-- This is an easy consequence of the homomorphism property.
@[simps]
def dilation.equiv (c : V) (r : ℝ) (h : r ≠ 0) : V ≃ V :=
{ to_fun := dilations c r,
  inv_fun := dilations c r⁻¹,
  left_inv := λ v,
  begin
    apply (congr_fun ((dilations c).map_mul r⁻¹ r) v).symm.trans _,
    rw inv_mul_cancel h,
    simp,
  end,
  right_inv := λ v,
  begin
    apply (congr_fun ((dilations c).map_mul r r⁻¹) v).symm.trans _,
    rw mul_inv_cancel h,
    simp,
  end }

open_locale big_operators

-- move this to mathlib
section patch
variables {E : Type*} {F : Type*} {ι : Type*}
  [add_comm_group E] [vector_space ℝ E]
variables (i j : ι) (c : ℝ) (t : finset ι) (w : ι → ℝ) (z : ι → E)

example (a b : ℝ) : ∑ (i : ι) in t, c • z i = c • ∑ (i : ι) in t, z i :=
begin
  exact finset.smul_sum.symm
end
lemma finset.center_mass_add (k : E) (h : ∑ j in t, w j ≠ 0) :
  t.center_mass w (λ i, z i + k) = t.center_mass w z + k :=
by simp only [finset.center_mass, finset.sum_add_distrib, smul_add, ← finset.sum_smul,
              (mul_smul _ _ k).symm, inv_mul_cancel h, one_smul]
lemma finset.center_mass_sub (k : E) (h : ∑ j in t, w j ≠ 0) :
  t.center_mass w (λ i, z i - k) = t.center_mass w z - k :=
finset.center_mass_add _ _ _ (-k) h

lemma finset.center_mass_mul (c : ℝ) (h : c ≠ 0) :
  t.center_mass (λ x, c * w x) z = t.center_mass w z :=
begin
  simp only [finset.center_mass, mul_smul],
  rw [← finset.smul_sum, ← mul_smul, ← finset.mul_sum, mul_inv_rev', mul_assoc, inv_mul_cancel h, mul_one],
end

end patch

/--
Given a formula for `x` as a weighted center of mass of a finset `t`,
we give the formula for `x` as a weighted center of mass of `t` dilated by `r` about `c`,
plus a multiple of `c`.

We'll shortly specialise this to the case `c = barycenter t`.
-/
lemma quux (x : V) (t : finset V) (f : V → ℝ) (h : t.center_mass f id = x) (r : ℝ) (c : V) :
  t.center_mass (λ x, r⁻¹ * f x) (dilation c r) + (∑ z in t, (1 - r⁻¹) * f z) • c = x :=
sorry

variables [topological_space V]
  [topological_add_group V] [topological_vector_space ℝ V]

lemma dilation.continuous {c : V} {r : ℝ} : continuous (dilation c r) :=
(continuous_const.smul (continuous_id.add continuous_const)).add continuous_const

lemma foo {c x : V} {s : set V} (h : is_open s) (hx : x ∈ s) :  ∃ ε > (0:ℝ), dilation c (1+ε) x ∈ s :=
sorry

def barycenter (s : finset V) : V := s.center_mass 1 id
lemma barycenter_mem {s : finset V} (h : s.nonempty) : barycenter s ∈ convex_hull (↑s : set V) :=
begin
  apply finset.center_mass_mem_convex_hull _ _ _ _,
  { intros, norm_num },
  { simp only [mul_one, finset.sum_const, nsmul_eq_mul, pi.one_apply, nat.cast_pos],
    rwa finset.card_pos },
  { simp }
end

lemma aa (s : finset V) (r : ℝ) (h : r ≠ 0) :
  barycenter (s.map (dilation.equiv (barycenter s) r h).to_embedding) = barycenter s :=
sorry

/--
Given a formula for `x` as a weighted center of mass of a finset `t`,
we give the formula for `x` as a weighted center of mass of
the finset `t` dilated by `r` about its barycenter.
-/
lemma quux' (x : V) (t : finset V) (f : V → ℝ) (w : t.sum f = 1) (h : t.center_mass f id = x) (r : ℝ) :
  t.center_mass (λ x, r⁻¹ * f x + (1 - r⁻¹) / (t.card)) (λ x, dilation (barycenter t) r x) = x :=
sorry

def affine_independent (ι : Type*) (f : ι → V) : Prop :=
  ∀ s : finset ι, ∀ g : ι → ℝ, ∑ i in s, g i • f i = 0 → ∑ i in s, g i = 0 → ∀ i ∈ s, g i = 0

lemma affine_independent_of_linear_independent (ι : Type*) (f : ι → V) :
  linear_independent ℝ f → affine_independent ι f :=
begin
  rw linear_independent_iff',
  intros h s g h₁ h₂,
  apply h,
  apply h₁
end

def set.affine_independent (s : set V) : Prop := affine_independent (subtype s) subtype.val

-- TODO if a set is affine_independent, then its dilation about any center with `r ≠ 0` is too.

variables [finite_dimensional ℝ V]
open finite_dimensional

-- TODO the lemma characterising
-- the interior of the convex hull of a finset of size `d + 1`
-- as the strictly positive affine combinations of the points, if the finset is affine independent,
-- or empty otherwise

lemma interior_convex_hull_empty_of_card_le_dim
  (s : finset V) (b : s.card ≤ findim ℝ V) :
  interior (convex_hull (↑s : set V)) = ∅ :=
sorry

section
open_locale classical

lemma interior_convex_hull_eq_of_card_eq_dim_add_one
  (s : finset V) (b : s.card = findim ℝ V + 1) :
  interior (convex_hull (↑s : set V)) =
  if (↑s : set V).affine_independent then
    {x : V | ∃ (f : V → ℝ) (hw₀ : ∀ y ∈ s, 0 < f y) (hw₁ : s.sum f = 1),
      s.center_mass f id = x}
  else ∅ :=
sorry

end

lemma convex_hull_subset_int_convex_hull_dilation
  (s : finset V) (w : (↑s : set V).affine_independent) (ε : ℝ) (h : 0 < ε) :
  convex_hull (↑s : set V) ⊆
    interior (convex_hull
      (↑(s.map (dilation.equiv (barycenter s) (1+ε) sorry).to_embedding) : set V)) :=
-- This is now hopefully just plumbing the previous lemmas together.
sorry

lemma convex_hull_eq_union_interior {s : set V} (h : is_open s) :
  convex_hull s =
    ⋃ (t : finset V) (h : ↑t ⊆ s) (b : t.card = findim ℝ V + 1), interior (convex_hull (↑t : set V)) :=
-- We write `convex_hull s` as the union of convex hulls of finsets with cardinality at most dim V + 1.
-- Given a point `x ∈ convex_hull s`, by Caratheodory `x` is in the convex hull of some finset in `s`
-- with cardinality at most `dim V + 1`.
-- Discard any unused points,
-- replacing them to make an affine independent set of size exactly `dim V + 1`, still in `s`.
-- Pick an epsilon so the dilation of this set around its barycenter is still in `s`.
-- By the previous lemma `x` is in the interior of the convex hull of this dilated set.
sorry

/--
This is the explicit version of `convex_hull_eq_union_interior`,
unfolding the definitions to give an explicit formula for `x`
with positive coefficients.

This is `lem:int_cvx` from the blueprint.
-/
theorem eq_strict_center_mass_card_eq_dim_succ_of_mem_convex_hull_open
  {s : set V} (o : is_open s) {x : V} (h : x ∈ convex_hull s) :
  ∃ (t : finset V) (w : ↑t ⊆ s) (b : t.card = findim ℝ V + 1)
    (f : V → ℝ), (∀ y ∈ t, 0 < f y) ∧ t.sum f = 1 ∧ t.center_mass f id = x :=
begin
  classical,
  rw convex_hull_eq_union_interior o at h,
  simp only [exists_prop, set.mem_Union] at h,
  obtain ⟨t, w, b, m⟩ := h,
  rw interior_convex_hull_eq_of_card_eq_dim_add_one _ b at m,
  split_ifs at m,
  { simp only [exists_prop, set.mem_set_of_eq] at m,
    obtain ⟨f, c⟩ := m,
    exact ⟨t, w, b, f, c⟩, },
  { simpa using m, },
end
