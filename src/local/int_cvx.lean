import data.real.basic
import linear_algebra.basic
import linear_algebra.finite_dimensional
import category_theory.endomorphism
import topology.algebra.module
import topology.instances.real
import analysis.convex.basic

-- This is intended as a Lean roadmap for the `int_cvx` lemma, currently Lemma 1.5 of loops.tex.
-- Rather than a "human readable" proof of a single lemma,
-- it is a longer sequence of lemmas, facts, and constructions, for now all sorried.

-- TODO everything in this file could be generalised to arbitrary affine spaces over ℝ.
variables {V : Type*} [add_comm_group V] [vector_space ℝ V]

/-- The dilation about `c` with scale factor `r`. -/
def dilation (c : V) (r : ℝ) : V → V := sorry

/-- The dilations about `c` give a multiplicative homomorphism from ℝ to End V. -/
-- In fact, dilations preserve the affine structure,
-- so one could strengthen this to `ℝ →* End (Aff.of V)`,
-- if we define `Aff`.
def dilations (c : V) : ℝ →* category_theory.End V := sorry

-- TODO The @[simp] lemma that this agrees with `dilation`.

/-- A dilation with nonzero scale factor gives an equivalence. -/
-- This is an easy consequence of the homomorphism property.
def dilation.equiv (c : V) (r : ℝ) (h : r ≠ 0) : V ≃ V := sorry

-- TODO The @[simp] lemma that this agrees with dilation.

open_locale big_operators

/-- 
Given a formula for `x` as a weighted center of mass of a finset `t`,
we give the formula for `x` as a weighted center of mass of `t` dilated by `r` about `c`,
plus a multiple of `c`.

We'll shortly specialise this to the case `c = barycenter t`.
-/
lemma quux (x : V) (t : finset V) (f : V → ℝ) (h : t.center_mass f id = x) (r : ℝ) (c : V) :
  t.center_mass (λ x, r⁻¹ * f x) (λ x, dilation c r x) + (∑ z in t, (1 - r⁻¹) * f z) • c = x :=
sorry

variables [topological_space V]
  [topological_add_group V] [topological_vector_space ℝ V]

lemma dilation.continuous {c : V} {r : ℝ} : continuous (dilation c r) := sorry

lemma foo {c x : V} {s : set V} (h : is_open s) : ∃ ε : ℝ, ε > 0 ∧ dilation c (1+ε) x ∈ s := sorry

-- TODO if a finset is contained in an open set, then for any center `c` there is some ε > 0
-- so its dilation by (1+ε) is still in that open set.

def barycenter (s : finset V) : V := sorry
lemma barycenter_mem {s : finset V} : barycenter s ∈ convex_hull (↑s : set V) := sorry

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

def affine_independent (s : finset V) : Prop := sorry

-- TODO if a finset is affine_independent, then its dilation about any center with `r ≠ 0` is too.

variables [finite_dimensional ℝ V]
open finite_dimensional

-- TODO the lemma characterising 
-- the interior of the convex hull of a finset of size `d + 1`
-- as the strictly positive affine combinations of the points, if the finset is affine independent,
-- or empty otherwise

lemma convex_hull_subset_int_convex_hull_dilation 
  (s : finset V) (w : affine_independent s) (ε : ℝ) (h : 0 < ε) :
  convex_hull (↑s : set V) ⊆ 
    interior (convex_hull 
      (↑(s.map (dilation.equiv (barycenter s) (1+ε) sorry).to_embedding) : set V)) := 
-- This is now hopefully just plumbing the previous lemmas together.      
sorry

lemma int_cvx (s : set V) (h : is_open s) :
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