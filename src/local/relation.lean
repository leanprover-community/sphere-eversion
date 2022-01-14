import analysis.calculus.times_cont_diff
import linear_algebra.dual

import to_mathlib.analysis.normed_space.operator_norm
import to_mathlib.topology.misc

import local.ample

/-!
# Local partial differential relations and their formal solutions

This file defines `rel_loc E F`, the type of first order partial differential relations
for maps between two real normed spaces `E` and `F`.

To any `R : rel_loc E F` and `U : set E` we associate the type `sol R U` of maps `f : E → F` of
solutions of `R` over `U`, and its formal counterpart `formal_sol R U`.

The h-principle question is whether we can deform any formal solution into a solution.
The type of deformations is `htpy_formal_sol R U` (homotopies of formal solutions of `R` over
`U`). Implementation note: the time parameter `t` is any real number, but all the homotopies we will
construct will be constant for `t ≤ 0` and `t ≥ 1`. It looks like this imposes more smoothness
constraints at `t = 0` and `t = 1` (requiring flat functions), but this is needed for smooth
concatenations anyway.

This file also defines the ampleness conditions for these relations. Together with openness,
this will guarantee the h-principle (in some other file).
-/

noncomputable theory

open set function

variables (E : Type*) [normed_group E] [normed_space ℝ E] (F : Type*)
                        [normed_group F] [normed_space ℝ F]

local notation `D` := fderiv ℝ
local notation `hull` := convex_hull ℝ
local notation `smooth_on` := times_cont_diff_on ℝ ⊤

open_locale unit_interval

open module (dual)
open_locale classical

local notation u ` ⬝ `:70 φ:65 :=
  continuous_linear_map.comp (continuous_linear_map.to_span_singleton ℝ u) φ


-- TODO: move mathlib's dual_pair out of the root namespace!

/-- A continuous linear form `π` and a vector `v` that pair to one. In particular `ker π` is a
hyperplane and `v` spans a complement of this hyperplane. -/
structure dual_pair' :=
(π : E →L[ℝ] ℝ)
(v : E)
(pairing : π v = 1)

namespace dual_pair'
variables {E F}

local attribute [simp] continuous_linear_map.to_span_singleton_apply

/-- Given a dual pair `p`, `p.span_v` is the line spanned by `p.v`. -/
def span_v (p : dual_pair' E) : submodule ℝ E := submodule.span ℝ {p.v}

/-- Update a continuous linear map `φ : E →L[ℝ] F` using a dual pair `p` on `E` and a
vector `w : F`. The new map coincides with `φ` on `ker p.π` and sends `p.v` to `w`. -/
def update (p : dual_pair' E) (φ : E →L[ℝ] F) (w : F) : E →L[ℝ] F :=
φ + (w - φ p.v) ⬝ p.π

@[simp]
lemma update_ker_pi (p : dual_pair' E) (φ : E →L[ℝ] F) (w : F) {u} (hu : u ∈ p.π.ker) :
  p.update φ w u = φ u :=
begin
  rw continuous_linear_map.mem_ker at hu,
  simp only [update, hu, continuous_linear_map.to_span_singleton_apply, add_zero,
             continuous_linear_map.coe_comp', comp_app, zero_smul, continuous_linear_map.add_apply]
end

@[simp]
lemma update_v (p : dual_pair' E) (φ : E →L[ℝ] F) (w : F) :
  p.update φ w p.v = w :=
by simp only [update, p.pairing, continuous_linear_map.to_span_singleton_apply,
              continuous_linear_map.coe_comp', add_sub_cancel'_right, one_smul, comp_app,
              continuous_linear_map.add_apply]

@[simp]
lemma update_self (p : dual_pair' E) (φ : E →L[ℝ] F)  :
  p.update φ (φ p.v) = φ :=
by simp only [update, add_zero, continuous_linear_map.to_span_singleton_zero,
              continuous_linear_map.zero_comp, sub_self]

end dual_pair'

/-- A first order relation for maps between real vector spaces. -/
def rel_loc := set (E × F × (E →L[ℝ] F))

instance : has_mem (E × F × (E →L[ℝ] F)) (rel_loc E F) := set.has_mem

variables {E F}

namespace rel_loc

/-- The slice of a local relation `R : rel_loc E F` for a dual pair `p` at a jet `θ` is
the set of `w` in `F` such that updating `θ` using `p` and `w` leads to a jet in `R`. -/
def slice (R : rel_loc E F) (p : dual_pair' E) (θ : E × F × (E →L[ℝ] F)) : set F :=
{w | (θ.1, θ.2.1, p.update θ.2.2 w) ∈ R}

/-- A local relation `R` is open over a set `U` if the part of `R` lying over `U`
(for the obvious projection `(E × F × (E →L[ℝ] F)) → E`) is open. -/
def is_open_over (R : rel_loc E F) (U : set E) : Prop :=
is_open (R ∩ U ×ˢ @univ (F × (E →L[ℝ] F)))

/-- A relation is ample if all its slices are ample. -/
def is_ample (R : rel_loc E F) : Prop := ∀ (p : dual_pair' E) (θ : E × F × (E →L[ℝ] F)),
ample_set (R.slice p θ)

/-- A solution to a local relation `R` over a set `U`. -/
@[ext] structure sol (R : rel_loc E F) (U : set E) :=
(f : E → F)
(f_diff : smooth_on f U)
(is_sol : ∀ x ∈ U, (x, f x, D f x) ∈ R)

/-- A formal solution to a local relation `R` over a set `U`. -/
@[ext] structure formal_sol (R : rel_loc E F) (U : set E) :=
(f : E → F)
(f_diff : smooth_on f U)
(φ : E → E →L[ℝ] F)
(φ_diff : smooth_on φ U)
(is_sol : ∀ x ∈ U, (x, f x, φ x) ∈ R)

/-- Inclusion of solutions into formal solutions. -/
def sol.to_formal_sol {R : rel_loc E F} {U : set E} (𝓕 : sol R U) (hU : is_open U) : formal_sol R U :=
{ f := 𝓕.f,
  f_diff := 𝓕.f_diff,
  φ := D 𝓕.f,
  φ_diff := ((times_cont_diff_on_top_iff_fderiv_of_open hU).mp 𝓕.f_diff).2,
  is_sol := 𝓕.is_sol }

end rel_loc

namespace rel_loc.formal_sol

open rel_loc

instance (R : rel_loc E F) (U : set E) : has_coe_to_fun (formal_sol R U) (λ S, E → F × (E →L[ℝ] F)) :=
⟨λ 𝓕, λ x, (𝓕.f x, 𝓕.φ x)⟩

variables {U : set E} {R : rel_loc E F}

/-- The slice associated to a formal solution and a dual pair at some point. -/
def slice_at (𝓕 : formal_sol R U) (p : dual_pair' E) (x : E) : set F :=
R.slice p (x, 𝓕.f x, 𝓕.φ x)

-- This probably won't stay stated like this
def slices (𝓕 : formal_sol R U) (p : dual_pair' E) : set (E × F) :=
⋃ x ∈ U, ({x} : set E) ×ˢ (R.slice p (x, 𝓕.f x, 𝓕.φ x))

/-- A formal solution `𝓕` of `R` is holonomic if its linear map part at `x`
is the derivative of its function part at `x`. -/
def is_holonomic_at (𝓕 : formal_sol R U) (x : E) : Prop := D 𝓕.f x = 𝓕.φ x

lemma _root_.rel_loc.sol.is_holonomic (𝓕 : sol R U) (hU : is_open U) (x : E) :
  (𝓕.to_formal_sol hU).is_holonomic_at x :=
by simp [rel_loc.sol.to_formal_sol, is_holonomic_at]

/-- A formal solution of `R` over `U` that is holonomic at every point of `U`
comes from a genuine solution. -/
def to_sol (𝓕 : formal_sol R U) (h : ∀ x ∈ U, 𝓕.is_holonomic_at x) : sol R U :=
{ f := 𝓕.f,
  f_diff := 𝓕.f_diff,
  is_sol := λ x hx, ((h x hx).symm ▸ (𝓕.is_sol x hx)) }

lemma to_sol_to_formal_sol (𝓕 : sol R U) (hU : is_open U) :
  (𝓕.to_formal_sol hU).to_sol (λ x hx, 𝓕.is_holonomic hU x) = 𝓕 :=
by { ext x, refl }

/-- A formal solution `𝓕` of `R` is partially holonomic in the direction of some subspace `E'`
if its linear map part at `x` is the derivative of its function part at `x` in restriction to
`E'`. -/
def is_part_holonomic_at (𝓕 : formal_sol R U) (E' : submodule ℝ E) (x : E) :=
∀ v ∈ E', D 𝓕.f x v = 𝓕.φ x v

lemma mem_slice (𝓕 : formal_sol R U) (p : dual_pair' E) {x : E} (hx : x ∈ U) :
  𝓕.φ x p.v ∈ 𝓕.slice_at p x :=
by simp [slice_at, rel_loc.slice, 𝓕.is_sol x hx]

/-- A formal solution `𝓕` is short for a dual pair `p` at a point `x` if the derivative of
the function `𝓕.f` at `x` is in the convex hull of the relevant connected component of the
corresponding slice. -/
def is_short_at (𝓕 : formal_sol R U) (p : dual_pair' E) (x : E) : Prop :=
D 𝓕.f x p.v ∈ hull (connected_comp_in (𝓕.slice_at p x) $ 𝓕.φ x p.v)

end rel_loc.formal_sol

section htpy_formal_sol

open rel_loc

/-- A homotopy of formal solutions to `R` over a set `U`. -/
structure htpy_formal_sol (R : rel_loc E F) (U : set E) :=
(f : ℝ → E → F)
(f_diff : smooth_on (uncurry f) (@univ ℝ ×ˢ U))
(φ : ℝ → E → E →L[ℝ] F)
(φ_diff : smooth_on (uncurry φ) (@univ ℝ ×ˢ U))
(is_sol : ∀ t, ∀ x ∈ U, (x, f t x, φ t x) ∈ R)

variables {U : set E} {R : rel_loc E F}

instance : has_coe_to_fun (htpy_formal_sol R U) (λ S, ℝ → formal_sol R U) :=
⟨λ S t,
 { f := S.f t,
   f_diff := sorry,
   φ := S.φ t,
   φ_diff := sorry,
   is_sol := λ x hx, S.is_sol t x hx }⟩

/-- The constant homotopy of formal solutions at a given formal solution. It will be used
as junk value for constructions of formal homotopies that need additional assumptions. -/
def rel_loc.formal_sol.const_htpy (𝓕 : formal_sol R U) : htpy_formal_sol R U :=
{ f := λ t, 𝓕.f,
  f_diff := sorry,
  φ := λ t, 𝓕.φ,
  φ_diff := sorry,
  is_sol := λ t, 𝓕.is_sol }


-- The next gadget is probably already in mathlib somewhere (the precise values 1/4 and 3/4 are
-- not important)

/-- A smooth step function on `ℝ`, equal to `0` before `1/4` and `1` after `3/4`. -/
def smooth_step : ℝ → ℝ := sorry

lemma smooth_step.smooth : times_cont_diff ℝ ⊤ smooth_step :=
sorry

lemma smooth_step.of_lt {t : ℝ} (h : t < 1/4) : smooth_step t = 0 :=
sorry

lemma smooth_step.of_gt {t : ℝ} (h : 3/4 < t) : smooth_step t = 1 :=
sorry

/-- Concatenation of homotopies of formal solution. The result depend on our choice of
a smooth step function in order to keep smoothness with respect to the time parameter. -/
def rel_loc.htpy_formal_sol.comp (𝓕 𝓖 : htpy_formal_sol R U) : htpy_formal_sol R U :=
{ f := λ t x, if t ≤ 1/2 then 𝓕.f (smooth_step $ 2*t) x else  𝓖.f (smooth_step $ 2*t - 1) x,
  f_diff := sorry,
  φ := λ t x, if t ≤ 1/2 then 𝓕.φ (smooth_step $ 2*t) x else  𝓖.φ (smooth_step $ 2*t - 1) x,
  φ_diff := sorry,
  is_sol := sorry }

end htpy_formal_sol
