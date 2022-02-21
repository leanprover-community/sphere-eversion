import analysis.calculus.times_cont_diff
import linear_algebra.dual
import topology.metric_space.hausdorff_distance

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
The type of deformations is `htpy_jet_sec R U` (homotopies of formal solutions of `R` over
`U`). Implementation note: the time parameter `t` is any real number, but all the homotopies we will
construct will be constant for `t ≤ 0` and `t ≥ 1`. It looks like this imposes more smoothness
constraints at `t = 0` and `t = 1` (requiring flat functions), but this is needed for smooth
concatenations anyway.

This file also defines the ampleness conditions for these relations. Together with openness,
this will guarantee the h-principle (in some other file).
-/

noncomputable theory

open set function module (dual)
open_locale unit_interval topological_space

variables (E : Type*) [normed_group E] [normed_space ℝ E] (F : Type*)
                        [normed_group F] [normed_space ℝ F]

local notation `D` := fderiv ℝ
local notation `hull` := convex_hull ℝ
local notation `smooth_on` := times_cont_diff_on ℝ ⊤

-- `∀ᶠ x near s, p x` means property `p` holds at every point in a neighborhood of the set `s`.
local notation `∀ᶠ` binders ` near ` s `, ` r:(scoped p, filter.eventually p $ 𝓝ˢ s) := r

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

/-- Given a finite basis `e : basis ι ℝ E`, and `i : ι`, `e.dual_pair' i`
is given by the `i`th basis element and its dual. -/
def _root_.basis.dual_pair' [finite_dimensional ℝ E] {ι : Type*} [fintype ι] [decidable_eq ι]
  (e : basis ι ℝ E) (i : ι) : dual_pair' E :=
{ π := (e.dual_basis i).to_continuous_linear_map,
  v := e i,
  pairing := by simp only [basis.coord_apply, finsupp.single_eq_same, basis.repr_self,
                           linear_map.coe_to_continuous_linear_map', basis.coe_dual_basis] }

end dual_pair'

@[derive metric_space]
def one_jet := E × F × (E →L[ℝ] F)

/-- A first order relation for maps between real vector spaces. -/
def rel_loc := set (one_jet E F)

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

lemma is_open_over.exists_thickening {R : rel_loc E F} {U : set E} (h : R.is_open_over U)
  {K : set $ one_jet E F} (hK : is_compact K) (hK' : K ⊆ R ∩ U ×ˢ @univ (F × (E →L[ℝ] F))) :
∃ ε > 0, metric.thickening ε K ⊆ R :=
begin

  sorry
end

/-- A relation is ample if all its slices are ample. -/
def is_ample (R : rel_loc E F) : Prop := ∀ (p : dual_pair' E) (θ : E × F × (E →L[ℝ] F)),
ample_set (R.slice p θ)

/-- A solution to a local relation `R` over a set `U`. -/
@[ext] structure sol (R : rel_loc E F) (U : set E) :=
(f : E → F)
(f_diff : smooth_on f U)
(is_sol : ∀ x ∈ U, (x, f x, D f x) ∈ R)

@[ext] structure jet_sec (U : set E) (F : Type*) [normed_group F] [normed_space ℝ F] :=
(f : E → F)
(f_diff : smooth_on f U)
(φ : E → E →L[ℝ] F)
(φ_diff : smooth_on φ U)

def jet_sec.is_formal_sol {U : set E} (𝓕 : jet_sec U F) (R : rel_loc E F) : Prop :=
∀ x ∈ U, (x, 𝓕.f x, 𝓕.φ x) ∈ R

/-- A formal solution to a local relation `R` over a set `U`. -/
@[ext] structure formal_sol (R : rel_loc E F) (U : set E) extends jet_sec U F :=
(is_sol : ∀ x ∈ U, (x, f x, φ x) ∈ R)

instance (R : rel_loc E F) (U : set E) : has_coe (formal_sol R U) (jet_sec U F):=
⟨formal_sol.to_jet_sec⟩

@[simp] lemma formal_sol.to_jet_sec_eq_coe {U : set E} {R : rel_loc E F} (𝓕 : formal_sol R U) :
𝓕.to_jet_sec = (𝓕 : jet_sec U F) := rfl

@[simp] lemma formal_sol.coe_is_formal_sol {U : set E} {R : rel_loc E F} (𝓕 : formal_sol R U) :
  (𝓕 : jet_sec U F).is_formal_sol R := 𝓕.is_sol

def jet_sec.is_formal_sol.formal_sol {U : set E} {𝓕 : jet_sec U F} {R : rel_loc E F}
  (h : 𝓕.is_formal_sol R) : formal_sol R U :=
{is_sol := h, ..𝓕}

/-- Inclusion of solutions into formal solutions. -/
def sol.to_formal_sol {R : rel_loc E F} {U : set E} (𝓕 : sol R U) (hU : is_open U) : formal_sol R U :=
{ f := 𝓕.f,
  f_diff := 𝓕.f_diff,
  φ := D 𝓕.f,
  φ_diff := ((times_cont_diff_on_top_iff_fderiv_of_open hU).mp 𝓕.f_diff).2,
  is_sol := 𝓕.is_sol }

end rel_loc

namespace rel_loc.jet_sec

open rel_loc

instance (U : set E) : has_coe_to_fun (jet_sec U F) (λ S, E → F × (E →L[ℝ] F)) :=
⟨λ 𝓕, λ x, (𝓕.f x, 𝓕.φ x)⟩

instance (R : rel_loc E F) (U : set E) : has_coe_to_fun (formal_sol R U) (λ S, E → F × (E →L[ℝ] F)) :=
⟨λ 𝓕, λ x, (𝓕.f x, 𝓕.φ x)⟩

@[simp] lemma formal_sol.coe_apply {U : set E} {R : rel_loc E F} (𝓕 : formal_sol R U) (x : E) :
(𝓕 : jet_sec U F) x = 𝓕 x := rfl

variables {U : set E} {R : rel_loc E F}

/-- The slice associated to a jet section and a dual pair at some point. -/
def slice_at (𝓕 : jet_sec U F) (R : rel_loc E F) (p : dual_pair' E) (x : E) : set F :=
R.slice p (x, 𝓕.f x, 𝓕.φ x)

/-- The slice associated to a formal solution and a dual pair at some point. -/
def _root_.rel_loc.formal_sol.slice_at (𝓕 : formal_sol R U) (p : dual_pair' E) (x : E) : set F :=
R.slice p (x, 𝓕.f x, 𝓕.φ x)

-- This probably won't stay stated like this
def slices (𝓕 : jet_sec U F) (R : rel_loc E F) (p : dual_pair' E) : set (E × F) :=
⋃ x ∈ U, ({x} : set E) ×ˢ (R.slice p (x, 𝓕.f x, 𝓕.φ x))

/-- A jet section `𝓕` is holonomic if its linear map part at `x`
is the derivative of its function part at `x`. -/
def is_holonomic_at (𝓕 : jet_sec U F) (x : E) : Prop := D 𝓕.f x = 𝓕.φ x

def _root_.rel_loc.formal_sol.is_holonomic_at (𝓕 : formal_sol R U) (x : E) : Prop := D 𝓕.f x = 𝓕.φ x

lemma _root_.rel_loc.formal_sol.is_holonomic_at_congr (𝓕 𝓕' : formal_sol R U) {s : set E}
  (h : ∀ᶠ x near s, 𝓕 x = 𝓕' x) : ∀ᶠ x near s, 𝓕.is_holonomic_at x ↔ 𝓕'.is_holonomic_at x :=
sorry

lemma _root_.rel_loc.sol.is_holonomic {R : rel_loc E F} (𝓕 : sol R U) (hU : is_open U) (x : E) :
  (𝓕.to_formal_sol hU).is_holonomic_at x :=
by simp [rel_loc.sol.to_formal_sol, rel_loc.formal_sol.is_holonomic_at]

/-- A formal solution of `R` over `U` that is holonomic at every point of `U`
comes from a genuine solution. -/
def _root_.rel_loc.formal_sol.to_sol (𝓕 : formal_sol R U) (h : ∀ x ∈ U, 𝓕.to_jet_sec.is_holonomic_at x) : sol R U :=
{ f := 𝓕.f,
  f_diff := 𝓕.f_diff,
  is_sol := λ x hx, ((h x hx).symm ▸ (𝓕.is_sol x hx)) }

lemma to_sol_to_formal_sol (𝓕 : sol R U) (hU : is_open U) :
  (𝓕.to_formal_sol hU).to_sol (λ x hx, 𝓕.is_holonomic hU x) = 𝓕 :=
by { ext x, refl }

/-- A formal solution `𝓕` of `R` is partially holonomic in the direction of some subspace `E'`
if its linear map part at `x` is the derivative of its function part at `x` in restriction to
`E'`. -/
def is_part_holonomic_at (𝓕 : jet_sec U F) (E' : submodule ℝ E) (x : E) :=
∀ v ∈ E', D 𝓕.f x v = 𝓕.φ x v

lemma is_part_holonomic_at.sup (𝓕 : jet_sec U F) {E' E'' : submodule ℝ E} {x : E}
  (h' : 𝓕.is_part_holonomic_at E' x) (h'' : 𝓕.is_part_holonomic_at E'' x) :
  𝓕.is_part_holonomic_at (E' ⊔ E'') x :=
begin

  sorry
end

lemma _root_.rel_loc.jet_sec.is_part_holonomic_at.mono {𝓕 : jet_sec U F}
  {E' E'' : submodule ℝ E} {x : E} (h : 𝓕.is_part_holonomic_at E' x) (h' : E'' ≤ E') :
  𝓕.is_part_holonomic_at E'' x :=
λ v v_in, h v $ set_like.coe_subset_coe.mpr h' v_in

def _root_.rel_loc.formal_sol.is_part_holonomic_at (𝓕 : formal_sol R U) (E' : submodule ℝ E) (x : E) :=
∀ v ∈ E', D 𝓕.f x v = 𝓕.φ x v

lemma _root_.rel_loc.formal_sol.is_part_holonomic_at.mono {𝓕 : formal_sol R U}
  {E' E'' : submodule ℝ E} {x : E} (h : 𝓕.is_part_holonomic_at E' x) (h' : E'' ≤ E') :
  𝓕.is_part_holonomic_at E'' x :=
λ v v_in, h v $ set_like.coe_subset_coe.mpr h' v_in

lemma _root_.is_part_holonomic_top {𝓕 : jet_sec U F} {x : E} :
  is_part_holonomic_at 𝓕 ⊤ x ↔ is_holonomic_at 𝓕 x :=
sorry

@[simp] lemma is_part_holonomic_bot (𝓕 : jet_sec U F) :
  is_part_holonomic_at 𝓕 ⊥ = λ x, true :=
sorry

lemma mem_slice (𝓕 : formal_sol R U) (p : dual_pair' E) {x : E} (hx : x ∈ U) :
  𝓕.φ x p.v ∈ 𝓕.slice_at p x :=
by simpa [rel_loc.formal_sol.slice_at, rel_loc.slice] using  𝓕.is_sol x hx

/-- A formal solution `𝓕` is short for a dual pair `p` at a point `x` if the derivative of
the function `𝓕.f` at `x` is in the convex hull of the relevant connected component of the
corresponding slice. -/
def is_short_at (𝓕 : jet_sec U F) (R : rel_loc E F) (p : dual_pair' E) (x : E) : Prop :=
D 𝓕.f x p.v ∈ hull (connected_comp_in (𝓕.slice_at R p x) $ 𝓕.φ x p.v)

def _root_.rel_loc.formal_sol.is_short_at (𝓕 : formal_sol R U)(p : dual_pair' E) (x : E) : Prop :=
D 𝓕.f x p.v ∈ hull (connected_comp_in (𝓕.slice_at p x) $ 𝓕.φ x p.v)

lemma _root_.rel_loc.is_ample.is_short_at_jet_sec {R : rel_loc E F} (hR : is_ample R) (𝓕 : jet_sec U F) (p : dual_pair' E)
  (x : E) : 𝓕.is_short_at R p x :=
sorry


lemma _root_.rel_loc.is_ample.is_short_at {R : rel_loc E F} (hR : is_ample R) (𝓕 : formal_sol R U) (p : dual_pair' E)
  (x : E) : 𝓕.is_short_at p x :=
sorry

end rel_loc.jet_sec

section htpy_jet_sec

open rel_loc

/-- A homotopy of formal solutions to `R` over a set `U`. -/
structure htpy_jet_sec (U : set E) (F : Type*) [normed_group F] [normed_space ℝ F] :=
(f : ℝ → E → F)
(f_diff : smooth_on (uncurry f) (@univ ℝ ×ˢ U))
(φ : ℝ → E → E →L[ℝ] F)
(φ_diff : smooth_on (uncurry φ) (@univ ℝ ×ˢ U))

variables {U : set E} {R : rel_loc E F}

instance : has_coe_to_fun (htpy_jet_sec U F) (λ S, ℝ → jet_sec U F) :=
⟨λ S t,
 { f := S.f t,
   f_diff := sorry,
   φ := S.φ t,
   φ_diff := sorry }⟩

/-- The constant homotopy of formal solutions at a given formal solution. It will be used
as junk value for constructions of formal homotopies that need additional assumptions and also
for trivial induction initialization. -/
def rel_loc.jet_sec.const_htpy (𝓕 : jet_sec U F) : htpy_jet_sec U F :=
{ f := λ t, 𝓕.f,
  f_diff := sorry,
  φ := λ t, 𝓕.φ,
  φ_diff := sorry }

@[simp] lemma rel_loc.jet_sec.const_htpy_apply (𝓕 : jet_sec U F) :
  ∀ t, 𝓕.const_htpy t = 𝓕 :=
λ t, by ext x ; refl

-- The next gadget is probably already in mathlib somewhere (the precise values 1/4 and 3/4 are
-- not important)

/-- A smooth step function on `ℝ`.

TODO: check that `real.smooth_transition` from mathlib already fits the bill
-/
def smooth_step : ℝ → ℝ := sorry

lemma smooth_step.smooth : times_cont_diff ℝ ⊤ smooth_step :=
sorry

@[simp]
lemma smooth_step.zero : smooth_step 0 = 0 :=
sorry

@[simp]
lemma smooth_step.one : smooth_step 1 = 1 :=
sorry

lemma smooth_step.mem (t : ℝ) : smooth_step t ∈ I :=
sorry

lemma smooth_step.abs_le (t : ℝ) : |smooth_step t| ≤ 1 :=
sorry


/-- Concatenation of homotopies of formal solution. The result depend on our choice of
a smooth step function in order to keep smoothness with respect to the time parameter. -/
def htpy_jet_sec.comp (𝓕 𝓖 : htpy_jet_sec U F) : htpy_jet_sec U F :=
{ f := λ t x, if t ≤ 1/2 then 𝓕.f (smooth_step $ 2*t) x else  𝓖.f (smooth_step $ 2*t - 1) x,
  f_diff := sorry,
  φ := λ t x, if t ≤ 1/2 then 𝓕.φ (smooth_step $ 2*t) x else  𝓖.φ (smooth_step $ 2*t - 1) x,
  φ_diff := sorry }

@[simp]
lemma htpy_jet_sec.comp_0 (𝓕 𝓖 : htpy_jet_sec U F) : 𝓕.comp 𝓖 0 = 𝓕 0 :=
sorry

@[simp]
lemma htpy_jet_sec.comp_1 (𝓕 𝓖 : htpy_jet_sec U F) : 𝓕.comp 𝓖 1 = 𝓖 1 :=
sorry

@[simp]
lemma htpy_jet_sec.comp_of_le (𝓕 𝓖 : htpy_jet_sec U F) {t : ℝ} (ht : t ≤ 1/2) :
  𝓕.comp 𝓖 t = 𝓕 (smooth_step $ 2*t) :=
sorry

@[simp]
lemma htpy_jet_sec.comp_of_not_le (𝓕 𝓖 : htpy_jet_sec U F) {t : ℝ} (ht : ¬ t ≤ 1/2) :
  𝓕.comp 𝓖 t = 𝓖 (smooth_step $ 2*t - 1) :=
sorry

end htpy_jet_sec
