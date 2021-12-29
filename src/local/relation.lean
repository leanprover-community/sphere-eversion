import analysis.calculus.times_cont_diff
import linear_algebra.dual

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

-- TODO: replace mathlib's `connected_component_in`, which is never used, by the following. 

def connected_comp_in {α : Type*} [topological_space α] (F : set α) (x : α) : set α :=
if h : x ∈ F then coe '' (connected_component (⟨x, h⟩ : F)) else ∅ 


-- TODO: move mathlib's dual_pair out of the root namespace!

structure dual_pair' :=
(π : dual ℝ E)
(v : E)
(pairing : π v = 1)

variables {E}

def dual_pair'.span_v (p : dual_pair' E) : submodule ℝ E := submodule.span ℝ {p.v}

variables (E)

/-- A first order relation for maps between real vector spaces. -/
def rel_loc := set (E × F × (E →L[ℝ] F))

instance : has_mem (E × F × (E →L[ℝ] F)) (rel_loc E F) := set.has_mem

variables {E F}

namespace rel_loc

def slice (R : rel_loc E F) (p : dual_pair' E) : set F := sorry

def is_open_over (R : rel_loc E F) (U : set E) : Prop := sorry

end rel_loc

structure formal_sol (R : rel_loc E F) (U : set E) :=
(f : E → F)
(f_diff : smooth_on f U)
(φ : E → E →L[ℝ] F)
(φ_diff : smooth_on φ U)
(sol : ∀ x ∈ U, (x, f x, φ x) ∈ R)

namespace formal_sol

instance (R : rel_loc E F) (U : set E) : has_coe_to_fun (formal_sol R U) (λ S, E → F × (E →L[ℝ] F)) := 
⟨λ 𝓕, λ x, (𝓕.f x, 𝓕.φ x)⟩

variables {U : set E} {R : rel_loc E F}

def is_holonomic_at (𝓕 : formal_sol R U) (x : E) : Prop := D 𝓕.f x = 𝓕.φ x

def is_part_holonomic_at (𝓕 : formal_sol R U) (E' : submodule ℝ E) (x : E) :=
∀ v ∈ E', D 𝓕.f x v = 𝓕.φ x v

lemma mem_slice (𝓕 : formal_sol R U) (p : dual_pair' E) {x : E} (hx : x ∈ U) : 𝓕.φ x p.v ∈ R.slice p :=
sorry

def is_short_at (𝓕 : formal_sol R U) (p : dual_pair' E) (x : E) : Prop :=
D 𝓕.f x p.v ∈ hull (connected_comp_in (R.slice p) $ 𝓕.φ x p.v)

end formal_sol

structure htpy_formal_sol (R : rel_loc E F) (U : set E) :=
(f : ℝ → E → F)
(f_diff : smooth_on (uncurry f) (set.prod I U))
(φ : ℝ → E → E →L[ℝ] F)
(φ_diff : smooth_on (uncurry φ) (set.prod I U))
(sol : ∀ t ∈ I, ∀ x ∈ U, (x, f t x, φ t x) ∈ R)

instance (R : rel_loc E F) (U : set E) : has_coe_to_fun (htpy_formal_sol R U) (λ S, I → formal_sol R U) := 
⟨λ S t, 
 { f := S.f t,
   f_diff := sorry,
   φ := S.φ t,
   φ_diff := sorry,
   sol := λ x hx, S.sol t t.property x hx }⟩

def formal_sol.const_htpy {R : rel_loc E F} {U : set E} (𝓕 : formal_sol R U) : htpy_formal_sol R U :=
{ f := λ t, 𝓕.f,
  f_diff := sorry,
  φ := λ t, 𝓕.φ,
  φ_diff := sorry,
  sol := λ t ht, 𝓕.sol }