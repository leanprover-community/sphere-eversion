import analysis.calculus.fderiv


variables (E : Type*) [normed_group E] [normed_space ℝ E] (F : Type*)
                        [normed_group F] [normed_space ℝ F] 

local notation `D` := fderiv ℝ

/-- A first order relation for maps between real vector spaces. -/
def rel_loc := set (E × F × (E →L[ℝ] F))

instance : has_mem (E × F × (E →L[ℝ] F)) (rel_loc E F) :=
set.has_mem

variables {E F}

def is_formal_solution_on (R : rel_loc E F) (U : set E) (σ : E → F × (E →L[ℝ] F)) : Prop := 
∀ x ∈ U, (x, σ x) ∈ R

def is_holonomic_on (U : set E) (σ : E → (F × (E →L[ℝ] F))) :=
∀ x ∈ U, differentiable_at ℝ (λ x, (σ x).1) x ∧ D (λ x, (σ x).1) x = (σ x).2

def is_part_holonomic_on (U : set E) (E' : submodule ℝ E) (σ : E → (F × (E →L[ℝ] F))) :=
∀ x ∈ U, differentiable_at ℝ (λ x, (σ x).1) x ∧ ∀ v ∈ E', D (λ x, (σ x).1) x v = (σ x).2 v

structure is_solution_on (R : rel_loc E F) (U : set E) (f : E → F) : Prop :=
(diff : ∀ x ∈ U, differentiable_at ℝ f x)
(sol : ∀ x ∈ U, (x, f x, fderiv ℝ f x) ∈ R)