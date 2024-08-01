import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-
Multilinear map stuff that was meant as preliminaries for smooth functions gluing.

We no longer intend to use this file in the sphere eversion project.
-/
namespace Function

variable {ι : Sort*} [DecidableEq ι] {α β : ι → Type*}

/-- Special case of `function.apply_update`. Useful for `rw`/`simp`. -/
theorem update_fst (g : ∀ i, α i × β i) (i : ι) (v : α i × β i) (j : ι) :
    (update g i v j).fst = update (fun k ↦ (g k).fst) i v.fst j :=
  apply_update (fun _ ↦ Prod.fst) g i v j

/-- Special case of `function.apply_update`. Useful for `rw`/`simp`. -/
theorem update_snd (g : ∀ i, α i × β i) (i : ι) (v : α i × β i) (j : ι) :
    (update g i v j).snd = update (fun k ↦ (g k).snd) i v.snd j :=
  apply_update (fun _ ↦ Prod.snd) g i v j

end Function

open Function

namespace MultilinearMap

variable {R ι ι' M₃ M₄ : Type*} {M₁ M₂ : ι → Type*} {N : ι' → Type*}

variable [Semiring R]

variable [∀ i, AddCommMonoid (M₁ i)] [∀ i, Module R (M₁ i)]

variable [∀ i, AddCommMonoid (M₂ i)] [∀ i, Module R (M₂ i)]

variable [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]

variable [AddCommMonoid M₃] [Module R M₃]

variable [AddCommMonoid M₄] [Module R M₄]

/-- The coproduct of two multilinear maps. -/
@[simps!]
def coprod (L₁ : MultilinearMap R M₁ M₃) (L₂ : MultilinearMap R M₂ M₃) :
    MultilinearMap R (fun i ↦ M₁ i × M₂ i) M₃ :=
  (L₁.compLinearMap fun _ ↦ .fst ..) + L₂.compLinearMap fun _ ↦ .snd ..

end MultilinearMap

namespace ContinuousMultilinearMap

variable {R ι ι' : Type*} {M₁ M₂ : ι → Type*} {M₃ M₄ : Type*} {N : ι' → Type*}

variable [Semiring R]

variable [∀ i, AddCommMonoid (M₁ i)] [∀ i, AddCommMonoid (M₂ i)] [AddCommMonoid M₃]

variable [∀ i, Module R (M₁ i)] [∀ i, Module R (M₂ i)] [Module R M₃]

variable [∀ i, TopologicalSpace (M₁ i)] [∀ i, TopologicalSpace (M₂ i)]

variable [TopologicalSpace M₃]

variable [AddCommMonoid M₄] [Module R M₄] [TopologicalSpace M₄]

variable [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)] [∀ i, TopologicalSpace (N i)]

variable [ContinuousAdd M₃]

@[simps!]
def coprod (L₁ : ContinuousMultilinearMap R M₁ M₃) (L₂ : ContinuousMultilinearMap R M₂ M₃) :
    ContinuousMultilinearMap R (fun i ↦ M₁ i × M₂ i) M₃ :=
  (L₁.compContinuousLinearMap fun _ ↦ .fst ..) + L₂.compContinuousLinearMap fun _ ↦ .snd ..

@[simp]
def zero_coprod_zero :
    (0 : ContinuousMultilinearMap R M₁ M₃).coprod (0 : ContinuousMultilinearMap R M₂ M₃) = 0 := by
  ext; simp

end ContinuousMultilinearMap
