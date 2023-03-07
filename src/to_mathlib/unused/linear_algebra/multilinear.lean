import analysis.calculus.bump_function_inner

/-
Multilinear map stuff that was meant as preliminaries for smooth functions gluing.

We no longer intend to use this file in the sphere eversion project.
-/

namespace function

variables {ι : Sort*} [decidable_eq ι] {α β : ι → Type*}

/-- Special case of `function.apply_update`. Useful for `rw`/`simp`. -/
lemma update_fst (g : Π i, α i × β i) (i : ι) (v : α i × β i) (j : ι) :
  (update g i v j).fst = update (λ k, (g k).fst) i v.fst j :=
apply_update (λ _, prod.fst) g i v j

/-- Special case of `function.apply_update`. Useful for `rw`/`simp`. -/
lemma update_snd (g : Π i, α i × β i) (i : ι) (v : α i × β i) (j : ι) :
  (update g i v j).snd = update (λ k, (g k).snd) i v.snd j :=
apply_update (λ _, prod.snd) g i v j

end function
open function

namespace multilinear_map
variables {R ι ι' M₃ M₄ : Type*} {M₁ M₂ : ι → Type*} {N : ι' → Type*}
variables [decidable_eq ι] [decidable_eq ι'] [semiring R]
variables [Π i, add_comm_monoid (M₁ i)] [Π i, module R (M₁ i)]
variables [Π i, add_comm_monoid (M₂ i)] [Π i, module R (M₂ i)]
variables [Π i, add_comm_monoid (N i)] [Π i, module R (N i)]
variables [add_comm_monoid M₃] [module R M₃]
variables [add_comm_monoid M₄] [module R M₄]

/-- The coproduct of two multilinear maps. -/
@[simps]
def coprod (L₁ : multilinear_map R M₁ M₃) (L₂ : multilinear_map R M₂ M₃) :
  multilinear_map R (λ i, M₁ i × M₂ i) M₃ :=
{ to_fun := λ v, L₁ (λ i, (v i).1) + L₂ (λ i, (v i).2),
  map_add' := λ v i p q, by {
  simp_rw [update_fst, update_snd, add_add_add_comm, ← L₁.map_add, ← L₂.map_add, prod.add_def] },
  map_smul' := λ v i c p, by {
  simp_rw [update_fst, update_snd, smul_add, ← L₁.map_smul, ← L₂.map_smul, prod.smul_def] } }

end multilinear_map

namespace continuous_multilinear_map
variables {R ι ι' : Type*} {M₁ M₂ : ι → Type*} {M₃ M₄ : Type*} {N : ι' → Type*}
variables [decidable_eq ι] [decidable_eq ι'] [semiring R]
variables [Π i, add_comm_monoid (M₁ i)] [Π i, add_comm_monoid (M₂ i)] [add_comm_monoid M₃]
variables [Π i, module R (M₁ i)] [Π i, module R (M₂ i)] [module R M₃]
variables [Π i, topological_space (M₁ i)] [Π i, topological_space (M₂ i)]
variables [topological_space M₃]
variables [add_comm_monoid M₄] [module R M₄] [topological_space M₄]
variables [Π i, add_comm_monoid (N i)] [Π i, module R (N i)] [Π i, topological_space (N i)]

variables [has_continuous_add M₃]
@[simps]
def coprod (L₁ : continuous_multilinear_map R M₁ M₃) (L₂ : continuous_multilinear_map R M₂ M₃) :
  continuous_multilinear_map R (λ i, M₁ i × M₂ i) M₃ :=
{ cont := (L₁.cont.comp $ by continuity).add (L₂.cont.comp $ by continuity),
  .. L₁.to_multilinear_map.coprod L₂.to_multilinear_map }

@[simp]
def zero_coprod_zero :
  (0 : continuous_multilinear_map R M₁ M₃).coprod (0 : continuous_multilinear_map R M₂ M₃) = 0 :=
by { ext, simp }

end continuous_multilinear_map
