import analysis.calculus.specific_functions

/-
Multilinear map stuff that was meant as preliminaries for smooth functions gluing.

We no longer intend to use this file in the sphere eversion project.
-/

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
  have h1 := function.apply_update (λ _, prod.fst) v, dsimp at h1,
  have h2 := function.apply_update (λ _, prod.snd) v, dsimp at h2,
  simp_rw [h1, h2, add_add_add_comm, ← L₁.map_add, ← L₂.map_add, prod.add_def] },
  map_smul' := λ v i c p, by {
  have h1 := function.apply_update (λ _, prod.fst) v, dsimp at h1,
  have h2 := function.apply_update (λ _, prod.snd) v, dsimp at h2,
  simp_rw [h1, h2, smul_add, ← L₁.map_smul, ← L₂.map_smul, prod.smul_def] } }

/-- If `g` is a multilinear map and `f` is a collection of multilinear maps,
then `g (f₁ m, ..., fₙ m)` is again a multilinear map, that we call
`g.comp f`. -/
def comp (g : multilinear_map R N M₃) (f : Π i, multilinear_map R M₁ (N i)) :
  multilinear_map R M₁ M₃ :=
{ to_fun := λ v, g (λ i, f i v),
  map_add' := sorry,
  map_smul' := sorry }

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


def simps.apply (L₁ : continuous_multilinear_map R M₁ M₃) (v : Π i, M₁ i) : M₃ := L₁ v

initialize_simps_projections continuous_multilinear_map
  (-to_multilinear_map, to_multilinear_map_to_fun → apply)

@[simps]
def comp (g : continuous_multilinear_map R N M₃) (f : Π i, continuous_multilinear_map R M₁ (N i)) :
  continuous_multilinear_map R M₁ M₃ :=
{ cont := sorry,
  .. g.to_multilinear_map.comp $ λ i, (f i).to_multilinear_map }

lemma comp_zero (g : continuous_multilinear_map R N M₃) :
  g.comp (λ i, (0 : continuous_multilinear_map R M₁ (N i))) = 0 :=
sorry

lemma zero_comp (f : Π i, continuous_multilinear_map R M₁ (N i)) :
  (0 : continuous_multilinear_map R N M₃).comp f = 0 :=
sorry

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
