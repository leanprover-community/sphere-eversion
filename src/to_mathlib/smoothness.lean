import analysis.calculus.specific_functions

/- arguments about smoothness -/

open exp_neg_inv_glue real
lemma iterated_deriv_exp_neg_inv_glue (n : ℕ) : iterated_deriv n exp_neg_inv_glue = f_aux n :=
by simp_rw [← f_aux_zero_eq, f_aux_iterated_deriv]

lemma iterated_deriv_exp_neg_inv_glue_zero (n : ℕ) :
  iterated_deriv n exp_neg_inv_glue 0 = 0 :=
by simp_rw [iterated_deriv_exp_neg_inv_glue, f_aux, le_rfl, if_true]

@[simp]
lemma iterated_deriv_smooth_transition_zero (n : ℕ) :
  iterated_deriv n smooth_transition 0 = 0 :=
sorry

@[simp]
lemma iterated_deriv_smooth_transition_one {n : ℕ} (hn : 0 < n) :
  iterated_deriv n smooth_transition 1 = 0 :=
by { sorry }

@[simp]
lemma iterated_fderiv_smooth_transition_zero (n : ℕ) :
  iterated_fderiv ℝ n smooth_transition 0 = 0 :=
sorry

@[simp]
lemma iterated_fderiv_smooth_transition_one {n : ℕ} (hn : 0 < n) :
  iterated_fderiv ℝ n smooth_transition 1 = 0 :=
sorry

namespace linear_map
variables {R M₁ M₂ M₃ : Type*}
variables [semiring R]
variables [add_comm_monoid M₁] [module R M₁]
variables [add_comm_monoid M₂] [module R M₂]
variables [add_comm_monoid M₃] [module R M₃]
example (L₁ : M₁ →ₗ[R] M₃) (L₂ : M₂ →ₗ[R] M₃) : M₁ × M₂ →ₗ[R] M₃ :=
L₁.coprod L₂

end linear_map

namespace function
variables {ι α β : Sort*} [decidable_eq ι] (f : α → β) (g : ι → α) (i : ι) (v : α) (j : ι)

lemma apply_update' : f (update g i v j) = update (f ∘ g) i (f v) j :=
apply_update _ _ _ _ _

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


section smooth
variables {𝕜 E E' F F' G H K : Type*}
variables [nondiscrete_normed_field 𝕜]
variables [normed_group E] [normed_space 𝕜 E]
variables [normed_group E'] [normed_space 𝕜 E']
variables [normed_group F] [normed_space 𝕜 F]
variables [normed_group G] [normed_space 𝕜 G]
variables [normed_group H] [normed_space 𝕜 H]
variables [normed_group K] [normed_space 𝕜 K]
variables [normed_linear_ordered_field F'] [normed_space 𝕜 F']
variables {n : with_top ℕ}
-- #print continuous.if_le

lemma cont_diff_of_partial {f : E × E' → F} (h1f : ∀ x, cont_diff 𝕜 n (λ y, f (x, y)))
  (h2f : ∀ y, cont_diff 𝕜 n (λ x, f (x, y))) (hn : 1 ≤ n) : cont_diff 𝕜 n f :=
sorry

lemma iterated_fderiv_of_partial {f : E × E' → F} {n : ℕ} (h1f : ∀ x, cont_diff 𝕜 n (λ y, f (x, y)))
  (h2f : ∀ y, cont_diff 𝕜 n (λ x, f (x, y))) (hn : 1 ≤ n) (x : E) (y : E') :
    iterated_fderiv 𝕜 n f (x, y) =
    (iterated_fderiv 𝕜 n (λ x, f (x, y)) x).coprod (iterated_fderiv 𝕜 n (λ y, f (x, y)) y) :=
sorry

lemma iterated_fderiv_comp {g : F → G} {f : E → F} {n : ℕ} (hg : cont_diff 𝕜 n g)
  (hf : cont_diff 𝕜 n f) (x : E) :
    iterated_fderiv 𝕜 n (g ∘ f) x =
    (iterated_fderiv 𝕜 n g (f x)).comp (λ i, iterated_fderiv 𝕜 n f x) :=
sorry

lemma cont_diff.if_le_of_fderiv {f g : E → F} {a b : E → F'}
  (hf : cont_diff 𝕜 n f) (hg : cont_diff 𝕜 n g) (ha : cont_diff 𝕜 n a) (hb : cont_diff 𝕜 n b)
  (h : ∀ x n, a x = b x → iterated_fderiv 𝕜 n f x = iterated_fderiv 𝕜 n g x) :
  cont_diff 𝕜 n (λ x, if a x ≤ b x then f x else g x) :=
sorry

lemma cont_diff.if_le_of_deriv {n : with_top ℕ} {f g : 𝕜 → F} {a b : 𝕜 → F'}
  (hf : cont_diff 𝕜 n f) (hg : cont_diff 𝕜 n g) (ha : cont_diff 𝕜 n a) (hb : cont_diff 𝕜 n b)
  (h : ∀ x n, a x = b x → iterated_deriv n f x = iterated_deriv n g x) :
  cont_diff 𝕜 n (λ x, if a x ≤ b x then f x else g x) :=
sorry

lemma cont_diff.comp₂ {g : E × F → G} (hg : cont_diff 𝕜 n g) {e : H → E} (he : cont_diff 𝕜 n e)
  {f : H → F} (hf : cont_diff 𝕜 n f) : cont_diff 𝕜 n (λ h, g (e h, f h)) :=
hg.comp $ he.prod hf

lemma cont_diff.comp₃ {g : E × F × K → G} (hg : cont_diff 𝕜 n g)
  {e : H → E} (he : cont_diff 𝕜 n e) {f : H → F} (hf : cont_diff 𝕜 n f)
  {k : H → K} (hk : cont_diff 𝕜 n k) : cont_diff 𝕜 n (λ h, g (e h, f h, k h)) :=
hg.comp $ he.prod $ hf.prod hk

end smooth
