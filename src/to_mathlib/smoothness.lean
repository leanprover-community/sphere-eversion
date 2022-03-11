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


section C1_real

variables {E E' F : Type*}
variables [normed_group E] [normed_space ℝ E]
variables [normed_group E'] [normed_space ℝ E']
variables [normed_group F] [normed_space ℝ F]

open filter asymptotics metric
open_locale topological_space filter

/-
The next two lemmas may be too specialized, but they are painful enough that we don't want
to prove them in the middle of some serious proof. Maybe there is a more general statement
that would still be useful enough to combine is_o.comp_tendsto and is_o.trans_is_O.
-/

lemma asymptotics.is_o.comp_fst' {E E' F : Type*} [normed_group E] [normed_group E'] [normed_group F]
  {f : E → F} (h : is_o f id (𝓝 0)) :
  is_o (λ p : E × E', f p.1) id (𝓝 0) :=
begin
  have : tendsto prod.fst (𝓝 (0 : E × E')) (𝓝 0), from continuous_fst.continuous_at,
  apply (h.comp_tendsto this).trans_is_O,
  rw show id ∘ prod.fst = (λ h : E × E', h.1), by { ext x, refl },
  exact is_O_fst_prod'
end

lemma asymptotics.is_o.comp_fst {E E' F : Type*} [normed_group E] [normed_group E'] [normed_group F]
  {f : E → F} {e : E} (h : is_o f (λ x, x - e) (𝓝 e)) (e' : E') :
  is_o (λ p : E × E', f p.1) (λ p, p - (e, e')) (𝓝 (e, e')) :=
begin
  have : tendsto prod.fst (𝓝 (e, e')) (𝓝 e), from continuous_fst.continuous_at,
  apply (h.comp_tendsto this).trans_is_O,
  rw show (λ (x : E), x - e) ∘ prod.fst = (λ (p : E × E'), p.1 - e), by {ext, refl},
  exact is_O_fst_prod
end

lemma asymptotics.is_o.comp_snd' {E E' F : Type*} [normed_group E] [normed_group E'] [normed_group F]
  {f : E' → F} (h : is_o f id (𝓝 0)) :
  is_o (λ p : E × E', f p.2) id (𝓝 0) :=
begin
  have : tendsto prod.snd (𝓝 (0 : E × E')) (𝓝 0), from continuous_snd.continuous_at,
  apply (h.comp_tendsto this).trans_is_O,
  rw show id ∘ prod.snd = (λ h : E × E', h.2), by { ext x, refl },
  exact is_O_snd_prod'
end

lemma asymptotics.is_o.comp_snd {E E' F : Type*} [normed_group E] [normed_group E'] [normed_group F]
  {f : E' → F} {e' : E'} (h : is_o f (λ x, x - e') (𝓝 e')) (e : E) :
  is_o (λ p : E × E', f p.2) (λ p, p - (e, e')) (𝓝 (e, e')) :=
begin
  have : tendsto prod.snd (𝓝 (e, e')) (𝓝 e'), from continuous_snd.continuous_at,
  apply (h.comp_tendsto this).trans_is_O,
  rw show (λ (x : E'), x - e') ∘ prod.snd = (λ (p : E × E'), p.2 - e'), by {ext, refl},
  exact is_O_snd_prod
end


lemma prod_mem_ball_iff {α β : Type*} [pseudo_metric_space α] [pseudo_metric_space β] {x x₀ : α} {y y₀ : β}
  {r} : (x, y) ∈ ball (x₀, y₀) r ↔ (x ∈ ball x₀ r) ∧ (y ∈ ball y₀ r):=
begin
  rw [mem_ball, prod.dist_eq],
  exact max_lt_iff
end

lemma prod_mem_ball_iff' {α β : Type*} [pseudo_metric_space α] [pseudo_metric_space β] {x : α} {y : β}
  {p : α × β}
  {r} : (x, y) ∈ ball p r ↔ (x ∈ ball p.1 r) ∧ (y ∈ ball p.2 r):=
prod_mem_ball_iff


lemma prod_mk_mem_ball {α β : Type*} [pseudo_metric_space α] [pseudo_metric_space β] {x x₀ : α} {y y₀ : β}
  {r} (hx : x ∈ ball x₀ r) (hy : y ∈ ball y₀ r) : (x, y) ∈ ball (x₀, y₀) r :=
begin
  rw prod_mem_ball_iff,
  exact ⟨hx, hy⟩
end

def linear_map.coprodₗ (R M M₂ M₃ : Type*) [comm_ring R]
  [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃] [module R M]
  [module R M₂] [module R M₃] : ((M →ₗ[R] M₃) × (M₂ →ₗ[R] M₃)) →ₗ[R] (M × M₂ →ₗ[R] M₃) :=
{ to_fun := λ p, p.1.coprod p.2,
  map_add' := begin
    intros p q,
    apply linear_map.coe_injective,
    ext x,
    simp only [prod.fst_add, linear_map.coprod_apply, linear_map.add_apply, prod.snd_add],
    ac_refl
  end,
  map_smul' := begin
    intros r p,
    apply linear_map.coe_injective,
    ext x,
    simp only [prod.smul_fst, prod.smul_snd, linear_map.coprod_apply, linear_map.smul_apply,
               ring_hom.id_apply, smul_add]
  end }

lemma add_le_twice_max (a b : ℝ) : a + b ≤ 2*max a b :=
calc a + b ≤ max a b + max a b : add_le_add (le_max_left a b) (le_max_right a b)
... = _ : by ring

lemma is_bounded_linear_map_coprod (𝕜 : Type*) [nondiscrete_normed_field 𝕜] (E : Type*) [normed_group E]
  [normed_space 𝕜 E] (F : Type*) [normed_group F] [normed_space 𝕜 F]
  (G : Type*) [normed_group G] [normed_space 𝕜 G] : is_bounded_linear_map 𝕜
  (λ p : (E →L[𝕜] G) × (F →L[𝕜] G), p.1.coprod p.2) :=
{ map_add := begin
    intros,
    apply continuous_linear_map.coe_fn_injective,
    ext u,
    simp only [prod.fst_add, prod.snd_add, continuous_linear_map.coprod_apply,
               continuous_linear_map.add_apply],
    ac_refl
  end,
  map_smul := begin
    intros r p,
    apply continuous_linear_map.coe_fn_injective,
    ext x,
    simp only [prod.smul_fst, prod.smul_snd, continuous_linear_map.coprod_apply,
               continuous_linear_map.coe_smul', pi.smul_apply, smul_add],
  end,
  bound := begin
    refine ⟨2, zero_lt_two, _⟩,
    rintros ⟨φ, ψ⟩,
    apply continuous_linear_map.op_norm_le_bound,
    apply mul_nonneg zero_le_two, apply norm_nonneg,
    rintros ⟨e, f⟩,
    calc ∥φ e + ψ f∥ ≤ ∥φ e∥ + ∥ψ f∥ : norm_add_le _ _
    ... ≤  ∥φ∥ * ∥e∥ + ∥ψ∥ * ∥f∥ : add_le_add (φ.le_op_norm e) (ψ.le_op_norm f)
    ... ≤ (max ∥φ∥ ∥ψ∥) * ∥e∥ + (max ∥φ∥ ∥ψ∥) * ∥f∥ : _
    ... ≤ (2*(max ∥φ∥ ∥ψ∥)) * (max ∥e∥ ∥f∥) : _,
    apply add_le_add,
    exact mul_le_mul_of_nonneg_right (le_max_left ∥φ∥ ∥ψ∥) (norm_nonneg e),
    exact mul_le_mul_of_nonneg_right (le_max_right ∥φ∥ ∥ψ∥) (norm_nonneg f),
    rw [← mul_add, mul_comm (2 : ℝ), mul_assoc],
    apply mul_le_mul_of_nonneg_left (add_le_twice_max _ _) (le_max_of_le_left $ norm_nonneg _)
  end }

noncomputable
def continuous_linear_map.coprodL {𝕜 : Type*} [nondiscrete_normed_field 𝕜] {E : Type*} [normed_group E]
  [normed_space 𝕜 E] {F : Type*} [normed_group F] [normed_space 𝕜 F]
  {G : Type*} [normed_group G] [normed_space 𝕜 G] :
  ((E →L[𝕜] G) × (F →L[𝕜] G)) →L[𝕜] (E × F →L[𝕜] G) :=
(is_bounded_linear_map_coprod 𝕜 E F G).to_continuous_linear_map



lemma has_fderiv_at.comp' {𝕜 : Type*} [nondiscrete_normed_field 𝕜] {E : Type*} [normed_group E]
  [normed_space 𝕜 E] {F : Type*} [normed_group F] [normed_space 𝕜 F]
  {G : Type*} [normed_group G] [normed_space 𝕜 G] {f : E → F} {f' : E →L[𝕜] F} {x : E}
  {g : F → G} {g' : F →L[𝕜] G} (hg : has_fderiv_at g g' (f x)) (hf : has_fderiv_at f f' x)
  {gf' : E →L[𝕜] G} (h : gf' = g'.comp f') :
  has_fderiv_at (g ∘ f) gf' x :=
h.symm ▸ hg.comp x hf

lemma has_fderiv_at.sub' {𝕜 : Type*} [ nondiscrete_normed_field 𝕜] {E : Type*} [normed_group E]
  [normed_space 𝕜 E] {F : Type*} [normed_group F] [normed_space 𝕜 F]
  {f g : E → F} {f' g' fg' : E →L[𝕜] F} {x : E} (hf : has_fderiv_at f f' x)
  (hg : has_fderiv_at g g' x)  (h : fg' = f' - g') :
  has_fderiv_at (λ (x : E), f x - g x) fg' x :=
h.symm ▸ hf.sub hg

lemma has_fderiv_at_of_partial {f : E × E' → F} {φ₁ : E × E' → (E →L[ℝ] F)}
  {φ₂ : E × E' → (E' →L[ℝ] F)} {p : E × E'}
  (hfφ₁ : ∀ᶠ (q : E × E') in 𝓝 p, has_fderiv_at (λ (x : E), f (x, q.2)) (φ₁ q) q.1)
  (hfφ₂ : has_fderiv_at (λ (y : E'), f (p.1, y)) (φ₂ p) p.2) (hφ₁ : continuous_at φ₁ p) :
  has_fderiv_at f ((φ₁ p).coprod (φ₂ p)) p :=
begin
  change is_o _ _ _,
  have : (λ (q : E × E'), f q - f p - ((φ₁ p).coprod (φ₂ p)) (q - p)) =
    (λ q : E × E', f (q.1, q.2) - f (p.1, q.2) - φ₁ p (q.1 - p.1)) +
    (λ e', f (p.1, e') - f p  - φ₂ p (e'-p.2)) ∘ prod.snd,
  { ext ⟨x, y⟩,
    simp only [continuous_linear_map.coprod_apply, prod.fst_sub, map_sub, pi.add_apply, comp_app],
    abel },
  rw this, clear this,
  apply is_o.add,
  { rw is_o_iff,
    intros ε ε_pos,
    have : ∀ᶠ (q : E × E') in 𝓝 p, ∥φ₁ q - φ₁ p∥ ≤ ε,
    { filter_upwards [nhds_basis_ball.tendsto_right_iff.mp hφ₁ ε ε_pos] with x hx,
      exact (mem_ball_iff_norm.mp hx).le },
    rcases metric.eventually_nhds_iff_ball.mp (this.and hfφ₁) with ⟨δ, δ_pos, hδ⟩,
    apply metric.eventually_nhds_iff_ball.mpr ⟨δ, δ_pos, _⟩,
    rintros ⟨q₁, q₂⟩ h,
    dsimp only,
    let ψ : E' → E → F := λ q₂ q₁, f (q₁, q₂) - φ₁ p (q₁ - p.1),
    have : f (q₁, q₂) - f (p.fst, q₂) - (φ₁ p) (q₁ - p.fst) = ψ q₂ q₁ - ψ q₂ p.1,
    { simp only [ψ, pi.sub_apply],
      simp only [sub_self, sub_zero, continuous_linear_map.map_zero, sub_right_comm] },
    rw this,
    rw prod_mem_ball_iff' at h,
    have hψ : ∀ q₁ ∈ ball p.1 δ, has_fderiv_at (ψ q₂) (φ₁ (q₁, q₂) - φ₁ p) q₁,
    { intros q₁' hq₁',

      apply (hδ ⟨q₁', q₂⟩ (prod_mk_mem_ball hq₁' h.2)).2.sub,
      have : has_fderiv_at (λ (x : E), x - p.fst) (continuous_linear_map.id ℝ E) q₁',
      { apply (has_fderiv_at_id _).sub' (has_fderiv_at_const _ _),
        simp },
      apply (φ₁ p).has_fderiv_at.comp' this,
      simp },
    suffices : ∥ψ q₂ q₁ - ψ q₂ p.fst∥ ≤ ε * ∥q₁ - p.1∥,
    { exact this.trans (mul_le_mul_of_nonneg_left (le_max_left _ _) ε_pos.le) },
    apply (convex_ball p.1 δ).norm_image_sub_le_of_norm_has_fderiv_within_le (λ x hx, (hψ x hx).has_fderiv_within_at) _ (mem_ball_self δ_pos) h.1,
    intros x hx,
    exact (hδ (x, q₂) (prod_mk_mem_ball hx h.2)).1 },
  { cases p with p₁ p₂,
    have : is_o _ _ _ := hfφ₂,
    exact this.comp_snd p₁ }
end

lemma has_fderiv_of_partial {f : E × E' → F} {φ₁ : E × E' → (E →L[ℝ] F)}
  {φ₂ : E × E' → (E' →L[ℝ] F)}
  (hfφ₁ : ∀ q : E × E', has_fderiv_at (λ (x : E), f (x, q.2)) (φ₁ q) q.1)
  (hfφ₂ : ∀ q : E × E', has_fderiv_at (λ (y : E'), f (q.1, y)) (φ₂ q) q.2)
  (hφ₁ : continuous φ₁) (p : E × E') :
  has_fderiv_at f ((φ₁ p).coprod (φ₂ p)) p :=
has_fderiv_at_of_partial (eventually_of_forall (λ q : E × E', (hfφ₁ q))) (hfφ₂ p) hφ₁.continuous_at

lemma fderiv_of_partial {f : E × E' → F} {φ₁ : E × E' → (E →L[ℝ] F)}
  {φ₂ : E × E' → (E' →L[ℝ] F)}
  (hfφ₁ : ∀ q : E × E', has_fderiv_at (λ (x : E), f (x, q.2)) (φ₁ q) q.1)
  (hfφ₂ : ∀ q : E × E', has_fderiv_at (λ (y : E'), f (q.1, y)) (φ₂ q) q.2)
  (hφ₁ : continuous φ₁) : fderiv ℝ f = λ p, ((φ₁ p).coprod (φ₂ p)) :=
funext (λ p, (has_fderiv_of_partial hfφ₁ hfφ₂ hφ₁ p).fderiv)

lemma cont_diff_one_of_partial {f : E × E' → F} {φ₁ : E × E' → (E →L[ℝ] F)}
  {φ₂ : E × E' → (E' →L[ℝ] F)}
  (hfφ₁ : ∀ q : E × E', has_fderiv_at (λ (x : E), f (x, q.2)) (φ₁ q) q.1)
  (hfφ₂ : ∀ q : E × E', has_fderiv_at (λ (y : E'), f (q.1, y)) (φ₂ q) q.2)
  (hφ₁ : continuous φ₁) (hφ₂ : continuous φ₂) : cont_diff ℝ 1 f :=
begin
  rw cont_diff_one_iff_fderiv,
  refine ⟨λ p, ⟨(φ₁ p).coprod (φ₂ p), has_fderiv_of_partial hfφ₁ hfφ₂ hφ₁ p⟩, _⟩,
  rw fderiv_of_partial hfφ₁ hfφ₂ hφ₁,
  exact continuous_linear_map.coprodL.continuous.comp (hφ₁.prod_mk hφ₂)
end


end  C1_real

section smooth_real_same_univ

-- Fixing the universe for induction purposes. Maybe this can be avoided.
universe u
variables {E E' F F' G H K : Type u}
variables [normed_group E] [normed_space ℝ E]
variables [normed_group E'] [normed_space ℝ E']
variables [normed_group F] [normed_space ℝ F]
variables [normed_group G] [normed_space ℝ G]
variables [normed_group H] [normed_space ℝ H]
variables [normed_group K] [normed_space ℝ K]
variables [normed_linear_ordered_field F'] [normed_space ℝ F']
variables {n : with_top ℕ}
-- #print continuous.if_le

lemma cont_diff_of_partial' {n : ℕ} {f : E × E' → F} {φ₁ : E × E' → (E →L[ℝ] F)}
  {φ₂ : E × E' → (E' →L[ℝ] F)}
  (hfφ₁ : ∀ q : E × E', has_fderiv_at (λ (x : E), f (x, q.2)) (φ₁ q) q.1)
  (hfφ₂ : ∀ q : E × E', has_fderiv_at (λ (y : E'), f (q.1, y)) (φ₂ q) q.2)
  (hφ₁ : cont_diff ℝ n φ₁) (hφ₂ : cont_diff ℝ n φ₂) : cont_diff ℝ (n+1) f :=
begin
  revertI F,
  induction n with n hn,
  sorry ; { introsI F _ _ f φ₁ φ₂ hfφ₁ hfφ₂ hφ₁ hφ₂,
    exact cont_diff_one_of_partial hfφ₁ hfφ₂ hφ₁.continuous hφ₂.continuous },
  introsI F _ _ f φ₁ φ₂ hfφ₁ hfφ₂ hφ₁ hφ₂,
  erw cont_diff_succ_iff_fderiv,
  refine ⟨(cont_diff_one_of_partial hfφ₁ hfφ₂ hφ₁.continuous hφ₂.continuous).differentiable le_rfl, _⟩,
  apply hn,
  { intros q,
    rw fderiv_of_partial hfφ₁ hfφ₂ hφ₁.continuous,
    dsimp,
    have := funext (λ x, (hfφ₁ (x, q.2)).fderiv),
    dsimp at this,
    sorry },
  all_goals {sorry}
end
end smooth_real_same_univ

section smooth_real

variables {E E' F F' G H K : Type*}
variables [normed_group E] [normed_space ℝ E]
variables [normed_group E'] [normed_space ℝ E']
variables [normed_group F] [normed_space ℝ F]
variables [normed_group G] [normed_space ℝ G]
variables [normed_group H] [normed_space ℝ H]
variables [normed_group K] [normed_space ℝ K]
variables [normed_linear_ordered_field F'] [normed_space ℝ F']
variables {n : with_top ℕ}

-- Note: Patrick thinks all statements in this section are wrong

lemma cont_diff_of_partial {f : E × E' → F} (h1f : ∀ x, cont_diff ℝ (n+1) (λ y, f (x, y)))
  (h2f : ∀ y, cont_diff ℝ (n + 1) (λ x, f (x, y))) : cont_diff ℝ (n+1) f :=
sorry

lemma iterated_fderiv_of_partial {f : E × E' → F} {n : ℕ} (h1f : ∀ x, cont_diff ℝ (n+1) (λ y, f (x, y)))
  (h2f : ∀ y, cont_diff ℝ (n+1) (λ x, f (x, y))) (x : E) (y : E') :
    iterated_fderiv ℝ (n+1) f (x, y) =
    (iterated_fderiv ℝ (n+1) (λ x, f (x, y)) x).coprod (iterated_fderiv ℝ (n+1) (λ y, f (x, y)) y) :=
sorry

lemma iterated_fderiv_comp {g : F → G} {f : E → F} {n : ℕ} (hg : cont_diff ℝ n g)
  (hf : cont_diff ℝ n f) (x : E) :
    iterated_fderiv ℝ n (g ∘ f) x =
    (iterated_fderiv ℝ n g (f x)).comp (λ i, iterated_fderiv ℝ n f x) :=
sorry

lemma cont_diff.if_le_of_fderiv {f g : E → F} {a b : E → F'}
  (hf : cont_diff ℝ n f) (hg : cont_diff ℝ n g) (ha : cont_diff ℝ n a) (hb : cont_diff ℝ n b)
  (h : ∀ x n, a x = b x → iterated_fderiv ℝ n f x = iterated_fderiv ℝ n g x) :
  cont_diff ℝ n (λ x, if a x ≤ b x then f x else g x) :=
sorry

lemma cont_diff.if_le_of_deriv {n : with_top ℕ} {f g : ℝ → F} {a b : ℝ → F'}
  (hf : cont_diff ℝ n f) (hg : cont_diff ℝ n g) (ha : cont_diff ℝ n a) (hb : cont_diff ℝ n b)
  (h : ∀ x n, a x = b x → iterated_deriv n f x = iterated_deriv n g x) :
  cont_diff ℝ n (λ x, if a x ≤ b x then f x else g x) :=
sorry

end smooth_real

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


lemma cont_diff.comp₂ {g : E × F → G} (hg : cont_diff 𝕜 n g) {e : H → E} (he : cont_diff 𝕜 n e)
  {f : H → F} (hf : cont_diff 𝕜 n f) : cont_diff 𝕜 n (λ h, g (e h, f h)) :=
hg.comp $ he.prod hf

lemma cont_diff.comp₃ {g : E × F × K → G} (hg : cont_diff 𝕜 n g)
  {e : H → E} (he : cont_diff 𝕜 n e) {f : H → F} (hf : cont_diff 𝕜 n f)
  {k : H → K} (hk : cont_diff 𝕜 n k) : cont_diff 𝕜 n (λ h, g (e h, f h, k h)) :=
hg.comp $ he.prod $ hf.prod hk

end smooth
