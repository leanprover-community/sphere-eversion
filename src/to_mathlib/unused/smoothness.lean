import analysis.calculus.specific_functions

import to_mathlib.unused.linear_algebra.multilinear
import to_mathlib.analysis.normed_space.operator_norm

/-
Work toward gluing smooth function. This includes proving that a function
which has continuous partial derivatives on E × F is C¹.

We no longer intend to use this file in the sphere eversion project, but it should still
go into mathlib in some form.
-/

/- arguments about smoothness -/

/-- Ability to `sorry` things without getting warning messages. This should only be used in declarations we are not using in the project. -/
axiom sorry_ax {α : Sort*} : α

open exp_neg_inv_glue real
lemma iterated_deriv_exp_neg_inv_glue (n : ℕ) : iterated_deriv n exp_neg_inv_glue = f_aux n :=
by simp_rw [← f_aux_zero_eq, f_aux_iterated_deriv]

lemma iterated_deriv_exp_neg_inv_glue_zero (n : ℕ) :
  iterated_deriv n exp_neg_inv_glue 0 = 0 :=
by simp_rw [iterated_deriv_exp_neg_inv_glue, f_aux, le_rfl, if_true]

@[simp]
lemma iterated_deriv_smooth_transition_zero (n : ℕ) :
  iterated_deriv n smooth_transition 0 = 0 :=
sorry_ax

@[simp]
lemma iterated_deriv_smooth_transition_one {n : ℕ} (hn : 1 ≤ n) :
  iterated_deriv n smooth_transition 1 = 0 :=
sorry_ax

@[simp]
lemma iterated_fderiv_smooth_transition_zero (n : ℕ) :
  iterated_fderiv ℝ n smooth_transition 0 = 0 :=
sorry_ax

@[simp]
lemma iterated_fderiv_smooth_transition_one {n : ℕ} (hn : 1 ≤ n) :
  iterated_fderiv ℝ n smooth_transition 1 = 0 :=
sorry_ax

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
    simp only [continuous_linear_map.coprod_apply, prod.fst_sub, map_sub, pi.add_apply, function.comp_app],
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

/- The lemmas below are maybe-true lemmas about iterated derivatives, that are useful to have (though we probably don't need them in this project) -/
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

lemma iterated_fderiv_comp_eq_zero_right {g : F → G} {f : E → F} {n : ℕ} (hg : cont_diff 𝕜 n g)
  (hf : cont_diff 𝕜 n f) (x : E) (hn : 1 ≤ n) (h : ∀ m ≤ n, 1 ≤ m → iterated_fderiv 𝕜 m f x = 0) :
    iterated_fderiv 𝕜 n (g ∘ f) x = 0 :=
sorry_ax

lemma iterated_fderiv_comp_eq_zero_left {g : F → G} {f : E → F} {n : ℕ} (hg : cont_diff 𝕜 n g)
  (hf : cont_diff 𝕜 n f) (x : E) (hn : 1 ≤ n)
  (h : ∀ m ≤ n, 1 ≤ m → iterated_fderiv 𝕜 m g (f x) = 0) :
    iterated_fderiv 𝕜 n (g ∘ f) x = 0 :=
sorry_ax

lemma cont_diff.if_le_of_fderiv {f g : E → F} {a b : E → F'}
  (hf : cont_diff 𝕜 n f) (hg : cont_diff 𝕜 n g) (ha : cont_diff 𝕜 n a) (hb : cont_diff 𝕜 n b)
  (h : ∀ x n, a x = b x → iterated_fderiv 𝕜 n f x = iterated_fderiv 𝕜 n g x) :
  cont_diff 𝕜 n (λ x, if a x ≤ b x then f x else g x) :=
sorry_ax

lemma cont_diff.if_le_of_deriv {n : with_top ℕ} {f g : 𝕜 → F} {a b : 𝕜 → F'}
  (hf : cont_diff 𝕜 n f) (hg : cont_diff 𝕜 n g) (ha : cont_diff 𝕜 n a) (hb : cont_diff 𝕜 n b)
  (h : ∀ x n, a x = b x → iterated_deriv n f x = iterated_deriv n g x) :
  cont_diff 𝕜 n (λ x, if a x ≤ b x then f x else g x) :=
sorry_ax

end smooth
