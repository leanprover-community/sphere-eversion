import analysis.calculus.specific_functions
import to_mathlib.topology.misc

noncomputable theory

open set function filter
open_locale topological_space

lemma is_compact.bdd_above_norm {X : Type*} [topological_space X] {E : Type*} [normed_group E]
  {s : set X} (hs : is_compact s) {f : X → E} (hf : continuous f) : ∃ M > 0, ∀ x ∈ s, ∥f x∥ ≤ M :=
begin
  cases (hs.image (continuous_norm.comp hf)).bdd_above with M hM,
  refine ⟨max 1 M, zero_lt_one.trans_le (le_max_left _ _), λ x hx, _⟩,
  exact le_max_of_le_right (hM (set.mem_image_of_mem (norm ∘ f) hx))
end

namespace real

lemma smooth_transition_proj_I {x : ℝ} :
  smooth_transition (proj_I x) = smooth_transition x :=
begin
  cases le_total (0 : ℝ) x with hx hx,
  cases le_total (1 : ℝ) x with h2x h2x,
  { rw [proj_I_eq_one.mpr h2x, smooth_transition.one_of_one_le h2x,
      smooth_transition.one_of_one_le le_rfl], },
  { rw [proj_I_eq_self.mpr ⟨hx, h2x⟩] },
  { rw [proj_I_eq_zero.mpr hx, smooth_transition.zero_of_nonpos hx,
      smooth_transition.zero_of_nonpos le_rfl], }
end

lemma smooth_transition.continuous_at {x : ℝ} : continuous_at smooth_transition x :=
smooth_transition.continuous.continuous_at

end real

section calculus
open continuous_linear_map
variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
          {E : Type*} [normed_group E] [normed_space 𝕜 E]
          {F : Type*} [normed_group F] [normed_space 𝕜 F]
          {G : Type*} [normed_group G] [normed_space 𝕜 G]
          {n : with_top ℕ}

lemma has_fderiv_at.partial_fst {φ : E → F → G} {φ' : E × F →L[𝕜] G} {e₀ : E} {f₀ : F}
  (h : has_fderiv_at (uncurry φ) φ' (e₀, f₀)) :
  has_fderiv_at (λ e, φ e f₀) (φ'.comp (inl 𝕜 E F)) e₀ :=
h.comp e₀ $ has_fderiv_at_prod_mk_left e₀ f₀

lemma has_fderiv_at.partial_snd {φ : E → F → G} {φ' : E × F →L[𝕜] G} {e₀ : E} {f₀ : F}
  (h : has_fderiv_at (uncurry φ) φ' (e₀, f₀)) :
  has_fderiv_at (λ f, φ e₀ f) (φ'.comp (inr 𝕜 E F)) f₀ :=
h.comp f₀ $ has_fderiv_at_prod_mk_right e₀ f₀

variable (𝕜)

/-- The first partial derivative of a binary function. -/
def partial_fderiv_fst {F : Type*} (φ : E → F → G) : E → F → E →L[𝕜] G :=
λ (e₀ : E) (f₀ : F), fderiv 𝕜 (λ e, φ e f₀) e₀

/-- The second partial derivative of a binary function. -/
def partial_fderiv_snd {E : Type*} (φ : E → F → G) : E → F → F →L[𝕜] G :=
λ (e₀ : E) (f₀ : F), fderiv 𝕜 (λ f, φ e₀ f) f₀

local notation `∂₁` := partial_fderiv_fst
local notation `∂₂` := partial_fderiv_snd

variable {𝕜}

lemma fderiv_partial_fst {φ : E → F → G} {φ' : E × F →L[𝕜] G} {e₀ : E} {f₀ : F}
  (h : has_fderiv_at (uncurry φ) φ' (e₀, f₀)) :
  ∂₁ 𝕜 φ e₀ f₀ = φ'.comp (inl 𝕜 E F) :=
h.partial_fst.fderiv

lemma fderiv_partial_snd {φ : E → F → G} {φ' : E × F →L[𝕜] G} {e₀ : E} {f₀ : F}
  (h : has_fderiv_at (uncurry φ) φ' (e₀, f₀)) :
  ∂₂ 𝕜 φ e₀ f₀ = φ'.comp (inr 𝕜 E F) :=
h.partial_snd.fderiv

lemma differentiable_at.has_fderiv_at_partial_fst {φ : E → F → G} {e₀ : E} {f₀ : F}
  (h : differentiable_at 𝕜 (uncurry φ) (e₀, f₀)) :
  has_fderiv_at (λ e, φ e f₀) (partial_fderiv_fst 𝕜 φ e₀ f₀) e₀ :=
(h.comp e₀ $ differentiable_at_id.prod $ differentiable_at_const f₀).has_fderiv_at

lemma differentiable_at.has_fderiv_at_partial_snd {φ : E → F → G} {e₀ : E} {f₀ : F}
  (h : differentiable_at 𝕜 (uncurry φ) (e₀, f₀)) :
has_fderiv_at (λ f, φ e₀ f) (partial_fderiv_snd 𝕜 φ e₀ f₀) f₀ :=
begin
  rw fderiv_partial_snd h.has_fderiv_at,
  exact h.has_fderiv_at.partial_snd
end

lemma cont_diff.partial_fst {φ : E → F → G} {n : with_top ℕ}
  (h : cont_diff 𝕜 n $ uncurry φ) (f₀ : F) : cont_diff 𝕜 n (λ e, φ e f₀) :=
h.comp $ cont_diff_prod_mk_left f₀

lemma cont_diff.partial_snd {φ : E → F → G} {n : with_top ℕ}
  (h : cont_diff 𝕜 n $ uncurry φ) (e₀ : E) : cont_diff 𝕜 n (λ f, φ e₀ f) :=
h.comp $ cont_diff_prod_mk_right e₀

/-- Precomposition by a continuous linear map as a continuous linear map between spaces of
continuous linear maps. -/
def continuous_linear_map.comp_rightL (φ : E →L[𝕜] F) : (F →L[𝕜] G) →L[𝕜] (E →L[𝕜] G) :=
(compL 𝕜 E F G).flip φ

/-- Postcomposition by a continuous linear map as a continuous linear map between spaces of
continuous linear maps. -/
def continuous_linear_map.comp_leftL (φ : F →L[𝕜] G) : (E →L[𝕜] F) →L[𝕜] (E →L[𝕜] G) :=
compL 𝕜 E F G φ

lemma differentiable.fderiv_partial_fst {φ : E → F → G} (hF : differentiable 𝕜 (uncurry φ)) :
  ↿(∂₁ 𝕜 φ) = (λ ψ : E × F →L[𝕜] G, ψ.comp (inl 𝕜 E F)) ∘ (fderiv 𝕜 $ uncurry φ) :=
begin
  have : ∀ p : E × F, has_fderiv_at (uncurry φ) _ p,
  { intro p,
    exact (hF p).has_fderiv_at },
  dsimp [partial_fderiv_fst],
  rw funext (λ x : E , funext $ λ t : F, (this (x, t)).partial_fst.fderiv),
  ext ⟨y, t⟩,
  refl
end

lemma differentiable.fderiv_partial_snd {φ : E → F → G} (hF : differentiable 𝕜 (uncurry φ)) :
  ↿(∂₂ 𝕜 φ) = (λ ψ : E × F →L[𝕜] G, ψ.comp (inr 𝕜 E F)) ∘ (fderiv 𝕜 $ uncurry φ) :=
begin
  have : ∀ p : E × F, has_fderiv_at (uncurry φ) _ p,
  { intro p,
    exact (hF p).has_fderiv_at },
  dsimp [partial_fderiv_snd],
  rw funext (λ x : E , funext $ λ t : F, (this (x, t)).partial_snd.fderiv),
  ext ⟨y, t⟩,
  refl
end

/-- The first partial derivative of `φ : 𝕜 → F → G` seen as a function from `𝕜 → F → G`-/
def partial_deriv_fst (φ : 𝕜 → F → G) := λ k f, ∂₁ 𝕜 φ k f 1

/-- The second partial derivative of `φ : E → 𝕜 → G` seen as a function from `E → 𝕜 → G`-/
def partial_deriv_snd (φ : E → 𝕜 → G) := λ e k, ∂₂ 𝕜 φ e k 1

lemma partial_fderiv_fst_eq_smul_right (φ : 𝕜 → F → G) (k : 𝕜) (f : F) :
  ∂₁ 𝕜 φ k f = smul_right (1 : 𝕜 →L[𝕜] 𝕜) (partial_deriv_fst φ k f) := deriv_fderiv.symm

@[simp]
lemma partial_fderiv_fst_one (φ : 𝕜 → F → G) (k : 𝕜) (f : F) :
  ∂₁ 𝕜 φ k f 1 = partial_deriv_fst φ k f :=
by simp only [partial_fderiv_fst_eq_smul_right, smul_right_apply, one_apply, one_smul]

lemma partial_fderiv_snd_eq_smul_right (φ : E → 𝕜 → G) (e : E) (k : 𝕜) :
  ∂₂ 𝕜 φ e k  = smul_right (1 : 𝕜 →L[𝕜] 𝕜) (partial_deriv_snd φ e k) := deriv_fderiv.symm

lemma partial_fderiv_snd_one (φ : E → 𝕜 → G) (e : E) (k : 𝕜) :
  ∂₂ 𝕜 φ e k 1 = partial_deriv_snd φ e k :=
by simp only [partial_fderiv_snd_eq_smul_right, smul_right_apply, one_apply, one_smul]

@[to_additive]
lemma with_top.le_mul_self {α : Type*} [canonically_ordered_monoid α] (n m : α) :
  (n : with_top α) ≤ (m * n : α) :=
with_top.coe_le_coe.mpr le_mul_self

@[to_additive]
lemma with_top.le_self_mul {α : Type*} [canonically_ordered_monoid α] (n m : α) :
  (n : with_top α) ≤ (n * m : α) :=
with_top.coe_le_coe.mpr le_self_mul

lemma cont_diff.cont_diff_partial_fst {φ : E → F → G} {n : ℕ}
  (hF : cont_diff 𝕜 (n + 1) (uncurry φ)) : cont_diff 𝕜 n ↿(∂₁ 𝕜 φ) :=
begin
  cases cont_diff_succ_iff_fderiv.mp hF with hF₁ hF₂,
  rw (hF.one_of_succ.differentiable le_rfl).fderiv_partial_fst,
  apply cont_diff.comp _ hF₂,
  exact ((inl 𝕜 E F).comp_rightL : (E × F →L[𝕜] G) →L[𝕜] E →L[𝕜] G).cont_diff
end

lemma cont_diff.cont_diff_partial_fst_apply {φ : E → F → G} {n : ℕ}
  (hF : cont_diff 𝕜 (n + 1) (uncurry φ)) {x : E} : cont_diff 𝕜 n ↿(λ x' y, ∂₁ 𝕜 φ x' y x) :=
(continuous_linear_map.apply 𝕜 G x).cont_diff.comp hF.cont_diff_partial_fst

lemma cont_diff.continuous_partial_fst {φ : E → F → G} {n : ℕ}
  (h : cont_diff 𝕜 ((n + 1 : ℕ) : with_top ℕ) $ uncurry φ) : continuous ↿(∂₁ 𝕜 φ) :=
h.cont_diff_partial_fst.continuous

lemma cont_diff.cont_diff_top_partial_fst {φ : E → F → G} (hF : cont_diff 𝕜 ⊤ (uncurry φ)) :
  cont_diff 𝕜 ⊤ ↿(∂₁ 𝕜 φ) :=
cont_diff_top.mpr (λ n, (cont_diff_top.mp hF (n + 1)).cont_diff_partial_fst)

lemma cont_diff.cont_diff_partial_snd {φ : E → F → G} {n : ℕ}
  (hF : cont_diff 𝕜 (n + 1) (uncurry φ)) : cont_diff 𝕜 n ↿(∂₂ 𝕜 φ) :=
begin
  cases cont_diff_succ_iff_fderiv.mp hF with hF₁ hF₂,
  rw (hF.one_of_succ.differentiable le_rfl).fderiv_partial_snd,
  apply cont_diff.comp _ hF₂,
  exact ((inr 𝕜 E F).comp_rightL : (E × F →L[𝕜] G) →L[𝕜] F →L[𝕜] G).cont_diff
end

lemma cont_diff.cont_diff_partial_snd_apply {φ : E → F → G} {n : ℕ}
  (hF : cont_diff 𝕜 (n + 1) (uncurry φ)) {y : F} : cont_diff 𝕜 n ↿(λ x y', ∂₂ 𝕜 φ x y' y) :=
(continuous_linear_map.apply 𝕜 G y).cont_diff.comp hF.cont_diff_partial_snd

lemma cont_diff.continuous_partial_snd {φ : E → F → G} {n : ℕ}
  (h : cont_diff 𝕜 ((n + 1 : ℕ) : with_top ℕ) $ uncurry φ) : continuous ↿(∂₂ 𝕜 φ) :=
h.cont_diff_partial_snd.continuous

lemma cont_diff.cont_diff_top_partial_snd {φ : E → F → G} (hF : cont_diff 𝕜 ⊤ (uncurry φ)) :
  cont_diff 𝕜 ⊤ ↿(∂₂ 𝕜 φ) :=
cont_diff_top.mpr (λ n, (cont_diff_top.mp hF (n + 1)).cont_diff_partial_snd)

end calculus

section real_calculus
open continuous_linear_map
variables {E : Type*} [normed_group E] [normed_space ℝ E]
          {F : Type*} [normed_group F] [normed_space ℝ F]

lemma cont_diff.lipschitz_on_with {s : set E} {f : E → F} (hf : cont_diff ℝ 1 f)
  (hs : convex ℝ s) (hs' : is_compact s) : ∃ K, lipschitz_on_with K f s :=
begin
  rcases hs'.bdd_above_norm (hf.continuous_fderiv le_rfl) with ⟨M, M_pos : 0 < M, hM⟩,
  use ⟨M, M_pos.le⟩,
  exact convex.lipschitz_on_with_of_nnnorm_fderiv_le (λ x x_in, hf.differentiable le_rfl x) hM hs
end

end real_calculus


open real continuous_linear_map asymptotics
open_locale topological_space

lemma of_eventually_nhds {X : Type*} [topological_space X] {P : X → Prop} {x₀ : X}
  (h : ∀ᶠ x in 𝓝 x₀, P x) : P x₀ :=
mem_of_mem_nhds h



/- Move this next to cont_diff_smul -/
lemma cont_diff.const_smul {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {E : Type*} [normed_group E] [normed_space 𝕜 E]
  {F : Type*} [normed_group F] [normed_space 𝕜 F]
  {f : E → F} {n : with_top ℕ} (hf : cont_diff 𝕜 n f) (a : 𝕜) :
  cont_diff 𝕜 n (λ x, a • f x) :=
cont_diff_const.smul hf

section

open asymptotics continuous_linear_map filter
open_locale filter

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
          {E : Type*}  {F : Type*} [normed_group F]

lemma filter.eventually_le.is_O {f g h : E → F} {l : filter E}
  (hfg : (λ x, ∥f x∥) ≤ᶠ[l] (λ x, ∥g x∥)) (hh : is_O g h l) : is_O f h l :=
(is_O_iff.mpr ⟨1, by  simpa using hfg⟩).trans hh

lemma filter.eventually.is_O {f g h : E → F} {l : filter E}
  (hfg : ∀ᶠ x in l, ∥f x∥ ≤ ∥g x∥) (hh : is_O g h l) : is_O f h l :=
filter.eventually_le.is_O hfg hh

lemma filter.eventually.is_O' {f : E → F} {g : E → ℝ} {l : filter E}
  (hfg : ∀ᶠ x in l, ∥f x∥ ≤ g x) : is_O f g l :=
begin
  rw is_O_iff,
  use 1,
  apply hfg.mono,
  intros x h,
  rwa [real.norm_eq_abs, abs_of_nonneg ((norm_nonneg $ f x).trans h), one_mul]
end

variables [normed_group E] [normed_space 𝕜 E] [normed_space 𝕜 F]
          {G : Type*} [normed_group G] [normed_space 𝕜 G]

lemma asymptotics.is_O.eq_zero {f : E → F} {x₀ : E} {n : ℕ}
  (h : is_O f (λ x, ∥x - x₀∥^n) (𝓝 x₀)) (hn : 0 < n) : f x₀ = 0 :=
begin
  cases h.is_O_with with c hc,
  have:= mem_of_mem_nhds (is_O_with_iff.mp hc),
  simpa [zero_pow hn]
end

lemma is_o_pow_sub_pow_sub (x₀ : E) {n m : ℕ} (h : n < m) :
    is_o (λ (x : E), ∥x - x₀∥^m) (λ (x : E), ∥x - x₀∥^n) (𝓝 x₀) :=
begin
  have : tendsto (λ x, ∥x - x₀∥) (𝓝 x₀) (𝓝 0),
  { apply tendsto_norm_zero.comp,
    rw ← sub_self x₀,
    exact tendsto_id.sub tendsto_const_nhds },
  exact (is_o_pow_pow h).comp_tendsto this
end

lemma is_o_pow_sub_sub (x₀ : E) {m : ℕ} (h : 1 < m) :
    is_o (λ (x : E), ∥x - x₀∥^m) (λ (x : E), x - x₀) (𝓝 x₀) :=
by simpa only [is_o_norm_right, pow_one] using is_o_pow_sub_pow_sub x₀ h

lemma asymptotics.is_O_sub_prod_left (e₀ : E) (f₀ : F) (l : filter $ E × F) :
  is_O (λ p : E × F, p.1 - e₀) (λ p : E × F, p - (e₀, f₀)) l :=
is_O_of_le l (λ p, le_max_left _ _)

lemma asymptotics.is_O_sub_prod_right (e₀ : E) (f₀ : F) (l : filter $ E × F) :
  is_O (λ p : E × F, p.2 - f₀) (λ p : E × F, p - (e₀, f₀)) l :=
is_O_of_le l (λ p, le_max_right _ _)

lemma asymptotics.is_O_pow_sub_prod_left (e₀ : E) (f₀ : F) (l : filter $ E × F) (n : ℕ) :
  is_O (λ p : E × F, ∥p.1 - e₀∥^n) (λ p : E × F, ∥p - (e₀, f₀)∥^n) l :=
(is_O_norm_norm.mpr $ asymptotics.is_O_sub_prod_left e₀ f₀ l).pow n

lemma asymptotics.is_O_pow_sub_prod_right (e₀ : E) (f₀ : F) (l : filter $ E × F) (n : ℕ) :
  is_O (λ p : E × F, ∥p.2 - f₀∥^n) (λ p : E × F, ∥p - (e₀, f₀)∥^n) l :=
(is_O_norm_norm.mpr $ asymptotics.is_O_sub_prod_right e₀ f₀ l).pow n

lemma asymptotics.is_O.comp_fst {f : E → F} {n : ℕ} {e₀ : E} {l : filter E}
  (h : is_O f (λ e, ∥e - e₀∥^n) l) (g₀ : G) (l' : filter G) :
  is_O (λ p : E × G, f p.1) (λ p, ∥p - (e₀, g₀)∥^n) (l ×ᶠ l') :=
(h.comp_tendsto tendsto_fst).trans (asymptotics.is_O_pow_sub_prod_left _ _ _ _)

lemma asymptotics.is_O.comp_fst_one {f : E → F} {e₀ : E}  {l : filter E}
  (h : is_O f (λ e, ∥e - e₀∥) l) (g₀ : G) (l' : filter G) :
  is_O (λ p : E × G, f p.1) (λ p, ∥p - (e₀, g₀)∥) (l ×ᶠ l') :=
begin
  rw show (λ e, ∥e - e₀∥) = (λ e, ∥e - e₀∥^1), by { ext e, simp } at h,
  simpa using h.comp_fst g₀ l'
end

lemma asymptotics.is_O.comp_snd {f : G → F} {n : ℕ}  {g₀ : G} {l' : filter G}
  (h : is_O f (λ g, ∥g - g₀∥^n) l') (e₀ : E) (l : filter E) :
  is_O (λ p : E × G, f p.2) (λ p, ∥p - (e₀, g₀)∥^n) (l ×ᶠ l') :=
(h.comp_tendsto tendsto_snd).trans (asymptotics.is_O_pow_sub_prod_right _ _ _ _)

lemma asymptotics.is_O.comp_snd_one {f : G → F}  {g₀ : G} {l' : filter G}
  (h : is_O f (λ g, ∥g - g₀∥) l') (e₀ : E) (l : filter E) :
  is_O (λ p : E × G, f p.2) (λ p, ∥p - (e₀, g₀)∥) (l ×ᶠ l') :=
begin
  rw show (λ g, ∥g - g₀∥) = (λ g, ∥g - g₀∥^1), by { ext g, simp } at h,
  simpa using h.comp_snd e₀ l
end

lemma asymptotics.is_O.has_fderiv_at {f : E → F} {x₀ : E} {n : ℕ}
  (h : is_O f (λ x, ∥x - x₀∥^n) (𝓝 x₀)) (hn : 1 < n) :
  has_fderiv_at f (0 : E →L[𝕜] F) x₀ :=
begin
  change is_o _ _ _,
  simp only [h.eq_zero (zero_lt_one.trans hn), sub_zero, zero_apply],
  exact h.trans_is_o (is_o_pow_sub_sub x₀ hn)
end

lemma has_deriv_at.is_O {f : E → F} {x₀ : E} {f' : E →L[𝕜] F} (h : has_fderiv_at f f' x₀) :
  is_O (λ x, f x - f x₀) (λ x, x - x₀) (𝓝 x₀) :=
by simpa using h.is_O.add (is_O_sub f' (𝓝 x₀) x₀)

end

namespace continuous_linear_equiv

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜] {E : Type*} [normed_group E] [normed_space 𝕜 E]
  {F : Type*} [normed_group F] [normed_space 𝕜 F] {G : Type*} [normed_group G] [normed_space 𝕜 G]
  {f : E → F} {n : with_top ℕ}

--todo: protect `continuous_linear_map.cont_diff`/`continuous_linear_equiv.cont_diff`

lemma cont_diff_comp_iff (e : G ≃L[𝕜] E) :
  _root_.cont_diff 𝕜 n (f ∘ e) ↔ _root_.cont_diff 𝕜 n f :=
by simp_rw [← cont_diff_on_univ, ← e.cont_diff_on_comp_iff, preimage_univ]

lemma comp_cont_diff_iff (e : F ≃L[𝕜] G) :
  _root_.cont_diff 𝕜 n (e ∘ f) ↔ _root_.cont_diff 𝕜 n f :=
by simp_rw [← cont_diff_on_univ, ← e.comp_cont_diff_on_iff]

end continuous_linear_equiv


section
open continuous_linear_map

lemma coprod_eq_add {R₁ : Type*} [semiring R₁] {M₁ : Type*} [topological_space M₁]
  [add_comm_monoid M₁] {M₂ : Type*} [topological_space M₂] [add_comm_monoid M₂]
  {M₃ : Type*} [topological_space M₃] [add_comm_monoid M₃] [module R₁ M₁]
  [module R₁ M₂] [module R₁ M₃] [has_continuous_add M₃]
  (f : M₁ →L[R₁] M₃) (g : M₂ →L[R₁] M₃) :
  f.coprod g = (f.comp $ fst R₁ M₁ M₂) + (g.comp $ snd R₁ M₁ M₂) :=
by { ext ; refl }

end

open filter

/-
The lemma below is ridiculously painful, but Patrick isn't patient enough.
-/
lemma const_mul_one_div_lt {ε : ℝ} (ε_pos : 0 < ε) (C : ℝ) : ∀ᶠ (N : ℝ) in at_top, C*∥1/N∥ < ε :=
begin
  have : tendsto (λ N : ℝ, 1/N) at_top (𝓝 0),
  { rw show (λ N : ℝ, 1/N) = λ N, N^(-(1 : ℤ)), by simp,
    exact tendsto_pow_neg_at_top le_rfl },
  rw tendsto_iff_norm_tendsto_zero at this,
  simp only [sub_zero] at this,
  have key := this.const_mul C,
  rw mul_zero at key,
  apply (normed_group.tendsto_nhds_zero.mp key ε ε_pos).mono,
  intros N hN,
  cases le_or_lt (C * ∥1 / N∥) 0 with h h,
  { exact h.trans_lt ε_pos },
  { rwa real.norm_of_nonneg h.le at hN },
end
