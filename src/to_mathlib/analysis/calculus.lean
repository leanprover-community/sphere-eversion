import analysis.calculus.specific_functions
import to_mathlib.topology.misc
import to_mathlib.topology.algebra.module

noncomputable theory

open set function filter
open_locale topological_space

namespace real

lemma smooth_transition_proj_I {x : ℝ} :
  smooth_transition (proj_I x) = smooth_transition x :=
begin
  cases le_total (0 : ℝ) x with hx hx,
  cases le_total (1 : ℝ) x with h2x h2x,
  { rw [proj_I_eq_one.mpr h2x, smooth_transition.one_of_one_le h2x, smooth_transition.one], },
  { rw [proj_I_eq_self.mpr ⟨hx, h2x⟩] },
  { rw [proj_I_eq_zero.mpr hx, smooth_transition.zero_of_nonpos hx, smooth_transition.zero], }
end

lemma smooth_transition.continuous_at {x : ℝ} : continuous_at smooth_transition x :=
smooth_transition.continuous.continuous_at

end real

-- section cont_diff_fderiv
/-! In this section we prove that the derivative of a parametric function is smooth, assuming the
  input function is smooth enough. We also do this for `cont_diff_within_at` and `fderiv_within`
  (needed for manifolds)
  We also need some random other lemmas that we didn't bother to put in the right place yet. -/

section fderiv

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
variables {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
variables {F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]
variables {G : Type*} [normed_add_comm_group G] [normed_space 𝕜 G]
variables {X : Type*} [normed_add_comm_group X] [normed_space 𝕜 X]
variables {G' : Type*} [normed_add_comm_group G'] [normed_space 𝕜 G']
variables {f : E → F} {g : E → F} {u : set (E × F)} {s : set E} {x : E} {t : set F} {n m : ℕ∞}

section specific_bilinear_maps

lemma cont_diff.clm_apply {f : E → F →L[𝕜] G} {g : E → F} {n : ℕ∞}
  (hf : cont_diff 𝕜 n f) (hg : cont_diff 𝕜 n g) :
  cont_diff 𝕜 n (λ x, (f x) (g x)) :=
is_bounded_bilinear_map_apply.cont_diff.comp₂ hf hg

lemma cont_diff_on.clm_apply {f : E → F →L[𝕜] G} {g : E → F} {n : ℕ∞}
  (hf : cont_diff_on 𝕜 n f s) (hg : cont_diff_on 𝕜 n g s) :
  cont_diff_on 𝕜 n (λ x, (f x) (g x)) s :=
is_bounded_bilinear_map_apply.cont_diff.comp_cont_diff_on₂ hf hg

lemma cont_diff.smul_right {f : E → F →L[𝕜] 𝕜} {g : E → G} {n : ℕ∞}
  (hf : cont_diff 𝕜 n f) (hg : cont_diff 𝕜 n g) :
  cont_diff 𝕜 n (λ x, (f x).smul_right (g x)) :=
-- giving the following implicit type arguments speeds up elaboration significantly
(@is_bounded_bilinear_map_smul_right 𝕜 _ F _ _ G _ _).cont_diff.comp₂ hf hg

end specific_bilinear_maps

lemma cont_diff_within_at.has_fderiv_within_at_nhds {f : E → F → G} {g : E → F} {u : set (E × F)}
  {t : set F} {n : ℕ}
  (hf : cont_diff_within_at 𝕜 (n+1) (function.uncurry f) u (x, g x))
  (hg : cont_diff_within_at 𝕜 n g s x)
  (hst : insert x s ×ˢ t ⊆ u) -- can be weakened to only consider points near `(x, g x)`
  (hu : u ∈ 𝓝[(λ x, (x, g x)) '' s] (x, g x)) :
  ∃ u ∈ 𝓝[insert x s] x, u ⊆ insert x s ∧ ∃ f' : E → F →L[𝕜] G,
    (∀ x ∈ u, has_fderiv_within_at (f x) (f' x) t (g x)) ∧
    cont_diff_within_at 𝕜 n (λ x, f' x) s x :=
begin
  obtain ⟨v, hv, hvs, f', hvf', hf'⟩ := cont_diff_within_at_succ_iff_has_fderiv_within_at'.mp hf,
  refine ⟨(λ z, (z, g z)) ⁻¹' v ∩ insert x s, _, inter_subset_right _ _,
    λ z, (f' (z, g z)).comp (continuous_linear_map.inr 𝕜 E F), _, _⟩,
  { refine inter_mem _ self_mem_nhds_within,
    have := mem_of_mem_nhds_within (mem_insert _ _) hv,
    refine mem_nhds_within_insert.mpr ⟨this, _⟩,
    refine (continuous_within_at_id.prod hg.continuous_within_at).preimage_mem_nhds_within' _,
    rw [← nhds_within_le_iff] at hu hv ⊢,
    refine (hu.trans $ nhds_within_mono _ $ subset_insert _ _).trans hv },
  { intros z hz,
    have := hvf' (z, g z) hz.1,
    refine this.comp _ (has_fderiv_at_prod_mk_right _ _).has_fderiv_within_at _,
    exact maps_to'.mpr ((image_prod_mk_subset_prod_right hz.2).trans hst) },
  { exact (hf'.continuous_linear_map_comp $ (continuous_linear_map.compL 𝕜 F (E × F) G).flip
      (continuous_linear_map.inr 𝕜 E F)).comp_of_mem x
      (cont_diff_within_at_id.prod hg) hu },
end

lemma cont_diff_within_at.fderiv_within'' {f : E → F → G} {g : E → F} {u : set (E × F)}
  {t : set F} {n : ℕ∞}
  (hf : cont_diff_within_at 𝕜 n (function.uncurry f) u (x, g x))
  (hg : cont_diff_within_at 𝕜 m g s x)
  (ht : ∀ᶠ x' in 𝓝[insert x s] x, unique_diff_within_at 𝕜 t (g x'))
  (hmn : m + 1 ≤ n)
  (hst : insert x s ×ˢ t ⊆ u)
  (hu : u ∈ 𝓝[(λ x', (x', g x')) '' s] (x, g x)) :
  cont_diff_within_at 𝕜 m (λ x', fderiv_within 𝕜 (f x') t (g x')) s x :=
begin
  have : ∀ k : ℕ, (k : with_top ℕ) ≤ m →
    cont_diff_within_at 𝕜 k (λ x, fderiv_within 𝕜 (f x) t (g x)) s x,
  { intros k hkm,
    obtain ⟨v, hv, -, f', hvf', hf'⟩ :=
      (hf.of_le $ (add_le_add_right hkm 1).trans hmn).has_fderiv_within_at_nhds (hg.of_le hkm)
      hst hu,
    refine hf'.congr_of_eventually_eq_insert _,
    filter_upwards [hv, ht],
    exact λ y hy h2y, (hvf' y hy).fderiv_within h2y },
  induction m using with_top.rec_top_coe,
  { obtain rfl := eq_top_iff.mpr hmn,
    rw [cont_diff_within_at_top],
    exact λ m, this m le_top },
  exact this m le_rfl
end

/-- A special case of `cont_diff_within_at.fderiv_within''` where we require that
  `s ∪ {x} ⊆ g⁻¹(t)`. -/
lemma cont_diff_within_at.fderiv_within'2 {f : E → F → G} {g : E → F} {u : set (E × F)}
  {t : set F} {n : ℕ∞}
  (hf : cont_diff_within_at 𝕜 n (function.uncurry f) u (x, g x))
  (hg : cont_diff_within_at 𝕜 m g s x)
  (ht : ∀ᶠ x' in 𝓝[insert x s] x, unique_diff_within_at 𝕜 t (g x'))
  (hmn : m + 1 ≤ n)
  (hst : insert x s ×ˢ t ⊆ u)
  (h2st : s ⊆ g ⁻¹' t) :
  cont_diff_within_at 𝕜 m (λ x, fderiv_within 𝕜 (f x) t (g x)) s x :=
begin
  refine hf.fderiv_within'' hg ht hmn hst _,
  refine mem_of_superset self_mem_nhds_within _,
  refine image_prod_mk_subset_prod.trans _,
  rw [image_id'], rw [← image_subset_iff] at h2st,
  exact (prod_mono (subset_insert x s) h2st).trans hst
end

/-- A special case of `cont_diff_within_at.fderiv_within'` where we require that `x ∈ s` and there
  are unique derivatives everywhere within `t`. -/
lemma cont_diff_within_at.fderiv_within2 {f : E → F → G} {g : E → F} {u : set (E × F)}
  {t : set F} {n : ℕ∞}
  (hf : cont_diff_within_at 𝕜 n (function.uncurry f) u (x, g x))
  (hg : cont_diff_within_at 𝕜 m g s x)
  (ht : unique_diff_on 𝕜 t)
  (hmn : m + 1 ≤ n) (hx : x ∈ s)
  (hst : s ×ˢ t ⊆ u)
  (h2st : s ⊆ g ⁻¹' t) :
  cont_diff_within_at 𝕜 m (λ x, fderiv_within 𝕜 (f x) t (g x)) s x :=
begin
  rw [← insert_eq_self.mpr hx] at hst,
  refine hf.fderiv_within'2 hg _ hmn hst h2st,
  rw [insert_eq_self.mpr hx],
  exact eventually_of_mem self_mem_nhds_within (λ x hx, ht _ (h2st hx))
end

/-- `fderiv` applied to a (variable) vector is smooth at a point within a set. -/
lemma cont_diff_within_at.fderiv_within_apply {f : E → F → G} {g k : E → F} {u : set (E × F)}
  {t : set F} {n : ℕ∞}
  (hf : cont_diff_within_at 𝕜 n (function.uncurry f) u (x, g x))
  (hg : cont_diff_within_at 𝕜 m g s x)
  (hk : cont_diff_within_at 𝕜 m k s x)
  (ht : unique_diff_on 𝕜 t)
  (hmn : m + 1 ≤ n) (hx : x ∈ s)
  (hst : s ×ˢ t ⊆ u)
  (h2st : s ⊆ g ⁻¹' t) :
  cont_diff_within_at 𝕜 m (λ x, fderiv_within 𝕜 (f x) t (g x) (k x)) s x :=
(cont_diff_fst.clm_apply cont_diff_snd).cont_diff_at.comp_cont_diff_within_at x
  ((hf.fderiv_within2 hg ht hmn hx hst h2st).prod hk)

/-- `fderiv_within` is smooth at `x` within `s` (for functions without parameters). -/
lemma cont_diff_within_at.fderiv_within_right
  (hf : cont_diff_within_at 𝕜 n f s x) (hs : unique_diff_on 𝕜 s)
  (hmn : (m + 1 : ℕ∞) ≤ n) (hxs : x ∈ s) :
  cont_diff_within_at 𝕜 m (fderiv_within 𝕜 f s) s x :=
cont_diff_within_at.fderiv_within2
  (cont_diff_within_at.comp (x, x) hf cont_diff_within_at_snd subset_rfl)
  cont_diff_within_at_id hs hmn hxs
  (by { rw [← univ_prod], exact prod_mono (subset_univ _) subset_rfl })
  (by rw [preimage_id'])

/-- `fderiv` is smooth at `x` (for functions without parameters). -/
lemma cont_diff_at.cont_diff_at_fderiv {f : E → F → G} {g : E → F} {n : ℕ∞}
  (hf : cont_diff_at 𝕜 n (function.uncurry f) (x, g x))
  (hg : cont_diff_at 𝕜 m g x)
  (hmn : m + 1 ≤ n) :
  cont_diff_at 𝕜 m (λ x, fderiv 𝕜 (f x) (g x)) x :=
begin
  simp_rw [← fderiv_within_univ],
  refine (cont_diff_within_at.fderiv_within2 hf.cont_diff_within_at hg.cont_diff_within_at
    unique_diff_on_univ hmn (mem_univ x) (subset_univ _) _).cont_diff_at univ_mem,
  rw [preimage_univ]
end

/-- `fderiv` is smooth. -/
lemma cont_diff.fderiv {f : E → F → G} {g : E → F} {n m : ℕ∞}
  (hf : cont_diff 𝕜 m $ function.uncurry f) (hg : cont_diff 𝕜 n g) (hnm : n + 1 ≤ m) :
    cont_diff 𝕜 n (λ x, fderiv 𝕜 (f x) (g x)) :=
cont_diff_iff_cont_diff_at.mpr $ λ x, hf.cont_diff_at.cont_diff_at_fderiv hg.cont_diff_at hnm

/-- `fderiv` is continuous. -/
lemma continuous.fderiv {f : E → F → G} {g : E → F} {n : ℕ∞}
  (hf : cont_diff 𝕜 n $ function.uncurry f) (hg : continuous g) (hn : 1 ≤ n):
    continuous (λ x, fderiv 𝕜 (f x) (g x)) :=
(hf.fderiv (cont_diff_zero.mpr hg) hn).continuous

/-- `fderiv` applied to a (variable) vector is smooth. -/
lemma cont_diff.fderiv_apply {f : E → F → G} {g k : E → F} {n m : ℕ∞}
  (hf : cont_diff 𝕜 m $ function.uncurry f) (hg : cont_diff 𝕜 n g) (hk : cont_diff 𝕜 n k)
  (hnm : n + 1 ≤ m) :
  cont_diff 𝕜 n (λ x, fderiv 𝕜 (f x) (g x) (k x)) :=
(hf.fderiv hg hnm).clm_apply hk

-- the following versions are not exactly ported
lemma cont_diff_within_at_fderiv_within' {f : E → F → G}
  (hf : cont_diff_within_at 𝕜 n (function.uncurry f) u (x, g x))
  (hg : cont_diff_within_at 𝕜 m g s x)
  (ht : unique_diff_on 𝕜 t)
  (hmn : m + 1 ≤ n)
  (hst : insert x s ×ˢ t ⊆ u) -- maybe weaken
  (hgx : ∀ᶠ x' in 𝓝[insert x s] x, g x' ∈ t)
  (hu : u ∈ 𝓝[(λ x, (x, g x)) '' s] (x, g x)) -- remove
  :
  cont_diff_within_at 𝕜 m (λ x, fderiv_within 𝕜 (f x) t (g x)) s x :=
hf.fderiv_within'' hg (hgx.mono (λ y hy, ht _ hy)) hmn hst hu

lemma cont_diff_within_at_fderiv_within {f : E → F → G}
  (hf : cont_diff_within_at 𝕜 n (function.uncurry f) u (x, g x))
  (hg : cont_diff_within_at 𝕜 m g s x)
  (ht : unique_diff_on 𝕜 t)
  (hmn : m + 1 ≤ n) (hx : x ∈ s)
  (hst : s ×ˢ t ⊆ u) -- maybe weaken
  (hgx : ∀ᶠ x' in 𝓝[s] x, g x' ∈ t)
  (hu : u ∈ 𝓝[(λ x, (x, g x)) '' s] (x, g x)) -- remove
  :
  cont_diff_within_at 𝕜 m (λ x, fderiv_within 𝕜 (f x) t (g x)) s x :=
by { rw [← insert_eq_self.mpr hx] at hst hgx,
  exact cont_diff_within_at_fderiv_within' hf hg ht hmn hst hgx hu }

lemma cont_diff_at.fderiv {f : E → F → G}
  (hf : cont_diff_at 𝕜 n (function.uncurry f) (x, g x))
  (hg : cont_diff_at 𝕜 m g x)
  (hmn : m + 1 ≤ n) :
  cont_diff_at 𝕜 m (λ x, fderiv 𝕜 (f x) (g x)) x :=
begin
  simp_rw [← fderiv_within_univ],
  exact (cont_diff_within_at_fderiv_within hf.cont_diff_within_at hg.cont_diff_within_at
    unique_diff_on_univ hmn (mem_univ x) (subset_univ _) (eventually_of_forall (λ x, mem_univ _))
    univ_mem).cont_diff_at univ_mem,
end

end fderiv

section calculus
open continuous_linear_map
variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
          {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
          {E₁ : Type*} [normed_add_comm_group E₁] [normed_space 𝕜 E₁]
          {E₂ : Type*} [normed_add_comm_group E₂] [normed_space 𝕜 E₂]
          {E' : Type*} [normed_add_comm_group E'] [normed_space 𝕜 E']
          {F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]
          {G : Type*} [normed_add_comm_group G] [normed_space 𝕜 G]
          {n : ℕ∞}

lemma cont_diff_at.comp₂ {g : E₁ × E₂ → G} {f₁ : F → E₁} {f₂ : F → E₂} {x : F}
  (hg : cont_diff_at 𝕜 n g (f₁ x, f₂ x)) (hf₁ : cont_diff_at 𝕜 n f₁ x)
  (hf₂ : cont_diff_at 𝕜 n f₂ x) : cont_diff_at 𝕜 n (λ x, g (f₁ x, f₂ x)) x :=
hg.comp x $ hf₁.prod hf₂

lemma cont_diff_at.clm_comp {g : E' → F →L[𝕜] G} {f : E' → E →L[𝕜] F} {n : ℕ∞} {x : E'}
  (hg : cont_diff_at 𝕜 n g x) (hf : cont_diff_at 𝕜 n f x) :
  cont_diff_at 𝕜 n (λ x, g x ∘L f x) x :=
is_bounded_bilinear_map_comp.cont_diff.cont_diff_at.comp₂ hg hf

lemma fderiv_comp {g : F → G} {f : E → F} (x : E)
  (hg : differentiable_at 𝕜 g (f x)) (hf : differentiable_at 𝕜 f x) :
  fderiv 𝕜 (g ∘ f) x = (fderiv 𝕜 g (f x)).comp (fderiv 𝕜 f x) :=
(hg.has_fderiv_at.comp x hf.has_fderiv_at).fderiv

lemma fderiv_prod_left {x₀ : E} {y₀ : F} :
  fderiv 𝕜 (λ x, (x, y₀)) x₀ = continuous_linear_map.inl 𝕜 E F :=
begin
  refine (differentiable_at_id.fderiv_prod (differentiable_at_const y₀)).trans _,
  rw [fderiv_id, fderiv_const],
  refl
end

lemma fderiv_prod_right {x₀ : E} {y₀ : F} :
  fderiv 𝕜 (λ y, (x₀, y)) y₀ = continuous_linear_map.inr 𝕜 E F :=
begin
  refine ((differentiable_at_const x₀).fderiv_prod differentiable_at_id).trans _,
  rw [fderiv_id, fderiv_const],
  refl
end

lemma fderiv_prod_eq_add {f : E × F → G} {p : E × F} (hf : differentiable_at 𝕜 f p) :
  fderiv 𝕜 f p =
  fderiv 𝕜 (λ (z : E × F), f (z.1, p.2)) p + fderiv 𝕜 (λ (z : E × F), f (p.1, z.2)) p :=
begin
  rw [← @prod.mk.eta _ _ p] at hf,
  rw [fderiv_comp p (by apply hf) (differentiable_at_fst.prod $ differentiable_at_const _),
    fderiv_comp p (by apply hf) ((differentiable_at_const _).prod differentiable_at_snd),
    ← continuous_linear_map.comp_add,
    differentiable_at_fst.fderiv_prod (differentiable_at_const _),
    (differentiable_at_const _).fderiv_prod differentiable_at_snd,
    fderiv_fst, fderiv_snd, fderiv_const, fderiv_const],
  dsimp only [pi.zero_apply],
  rw [prod.mk.eta, continuous_linear_map.fst_prod_zero_add_zero_prod_snd,
    continuous_linear_map.comp_id]
end

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

lemma cont_diff.partial_fst {φ : E → F → G} {n : ℕ∞}
  (h : cont_diff 𝕜 n $ uncurry φ) (f₀ : F) : cont_diff 𝕜 n (λ e, φ e f₀) :=
h.comp $ cont_diff_prod_mk_left f₀

lemma cont_diff.partial_snd {φ : E → F → G} {n : ℕ∞}
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
by { ext1 ⟨y, t⟩, exact fderiv_partial_fst (hF ⟨y, t⟩).has_fderiv_at }

lemma differentiable.fderiv_partial_snd {φ : E → F → G} (hF : differentiable 𝕜 (uncurry φ)) :
  ↿(∂₂ 𝕜 φ) = (λ ψ : E × F →L[𝕜] G, ψ.comp (inr 𝕜 E F)) ∘ (fderiv 𝕜 $ uncurry φ) :=
by { ext1 ⟨y, t⟩, exact fderiv_partial_snd (hF ⟨y, t⟩).has_fderiv_at }

/-- The first partial derivative of `φ : 𝕜 → F → G` seen as a function from `𝕜 → F → G`-/
def partial_deriv_fst (φ : 𝕜 → F → G) : 𝕜 → F → G := λ k f, ∂₁ 𝕜 φ k f 1

/-- The second partial derivative of `φ : E → 𝕜 → G` seen as a function from `E → 𝕜 → G`-/
def partial_deriv_snd (φ : E → 𝕜 → G) : E → 𝕜 → G := λ e k, ∂₂ 𝕜 φ e k 1

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
cont_diff.fderiv (hF.comp $ cont_diff_snd.prod cont_diff_fst.snd) cont_diff_fst le_rfl

lemma cont_diff.cont_diff_partial_fst_apply {φ : E → F → G} {n : ℕ}
  (hF : cont_diff 𝕜 (n + 1) (uncurry φ)) {x : E} : cont_diff 𝕜 n ↿(λ x' y, ∂₁ 𝕜 φ x' y x) :=
(continuous_linear_map.apply 𝕜 G x).cont_diff.comp hF.cont_diff_partial_fst

lemma cont_diff.continuous_partial_fst {φ : E → F → G} {n : ℕ}
  (h : cont_diff 𝕜 ((n + 1 : ℕ) : ℕ∞) $ uncurry φ) : continuous ↿(∂₁ 𝕜 φ) :=
h.cont_diff_partial_fst.continuous

lemma cont_diff.cont_diff_top_partial_fst {φ : E → F → G} (hF : cont_diff 𝕜 ⊤ (uncurry φ)) :
  cont_diff 𝕜 ⊤ ↿(∂₁ 𝕜 φ) :=
cont_diff_top.mpr (λ n, (cont_diff_top.mp hF (n + 1)).cont_diff_partial_fst)

lemma cont_diff.cont_diff_partial_snd {φ : E → F → G} {n : ℕ}
  (hF : cont_diff 𝕜 (n + 1) (uncurry φ)) : cont_diff 𝕜 n ↿(∂₂ 𝕜 φ) :=
cont_diff.fderiv (hF.comp $ cont_diff_fst.fst.prod cont_diff_snd) cont_diff_snd le_rfl

lemma cont_diff.cont_diff_partial_snd_apply {φ : E → F → G} {n : ℕ}
  (hF : cont_diff 𝕜 (n + 1) (uncurry φ)) {y : F} : cont_diff 𝕜 n ↿(λ x y', ∂₂ 𝕜 φ x y' y) :=
(continuous_linear_map.apply 𝕜 G y).cont_diff.comp hF.cont_diff_partial_snd

lemma cont_diff.continuous_partial_snd {φ : E → F → G} {n : ℕ}
  (h : cont_diff 𝕜 ((n + 1 : ℕ) : ℕ∞) $ uncurry φ) : continuous ↿(∂₂ 𝕜 φ) :=
h.cont_diff_partial_snd.continuous

lemma cont_diff.cont_diff_top_partial_snd {φ : E → F → G} (hF : cont_diff 𝕜 ⊤ (uncurry φ)) :
  cont_diff 𝕜 ⊤ ↿(∂₂ 𝕜 φ) :=
cont_diff_top.mpr (λ n, (cont_diff_top.mp hF (n + 1)).cont_diff_partial_snd)

end calculus

section real_calculus
open continuous_linear_map
variables {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
          {F : Type*} [normed_add_comm_group F] [normed_space ℝ F]

lemma cont_diff.lipschitz_on_with {s : set E} {f : E → F} {n} (hf : cont_diff ℝ n f) (hn : 1 ≤ n)
  (hs : convex ℝ s) (hs' : is_compact s) : ∃ K, lipschitz_on_with K f s :=
begin
  rcases (bdd_above_iff_exists_ge 0).mp (hs'.image (hf.continuous_fderiv hn).norm).bdd_above with
    ⟨M, M_nonneg, hM⟩,
  simp_rw [ball_image_iff] at hM,
  use ⟨M, M_nonneg⟩,
  exact convex.lipschitz_on_with_of_nnnorm_fderiv_le (λ x x_in, hf.differentiable hn x) hM hs
end

end real_calculus

open filter

/-
The lemma below is ridiculously painful, but Patrick isn't patient enough.
-/
lemma const_mul_one_div_lt {ε : ℝ} (ε_pos : 0 < ε) (C : ℝ) : ∀ᶠ (N : ℝ) in at_top, C*‖1/N‖ < ε :=
begin
  have : tendsto (λ N : ℝ, 1/N) at_top (𝓝 0),
  { rw show (λ N : ℝ, 1/N) = λ N, N^(-(1 : ℤ)), by simp,
    exact tendsto_pow_neg_at_top one_ne_zero },
  rw tendsto_iff_norm_tendsto_zero at this,
  simp only [sub_zero] at this,
  have key := this.const_mul C,
  rw mul_zero at key,
  apply (normed_add_comm_group.tendsto_nhds_zero.mp key ε ε_pos).mono,
  intros N hN,
  cases le_or_lt (C * ‖1 / N‖) 0 with h h,
  { exact h.trans_lt ε_pos },
  { rwa real.norm_of_nonneg h.le at hN },
end
