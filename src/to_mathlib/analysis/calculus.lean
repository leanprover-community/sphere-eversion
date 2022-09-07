import analysis.calculus.specific_functions
import to_mathlib.topology.misc

noncomputable theory

open set function filter
open_locale topological_space

lemma is_compact.bdd_above_norm {X : Type*} [topological_space X] {E : Type*} [normed_add_comm_group E]
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

section cont_diff_fderiv
/-! In this section we prove that the derivative of a parametric function is smooth, assuming the
  input function is smooth enough. We also do this for `cont_diff_within_at` and `fderiv_within`
  (needed for manifolds)
  We also need some random other lemmas that we didn't bother to put in the right place yet. -/


namespace set

variables {α β γ δ : Type*}
lemma image_prod_mk_subset_prod {f : α → β} {g : α → γ} {s : set α} :
  (λ x, (f x, g x)) '' s ⊆ (f '' s) ×ˢ (g '' s) :=
by { rintros _ ⟨x, hx, rfl⟩, exact mk_mem_prod (mem_image_of_mem f hx) (mem_image_of_mem g hx) }

lemma maps_to.subset_preimage {f : α → β} {s : set α} {t : set β} (hf : maps_to f s t) :
  s ⊆ f ⁻¹' t := hf

end set
open set


namespace asymptotics
variables {α E F E' F' : Type*} [topological_space α] [has_norm E] [has_norm E']
variables [seminormed_add_comm_group F] [seminormed_add_comm_group F']
variables {x : α} {s : set α}

lemma is_O_with_insert {C : ℝ} {g : α → E} {g' : α → E'} (h : ∥g x∥ ≤ C * ∥g' x∥) :
  is_O_with C (𝓝[insert x s] x) g g' ↔ is_O_with C (𝓝[s] x) g g' :=
by simp_rw [is_O_with, nhds_within_insert, eventually_sup, eventually_pure, h, true_and]

lemma is_o_insert {g : α → F} {g' : α → F'} (h : g x = 0) :
  g =o[𝓝[insert x s] x] g' ↔ g =o[𝓝[s] x] g' :=
begin
  simp_rw [is_o],
  refine forall_congr (λ c, forall_congr (λ hc, _)),
  rw [is_O_with_insert],
  rw [h, norm_zero],
  exact mul_nonneg hc.le (norm_nonneg _)
end

end asymptotics


section fderiv

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
variables {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
variables {F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]
variables {G : Type*} [normed_add_comm_group G] [normed_space 𝕜 G]
variables {G' : Type*} [normed_add_comm_group G'] [normed_space 𝕜 G']


section -- basic topology

variables {α β : Type*} [topological_space α] [topological_space β] {x y : α} {s s' t : set α}

lemma insert_mem_nhds_within_of_subset_insert [t1_space α] (hu : t ⊆ insert y s) :
  insert x s ∈ 𝓝[t] x :=
begin
  rcases eq_or_ne x y with rfl|h,
  { exact mem_of_superset self_mem_nhds_within hu },
  rw [← union_singleton, union_comm, ← diff_subset_iff, diff_eq] at hu,
  exact mem_of_superset (inter_mem_nhds_within _ (compl_singleton_mem_nhds h))
    (hu.trans (subset_insert _ _)),
end

lemma prod_mem_nhds_within {t t' : set β} {x : α × β}
  (hs : s ∈ 𝓝[s'] x.1) (ht : t ∈ 𝓝[t'] x.2) : s ×ˢ t ∈ 𝓝[s' ×ˢ t'] x :=
begin
  rw [mem_nhds_within] at hs ht ⊢,
  obtain ⟨u, hu, hxu, hus⟩ := hs,
  obtain ⟨v, hv, hxv, hvt⟩ := ht,
  exact ⟨u ×ˢ v, hu.prod hv, ⟨hxu, hxv⟩, prod_inter_prod.subset.trans $ prod_mono hus hvt⟩,
end


end

section

variables {f : E → F} {s : set E} {x : E} {f' : E →L[𝕜] F} {n : ℕ∞}

theorem has_fderiv_within_at.comp_of_mem {g : F → G} {g' : F →L[𝕜] G} {t : set F}
  (hg : has_fderiv_within_at g g' t (f x)) (hf : has_fderiv_within_at f f' s x)
  (hst : tendsto f (𝓝[s] x) (𝓝[t] f x)) :
  has_fderiv_within_at (g ∘ f) (g'.comp f') s x :=
has_fderiv_at_filter.comp x hg hf hst

lemma cont_diff_within_at.comp_of_mem
  {s : set E} {t : set F} {g : F → G} {f : E → F} (x : E)
  (hg : cont_diff_within_at 𝕜 n g t (f x))
  (hf : cont_diff_within_at 𝕜 n f s x) (hs : t ∈ 𝓝[f '' s] f x) :
  cont_diff_within_at 𝕜 n (g ∘ f) s x :=
(hg.mono_of_mem hs).comp x hf (subset_preimage_image f s)

end


variables {f : G → E → F} {g : G → E} {s : set G} {t : set E} {x : G} {n m : ℕ∞} {u : set (G × E)}


lemma has_fderiv_within_at_insert {g' : G →L[𝕜] E} :
  has_fderiv_within_at g g' (insert x s) x ↔ has_fderiv_within_at g g' s x :=
begin
  simp_rw [has_fderiv_within_at, has_fderiv_at_filter],
  rw [asymptotics.is_o_insert],
  simp only [sub_self, g'.map_zero]
end

alias has_fderiv_within_at_insert ↔ has_fderiv_within_at.of_insert has_fderiv_within_at.insert

lemma cont_diff_within_at_insert :
  cont_diff_within_at 𝕜 n g (insert x s) x ↔ cont_diff_within_at 𝕜 n g s x :=
by simp_rw [cont_diff_within_at, insert_eq_of_mem (mem_insert _ _)]

alias cont_diff_within_at_insert ↔ cont_diff_within_at.of_insert cont_diff_within_at.insert

lemma has_fderiv_within_at_diff_singleton {g' : G →L[𝕜] E} :
  has_fderiv_within_at g g' (s \ {x}) x ↔ has_fderiv_within_at g g' s x :=
by rw [← has_fderiv_within_at_insert, insert_diff_singleton, has_fderiv_within_at_insert]

-- replaces 2 mathlib lemmas
lemma cont_diff_within_at_succ_iff_has_fderiv_within_at_of_mem' {f : E → F} {s : set E} {x : E}
  {n : ℕ} :
  cont_diff_within_at 𝕜 (n + 1 : ℕ) f s x
  ↔ ∃ u ∈ 𝓝[insert x s] x, u ⊆ insert x s ∧ ∃ f' : E → E →L[𝕜] F,
    (∀ x ∈ u, has_fderiv_within_at f (f' x) s x) ∧ cont_diff_within_at 𝕜 n f' s x :=
begin
  refine ⟨λ hf, hf.has_fderiv_within_at_nhds, _⟩,
  rw [← cont_diff_within_at_insert, cont_diff_within_at_succ_iff_has_fderiv_within_at,
    insert_eq_of_mem (mem_insert _ _)],
  rintro ⟨u, hu, hus, f', huf', hf'⟩,
  refine ⟨u, hu, f', λ y hy, (huf' y hy).insert.mono_of_mem _, hf'.insert.mono hus⟩,
  exact insert_mem_nhds_within_of_subset_insert hus,
end

/-- One direction of `cont_diff_within_at_succ_iff_has_fderiv_within_at`, but where all derivatives
  are taken within the same set. Version for partial derivatives. -/
lemma cont_diff_within_at.has_fderiv_within_at_nhds₂ {n : ℕ}
  (hf : cont_diff_within_at 𝕜 (n+1) (function.uncurry f) u (x, g x))
  (hg : cont_diff_within_at 𝕜 n g s x)
  (hst : insert x s ×ˢ t ⊆ u) -- can be weakened to only consider points near `(x, g x)`
  (hu : u ∈ 𝓝[(λ x, (x, g x)) '' s] (x, g x)) :
  ∃ u ∈ 𝓝[insert x s] x, u ⊆ insert x s ∧ ∃ f' : G → E →L[𝕜] F,
    (∀ x ∈ u, has_fderiv_within_at (f x) (f' x) t (g x)) ∧
    cont_diff_within_at 𝕜 n (λ x, f' x) s x :=
begin
  obtain ⟨v, hv, hvs, f', hvf', hf'⟩ := hf.has_fderiv_within_at_nhds,
  refine ⟨(λ z, (z, g z)) ⁻¹' v ∩ insert x s, _, inter_subset_right _ _,
    λ z, (f' (z, g z)).comp (continuous_linear_map.inr 𝕜 G E), _, _⟩,
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
  { exact (hf'.continuous_linear_map_comp $ (continuous_linear_map.compL 𝕜 E (G × E) F).flip
      (continuous_linear_map.inr 𝕜 G E)).comp_of_mem x
      (cont_diff_within_at_id.prod hg) hu },
end

-- simplify/replace mathlib lemmas using this
lemma cont_diff_within_at.fderiv_within₂'
  (hf : cont_diff_within_at 𝕜 n (function.uncurry f) u (x, g x))
  (hg : cont_diff_within_at 𝕜 m g s x)
  (ht : ∀ᶠ y in 𝓝[insert x s] x, unique_diff_within_at 𝕜 t (g y))
  (hmn : m + 1 ≤ n)
  (hst : insert x s ×ˢ t ⊆ u)
  (hu : u ∈ 𝓝[(λ x, (x, g x)) '' s] (x, g x)) :
  cont_diff_within_at 𝕜 m (λ x, fderiv_within 𝕜 (f x) t (g x)) s x :=
begin
  have : ∀ k : ℕ, (k : with_top ℕ) ≤ m →
    cont_diff_within_at 𝕜 k (λ x, fderiv_within 𝕜 (f x) t (g x)) s x,
  { intros k hkm,
    obtain ⟨v, hv, -, f', hvf', hf'⟩ :=
      (hf.of_le $ (add_le_add_right hkm 1).trans hmn).has_fderiv_within_at_nhds₂ (hg.of_le hkm)
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

lemma cont_diff_within_at_fderiv_within'
  (hf : cont_diff_within_at 𝕜 n (function.uncurry f) u (x, g x))
  (hg : cont_diff_within_at 𝕜 m g s x)
  (ht : unique_diff_on 𝕜 t)
  (hmn : m + 1 ≤ n)
  (hst : insert x s ×ˢ t ⊆ u) -- maybe weaken
  (hgx : ∀ᶠ x' in 𝓝[insert x s] x, g x' ∈ t)
  (hu : u ∈ 𝓝[(λ x, (x, g x)) '' s] (x, g x)) -- remove
  :
  cont_diff_within_at 𝕜 m (λ x, fderiv_within 𝕜 (f x) t (g x)) s x :=
hf.fderiv_within₂' hg (hgx.mono (λ y hy, ht _ hy)) hmn hst hu
-- $
--   begin
--     have := nhds_within_le_comap (continuous_within_at_id.prod hg.continuous_within_at),
--     have := hgx.filter_mono (nhds_within_mono _ $ subset_insert _ _),
--     refine mem_of_superset (inter_mem self_mem_nhds_within _) _,

--   end

lemma cont_diff_within_at_fderiv_within
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

lemma cont_diff_at.cont_diff_at_fderiv
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

lemma cont_diff.fderiv {f : E → F → G} {g : E → F} {n m : ℕ∞}
  (hf : cont_diff 𝕜 m $ uncurry f) (hg : cont_diff 𝕜 n g) (hnm : n + 1 ≤ m) :
    cont_diff 𝕜 n (λ x, fderiv 𝕜 (f x) (g x)) :=
cont_diff_iff_cont_diff_at.mpr $ λ x, hf.cont_diff_at.cont_diff_at_fderiv hg.cont_diff_at hnm

lemma continuous.fderiv {f : E → F → G} {g : E → F} {n : ℕ∞}
  (hf : cont_diff 𝕜 n $ uncurry f) (hg : continuous g) (hn : 1 ≤ n):
    continuous (λ x, fderiv 𝕜 (f x) (g x)) :=
(hf.fderiv (cont_diff_zero.mpr hg) hn).continuous

end fderiv

end cont_diff_fderiv

section calculus
open continuous_linear_map
variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
          {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
          {F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]
          {G : Type*} [normed_add_comm_group G] [normed_space 𝕜 G]
          {n : ℕ∞}

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
  (h : cont_diff 𝕜 ((n + 1 : ℕ) : ℕ∞) $ uncurry φ) : continuous ↿(∂₁ 𝕜 φ) :=
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

section

open asymptotics continuous_linear_map filter
open_locale filter

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
          {E : Type*}  {F : Type*} [normed_add_comm_group F]

lemma filter.eventually_le.is_O {f g h : E → F} {l : filter E}
  (hfg : (λ x, ∥f x∥) ≤ᶠ[l] λ x, ∥g x∥) (hh : g =O[l] h) : f =O[l] h :=
(is_O_iff.mpr ⟨1, by  simpa using hfg⟩).trans hh

lemma filter.eventually.is_O {f g h : E → F} {l : filter E}
  (hfg : ∀ᶠ x in l, ∥f x∥ ≤ ∥g x∥) (hh : g =O[l] h) : f =O[l] h :=
filter.eventually_le.is_O hfg hh

lemma filter.eventually.is_O' {f : E → F} {g : E → ℝ} {l : filter E}
  (hfg : ∀ᶠ x in l, ∥f x∥ ≤ g x) : f =O[l] g :=
begin
  rw is_O_iff,
  use 1,
  apply hfg.mono,
  intros x h,
  rwa [real.norm_eq_abs, abs_of_nonneg ((norm_nonneg $ f x).trans h), one_mul]
end

variables [normed_add_comm_group E] [normed_space 𝕜 E] [normed_space 𝕜 F]
          {G : Type*} [normed_add_comm_group G] [normed_space 𝕜 G]

lemma asymptotics.is_O.eq_zero {f : E → F} {x₀ : E} {n : ℕ}
  (h : f =O[𝓝 x₀] λ x, ∥x - x₀∥^n) (hn : 0 < n) : f x₀ = 0 :=
begin
  cases h.is_O_with with c hc,
  have:= mem_of_mem_nhds (is_O_with_iff.mp hc),
  simpa [zero_pow hn]
end

lemma is_o_pow_sub_pow_sub (x₀ : E) {n m : ℕ} (h : n < m) :
    (λ (x : E), ∥x - x₀∥^m) =o[𝓝 x₀] λ (x : E), ∥x - x₀∥^n :=
begin
  have : tendsto (λ x, ∥x - x₀∥) (𝓝 x₀) (𝓝 0),
  { apply tendsto_norm_zero.comp,
    rw ← sub_self x₀,
    exact tendsto_id.sub tendsto_const_nhds },
  exact (is_o_pow_pow h).comp_tendsto this
end

lemma is_o_pow_sub_sub (x₀ : E) {m : ℕ} (h : 1 < m) :
    (λ (x : E), ∥x - x₀∥^m) =o[𝓝 x₀] λ (x : E), x - x₀ :=
by simpa only [is_o_norm_right, pow_one] using is_o_pow_sub_pow_sub x₀ h

lemma asymptotics.is_O_sub_prod_left (e₀ : E) (f₀ : F) (l : filter $ E × F) :
  (λ p : E × F, p.1 - e₀) =O[l] λ p : E × F, p - (e₀, f₀) :=
is_O_of_le l (λ p, le_max_left _ _)

lemma asymptotics.is_O_sub_prod_right (e₀ : E) (f₀ : F) (l : filter $ E × F) :
  (λ p : E × F, p.2 - f₀) =O[l] λ p : E × F, p - (e₀, f₀) :=
is_O_of_le l (λ p, le_max_right _ _)

lemma asymptotics.is_O_pow_sub_prod_left (e₀ : E) (f₀ : F) (l : filter $ E × F) (n : ℕ) :
  (λ p : E × F, ∥p.1 - e₀∥^n) =O[l] λ p : E × F, ∥p - (e₀, f₀)∥^n :=
(is_O_norm_norm.mpr $ asymptotics.is_O_sub_prod_left e₀ f₀ l).pow n

lemma asymptotics.is_O_pow_sub_prod_right (e₀ : E) (f₀ : F) (l : filter $ E × F) (n : ℕ) :
  (λ p : E × F, ∥p.2 - f₀∥^n) =O[l] λ p : E × F, ∥p - (e₀, f₀)∥^n :=
(is_O_norm_norm.mpr $ asymptotics.is_O_sub_prod_right e₀ f₀ l).pow n

lemma asymptotics.is_O.comp_fst {f : E → F} {n : ℕ} {e₀ : E} {l : filter E}
  (h : f =O[l] λ e, ∥e - e₀∥^n) (g₀ : G) (l' : filter G) :
  (λ p : E × G, f p.1) =O[l ×ᶠ l'] λ p, ∥p - (e₀, g₀)∥^n :=
(h.comp_tendsto tendsto_fst).trans (asymptotics.is_O_pow_sub_prod_left _ _ _ _)

lemma asymptotics.is_O.comp_fst_one {f : E → F} {e₀ : E}  {l : filter E}
  (h : f =O[l] λ e, ∥e - e₀∥) (g₀ : G) (l' : filter G) :
  (λ p : E × G, f p.1) =O[l ×ᶠ l'] λ p, ∥p - (e₀, g₀)∥ :=
begin
  rw show (λ e, ∥e - e₀∥) = (λ e, ∥e - e₀∥^1), by { ext e, simp } at h,
  simpa using h.comp_fst g₀ l'
end

lemma asymptotics.is_O.comp_snd {f : G → F} {n : ℕ}  {g₀ : G} {l' : filter G}
  (h : f =O[l'] λ g, ∥g - g₀∥^n) (e₀ : E) (l : filter E) :
  (λ p : E × G, f p.2) =O[l ×ᶠ l'] λ p, ∥p - (e₀, g₀)∥^n :=
(h.comp_tendsto tendsto_snd).trans (asymptotics.is_O_pow_sub_prod_right _ _ _ _)

lemma asymptotics.is_O.comp_snd_one {f : G → F}  {g₀ : G} {l' : filter G}
  (h : f =O[l'] λ g, ∥g - g₀∥) (e₀ : E) (l : filter E) :
  (λ p : E × G, f p.2) =O[l ×ᶠ l'] λ p, ∥p - (e₀, g₀)∥ :=
begin
  rw show (λ g, ∥g - g₀∥) = (λ g, ∥g - g₀∥^1), by { ext g, simp } at h,
  simpa using h.comp_snd e₀ l
end

lemma asymptotics.is_O.has_fderiv_at {f : E → F} {x₀ : E} {n : ℕ}
  (h : f =O[𝓝 x₀] λ x, ∥x - x₀∥^n) (hn : 1 < n) :
  has_fderiv_at f (0 : E →L[𝕜] F) x₀ :=
begin
  change is_o _ _ _,
  simp only [h.eq_zero (zero_lt_one.trans hn), sub_zero, zero_apply],
  exact h.trans_is_o (is_o_pow_sub_sub x₀ hn)
end

lemma has_deriv_at.is_O {f : E → F} {x₀ : E} {f' : E →L[𝕜] F} (h : has_fderiv_at f f' x₀) :
  (λ x, f x - f x₀) =O[𝓝 x₀] λ x, x - x₀ :=
by simpa using h.is_O.add (is_O_sub f' (𝓝 x₀) x₀)

end

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
    exact tendsto_pow_neg_at_top one_ne_zero },
  rw tendsto_iff_norm_tendsto_zero at this,
  simp only [sub_zero] at this,
  have key := this.const_mul C,
  rw mul_zero at key,
  apply (normed_add_comm_group.tendsto_nhds_zero.mp key ε ε_pos).mono,
  intros N hN,
  cases le_or_lt (C * ∥1 / N∥) 0 with h h,
  { exact h.trans_lt ε_pos },
  { rwa real.norm_of_nonneg h.le at hN },
end
