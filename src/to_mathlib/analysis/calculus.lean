import analysis.calculus.times_cont_diff
import to_mathlib.topology.tsupport

noncomputable theory

open set function filter
open_locale topological_space

-- stuff about fderiv
section


section

-- forgot to move this lemma
lemma antitone_ball {α} {P : α → Prop} : antitone (λ s : set α, ∀ x ∈ s, P x) :=
λ s t hst h x hx, h x $ hst hx

variables {𝕜 E F H : Type*} [nondiscrete_normed_field 𝕜] [normed_group E]
  [normed_space 𝕜 E] [normed_group F] [normed_space 𝕜 F]
  {f : E → F} {x : E} {f₂ f₂' : 𝕜 → F} {f' : E → E →L[𝕜] F}

theorem times_cont_diff_one_iff_fderiv :
  times_cont_diff 𝕜 1 f ↔ differentiable 𝕜 f ∧ continuous (fderiv 𝕜 f) :=
by simp_rw [show (1 : with_top ℕ) = (0 + 1 : ℕ), from (zero_add 1).symm,
  times_cont_diff_succ_iff_fderiv, show ((0 : ℕ) : with_top ℕ) = 0, from rfl, times_cont_diff_zero]

theorem times_cont_diff_at_one_iff :
  times_cont_diff_at 𝕜 1 f x
  ↔ ∃ f' : E → (E →L[𝕜] F), ∃ u ∈ 𝓝 x, continuous_on f' u ∧ ∀ x ∈ u, has_fderiv_at f (f' x) x :=
by simp_rw [show (1 : with_top ℕ) = (0 + 1 : ℕ), from (zero_add 1).symm,
  times_cont_diff_at_succ_iff_has_fderiv_at, show ((0 : ℕ) : with_top ℕ) = 0, from rfl,
  times_cont_diff_at_zero, exists_mem_and_iff antitone_ball antitone_continuous_on, and_comm]

lemma times_cont_diff.continuous_deriv {n : with_top ℕ} (h : times_cont_diff 𝕜 n f₂) (hn : 1 ≤ n) :
  continuous (deriv f₂) :=
(times_cont_diff_succ_iff_deriv.mp (h.of_le hn)).2.continuous


lemma fderiv_eq (h : ∀ x, has_fderiv_at f (f' x) x) : fderiv 𝕜 f = f' :=
funext $ λ x, (h x).fderiv

lemma deriv_eq (h : ∀ x, has_deriv_at f₂ (f₂' x) x) : deriv f₂ = f₂' :=
funext $ λ x, (h x).deriv

-- lemma times_cont_diff_at.continuous_at_fderiv {n : with_top ℕ}
--   (h : times_cont_diff_at 𝕜 n f x) (hn : 1 ≤ n) :
--   continuous_at (fderiv 𝕜 f) x :=
-- sorry

lemma support_fderiv_subset : support (fderiv 𝕜 f) ⊆ tsupport f :=
begin
  intros x,
  rw [← not_imp_not],
  intro h2x,
  rw [not_mem_closure_support_iff_eventually_eq] at h2x,
  exact nmem_support.mpr (h2x.fderiv_eq.trans $ fderiv_const_apply 0),
end

lemma has_compact_support.fderiv (hf : has_compact_support f) : has_compact_support (fderiv 𝕜 f) :=
hf.mono' support_fderiv_subset

lemma support_deriv_subset : support (deriv f₂) ⊆ tsupport f₂ :=
begin
  intros x,
  rw [← not_imp_not],
  intro h2x,
  rw [not_mem_closure_support_iff_eventually_eq] at h2x,
  exact nmem_support.mpr (h2x.deriv_eq.trans (deriv_const x 0))
end

lemma has_compact_support.deriv (hf : has_compact_support f₂) : has_compact_support (deriv f₂) :=
hf.mono' support_deriv_subset

end

end

section

variables {ι k : Type*} [fintype ι]
variables [nondiscrete_normed_field k] {Z : Type*} [normed_group Z] [normed_space k Z]
variables {m : with_top ℕ}

lemma times_cont_diff_apply (i : ι) :
  times_cont_diff k m (λ (f : ι → Z), f i) :=
(continuous_linear_map.proj i : (ι → Z) →L[k] Z).times_cont_diff

lemma times_cont_diff_apply_apply (i j : ι) :
  times_cont_diff k m (λ (f : ι → ι → Z), f j i) :=
(@times_cont_diff_apply _ _ _ _ Z _ _ m i).comp (@times_cont_diff_apply _ _ _ _ (ι → Z) _ _ m j)

end

lemma is_compact.bdd_above_norm {X : Type*} [topological_space X] {E : Type*} [normed_group E]
  {s : set X} (hs : is_compact s) {f : X → E} (hf : continuous f) : ∃ M > 0, ∀ x ∈ s, ∥f x∥ ≤ M :=
begin
  cases (hs.image (continuous_norm.comp hf)).bdd_above with M hM,
  rcases s.eq_empty_or_nonempty with rfl | ⟨⟨x₀, x₀_in⟩⟩,
  { use [1, zero_lt_one],
    simp },
  { use M + 1,
    split,
    { linarith [(norm_nonneg (f x₀)).trans (hM (set.mem_image_of_mem (norm ∘ f) x₀_in))] },
    { intros x x_in,
      linarith [hM (set.mem_image_of_mem (norm ∘ f) x_in)] } }
end


section calculus
open continuous_linear_map
variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
          {E : Type*} [normed_group E] [normed_space 𝕜 E]
          {F : Type*} [normed_group F] [normed_space 𝕜 F]
          {G : Type*} [normed_group G] [normed_space 𝕜 G]

lemma has_fderiv_at_prod_left (e₀ : E) (f₀ : F) : has_fderiv_at (λ e : E, (e, f₀)) (inl 𝕜 E F) e₀ :=
begin
  rw has_fderiv_at_iff_is_o_nhds_zero,
  simp [asymptotics.is_o_zero]
end

lemma has_fderiv_at.partial_fst {φ : E → F → G} {φ' : E × F →L[𝕜] G} {e₀ : E} {f₀ : F}
  (h : has_fderiv_at (uncurry φ) φ' (e₀, f₀)) :
  has_fderiv_at (λ e, φ e f₀) (φ'.comp (inl 𝕜 E F)) e₀ :=
begin
  rw show (λ e, φ e f₀) = (uncurry φ) ∘ (λ e, (e, f₀)), by { ext e, simp },
  refine h.comp e₀ _,
  apply has_fderiv_at_prod_left
end

variable (𝕜)

def partial_fderiv_fst {F : Type*} (φ : E → F → G) :=
λ (e₀ : E) (f₀ : F), fderiv 𝕜 (λ e, φ e f₀) e₀

notation `∂₁` := partial_fderiv_fst

variable {𝕜}

lemma fderiv_partial_fst {φ : E → F → G} {φ' : E × F →L[𝕜] G} {e₀ : E} {f₀ : F}
  (h : has_fderiv_at (uncurry φ) φ' (e₀, f₀)) :
  ∂₁ 𝕜 φ e₀ f₀ = φ'.comp (inl 𝕜 E F) :=
h.partial_fst.fderiv

lemma times_cont_diff_prod_left (f₀ : F) : times_cont_diff 𝕜 ⊤ (λ e : E, (e, f₀)) :=
begin
  rw times_cont_diff_top_iff_fderiv,
  split,
  { intro e₀,
    exact (has_fderiv_at_prod_left e₀ f₀).differentiable_at },
  { dsimp only,
    rw show fderiv 𝕜 (λ (e : E), (e, f₀)) = λ (e : E), inl 𝕜 E F,
      from  funext (λ e : E, (has_fderiv_at_prod_left e f₀).fderiv),
    exact times_cont_diff_const }
end

lemma has_fderiv_at_prod_mk (e₀ : E) (f₀ : F) : has_fderiv_at (λ f : F, (e₀, f)) (inr 𝕜 E F) f₀ :=
begin
  rw has_fderiv_at_iff_is_o_nhds_zero,
  simp [asymptotics.is_o_zero]
end

lemma has_fderiv_at.partial_snd {φ : E → F → G} {φ' : E × F →L[𝕜] G} {e₀ : E} {f₀ : F}
  (h : has_fderiv_at (uncurry φ) φ' (e₀, f₀)) :
  has_fderiv_at (λ f, φ e₀ f) (φ'.comp (inr 𝕜 E F)) f₀ :=
begin
  rw show (λ f, φ e₀ f) = (uncurry φ) ∘ (λ f, (e₀, f)), by { ext e, simp },
  refine h.comp f₀ _,
  apply has_fderiv_at_prod_mk
end

lemma fderiv_partial_snd {φ : E → F → G} {φ' : E × F →L[𝕜] G} {e₀ : E} {f₀ : F}
  (h : has_fderiv_at (uncurry φ) φ' (e₀, f₀)) :
  fderiv 𝕜 (λ f, φ e₀ f) f₀ = φ'.comp (inr 𝕜 E F) :=
h.partial_snd.fderiv

lemma times_cont_diff_prod_mk (e₀ : E) : times_cont_diff 𝕜 ⊤ (λ f : F, (e₀, f)) :=
begin
  rw times_cont_diff_top_iff_fderiv,
  split,
  { intro f₀,
    exact (has_fderiv_at_prod_mk e₀ f₀).differentiable_at },
  { dsimp only,
    rw show fderiv 𝕜 (λ (f : F), (e₀, f)) = λ (f : F), inr 𝕜 E F,
      from  funext (λ f : F, (has_fderiv_at_prod_mk e₀ f).fderiv),
    exact times_cont_diff_const }
end

lemma times_cont_diff.partial_fst {φ : E → F → G} {n : with_top ℕ}
  (h : times_cont_diff 𝕜 n $ uncurry φ) (f₀ : F) : times_cont_diff 𝕜 n (λ e, φ e f₀) :=
h.comp ((times_cont_diff_prod_left f₀).of_le le_top)

lemma times_cont_diff.partial_snd {φ : E → F → G} {n : with_top ℕ}
  (h : times_cont_diff 𝕜 n $ uncurry φ) (e₀ : E) : times_cont_diff 𝕜 n (λ f, φ e₀ f) :=
h.comp ((times_cont_diff_prod_mk e₀).of_le le_top)

/-- Precomposition by a continuous linear map as a continuous linear map between spaces of
continuous linear maps. -/
def continuous_linear_map.comp_rightL (φ  : E →L[𝕜] F) : (F →L[𝕜] G) →L[𝕜] (E →L[𝕜] G) :=
{ to_fun := λ ψ, ψ.comp φ,
  map_add' := λ x y, add_comp _ _ _,
  map_smul' := λ r x, by rw [smul_comp, ring_hom.id_apply],
  cont := begin
    dsimp only,
    apply @continuous_of_linear_of_bound 𝕜,
    { intros x y,
      apply add_comp },
    { intros c ψ,
      rw smul_comp },
    { intros ψ,
      change ∥ψ.comp φ∥ ≤ ∥φ∥ * ∥ψ∥,
      rw mul_comm,
      apply op_norm_comp_le }
  end }

/-- Postcomposition by a continuous linear map as a continuous linear map between spaces of
continuous linear maps. -/
def continuous_linear_map.comp_leftL (φ  : F →L[𝕜] G) : (E →L[𝕜] F) →L[𝕜] (E →L[𝕜] G) :=
{ to_fun := φ.comp,
  map_add' := λ x y, comp_add _ _ _,
  map_smul' := λ r x, by rw [comp_smul, ring_hom.id_apply],
  cont := begin
    dsimp only,
    apply @continuous_of_linear_of_bound 𝕜,
    { intros x y,
      apply comp_add },
    { intros c ψ,
      rw comp_smul },
    { intros ψ,
      apply op_norm_comp_le }
  end }

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

@[to_additive]
lemma with_top.le_mul_self {α : Type*} [canonically_ordered_monoid α] (n m : α) : (n : with_top α) ≤ (m * n : α) :=
with_top.coe_le_coe.mpr le_mul_self

@[to_additive]
lemma with_top.le_self_mul {α : Type*} [canonically_ordered_monoid α] (n m : α) : (n : with_top α) ≤ (n * m : α) :=
with_top.coe_le_coe.mpr le_self_mul

lemma times_cont_diff.of_succ {φ : E → F} {n : ℕ} (h : times_cont_diff 𝕜 (n + 1) φ) :
  times_cont_diff 𝕜 n φ :=
h.of_le (with_top.le_self_add n 1)

lemma times_cont_diff.one_of_succ {φ : E → F} {n : ℕ} (h : times_cont_diff 𝕜 (n + 1) φ) :
  times_cont_diff 𝕜 1 φ :=
h.of_le (with_top.le_add_self 1 n)

lemma times_cont_diff.times_cont_diff_partial_fst {φ : E → F → G} {n : ℕ}
  (hF : times_cont_diff 𝕜 (n + 1) (uncurry φ)) : times_cont_diff 𝕜 n ↿(∂₁ 𝕜 φ) :=
begin
  cases times_cont_diff_succ_iff_fderiv.mp hF with hF₁ hF₂,
  rw (hF.differentiable $ with_top.le_add_self 1 n).fderiv_partial_fst,
  apply times_cont_diff.comp _ hF₂,
  exact ((inl 𝕜 E F).comp_rightL : (E × F →L[𝕜] G) →L[𝕜] E →L[𝕜] G).times_cont_diff
end

lemma times_cont_diff.times_cont_diff_partial_fst_apply {φ : E → F → G} {n : ℕ}
  (hF : times_cont_diff 𝕜 (n + 1) (uncurry φ)) {x : E} : times_cont_diff 𝕜 n ↿(λ x' y, ∂₁ 𝕜 φ x' y x) :=
(continuous_linear_map.apply 𝕜 G x).times_cont_diff.comp hF.times_cont_diff_partial_fst

lemma times_cont_diff.continuous_partial_fst {φ : E → F → G} {n : ℕ}
  (h : times_cont_diff 𝕜 ((n + 1 : ℕ) : with_top ℕ) $ uncurry φ) : continuous ↿(∂₁ 𝕜 φ) :=
h.times_cont_diff_partial_fst.continuous

lemma times_cont_diff.times_cont_diff_top_partial_fst {φ : E → F → G} (hF : times_cont_diff 𝕜 ⊤ (uncurry φ)) :
  times_cont_diff 𝕜 ⊤ ↿(∂₁ 𝕜 φ) :=
times_cont_diff_top.mpr (λ n, (times_cont_diff_top.mp hF (n + 1)).times_cont_diff_partial_fst)

@[simp] lemma linear_equiv.trans_symm {R M₁ M₂ M₃ : Type*} [semiring R]
  [add_comm_group M₁] [add_comm_group M₂] [add_comm_group M₃]
  [module R M₁] [module R M₂] [module R M₃] (e₁ : M₁ ≃ₗ[R] M₂) (e₂ : M₂ ≃ₗ[R] M₃) :
  (e₁.trans e₂).symm = e₂.symm.trans e₁.symm :=
rfl

@[simp] lemma continuous_linear_equiv.coe_one : (⇑(1 : E ≃L[𝕜] E) : E → E) = id := rfl

@[simp] lemma continuous_linear_equiv.one_symm : (1 : E ≃L[𝕜] E).symm = 1 := rfl

@[simps] def continuous_linear_equiv.arrow_congr_equiv'
  {H : Type*} [normed_group H] [normed_space 𝕜 H] (e₁ : E ≃L[𝕜] G) (e₂ : F ≃L[𝕜] H) :
  (E →L[𝕜] F) ≃L[𝕜] (G →L[𝕜] H) :=
{ map_add' := λ f g, by simp only [equiv.to_fun_as_coe, add_comp, comp_add,
    continuous_linear_equiv.arrow_congr_equiv_apply],
  map_smul' := λ t f, by simp only [equiv.to_fun_as_coe, smul_comp, comp_smulₛₗ,
    continuous_linear_equiv.arrow_congr_equiv_apply],
  continuous_to_fun := (continuous_linear_map.compL 𝕜 G F H (e₂ : F →L[𝕜] H)).continuous.comp
    ((continuous_linear_map.compL 𝕜 G E F).flip (e₁.symm : G →L[𝕜] E)).continuous,
  continuous_inv_fun := (continuous_linear_map.compL 𝕜 E H F (e₂.symm : H →L[𝕜] F)).continuous.comp
    ((continuous_linear_map.compL 𝕜 E G H).flip (e₁ : E →L[𝕜] G)).continuous,
  .. e₁.arrow_congr_equiv e₂, }

variables (ι : Type*) [fintype ι] [decidable_eq ι] [complete_space 𝕜]

@[simps] def continuous_linear_equiv.pi_ring : ((ι → 𝕜) →L[𝕜] G) ≃L[𝕜] (ι → G) :=
{ continuous_to_fun :=
  begin
    refine continuous_pi (λ i, _),
    simp only [linear_equiv.to_fun_eq_coe, linear_equiv.trans_apply,
      linear_map.coe_to_continuous_linear_map_symm, linear_equiv.pi_ring_apply,
      continuous_linear_map.coe_coe],
    exact (continuous_linear_map.apply 𝕜 G (pi.single i 1)).continuous,
  end,
  continuous_inv_fun :=
  begin
    simp only [linear_equiv.inv_fun_eq_symm, linear_equiv.trans_symm, linear_equiv.symm_symm],
    apply linear_map.continuous_of_bound _ (fintype.card ι : ℝ) (λ g, _),
    rw ← nsmul_eq_mul,
    apply op_norm_le_bound _ (nsmul_nonneg (norm_nonneg g) (fintype.card ι)) (λ t, _),
    simp only [linear_map.coe_comp, linear_equiv.coe_to_linear_map, comp_app,
      linear_map.coe_to_continuous_linear_map', linear_equiv.pi_ring_symm_apply],
    apply le_trans (norm_sum_le _ _),
    rw smul_mul_assoc,
    refine finset.sum_le_of_forall_le _ _ _ (λ i hi, _),
    rw [norm_smul, mul_comm],
    exact mul_le_mul (norm_le_pi_norm g i) (norm_le_pi_norm t i) (norm_nonneg _) (norm_nonneg g),
  end,
  .. linear_map.to_continuous_linear_map.symm.trans (linear_equiv.pi_ring 𝕜 G ι 𝕜) }

-- maybe we can do this without finite dimensionality of `F`?
lemma times_cont_diff_clm_apply {n : with_top ℕ} {f : E → F →L[𝕜] G} [finite_dimensional 𝕜 F] :
  times_cont_diff 𝕜 n f ↔ ∀ y, times_cont_diff 𝕜 n (λ x, f x y) :=
begin
  refine ⟨λ h y, (continuous_linear_map.apply 𝕜 G y).times_cont_diff.comp h, λ h, _⟩,
  let d := finite_dimensional.finrank 𝕜 F,
  have hd : finite_dimensional.finrank 𝕜 (fin d → 𝕜) = d := finite_dimensional.finrank_fin_fun 𝕜,
  obtain ⟨e₁⟩ := finite_dimensional.nonempty_continuous_linear_equiv_iff_finrank_eq.mpr hd,
  let e₂ := (e₁.arrow_congr_equiv' (1 : G ≃L[𝕜] G)).symm.trans
    (continuous_linear_equiv.pi_ring (fin d)),
  have he₂ : ∀ i x, e₂ (f x) i = f x (e₁ (pi.single i (1 : 𝕜))), { simp, },
  suffices :  times_cont_diff 𝕜 n (e₂ ∘ f),
  { rw [← comp.left_id f, ← e₂.symm_comp_self, function.comp.assoc],
    exact e₂.symm.times_cont_diff.comp this, },
  refine times_cont_diff_pi.mpr (λ i, _),
  simp only [he₂, comp_app, h _],
end

lemma times_cont_diff_succ_iff_fderiv_apply [finite_dimensional 𝕜 E] {n : ℕ} {f : E → F} :
  times_cont_diff 𝕜 ((n + 1) : ℕ) f ↔
  differentiable 𝕜 f ∧ ∀ y, times_cont_diff 𝕜 n (λ x, fderiv 𝕜 f x y) :=
by rw [times_cont_diff_succ_iff_fderiv, times_cont_diff_clm_apply]


end calculus

section real_calculus
open continuous_linear_map
variables {E : Type*} [normed_group E] [normed_space ℝ E]
          {F : Type*} [normed_group F] [normed_space ℝ F]

lemma times_cont_diff.lipschitz_on_with {s : set E} {f : E → F} (hf : times_cont_diff ℝ 1 f)
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



/- Move this next to times_cont_diff_smul, and think about how to mkae such things much
less painful. -/
lemma times_cont_diff.const_smul {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {E : Type*} [normed_group E] [normed_space 𝕜 E]
  {F : Type*} [normed_group F] [normed_space 𝕜 F]
  {f : E → F} {n : with_top ℕ} (h : times_cont_diff 𝕜 n f) (a : 𝕜) :
  times_cont_diff 𝕜 n (λ x, a • f x) :=
begin
  change times_cont_diff 𝕜 n ((λ p : 𝕜 × F, p.1 • p.2) ∘ (λ y : F, (a, y)) ∘ f),
  apply times_cont_diff.comp,
  exact times_cont_diff_smul,
  apply times_cont_diff.comp _ h,
  exact (times_cont_diff_prod_mk a).of_le le_top
end

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

--todo: protect `continuous_linear_map.times_cont_diff`/`continuous_linear_equiv.times_cont_diff`

lemma times_cont_diff_comp_iff (e : G ≃L[𝕜] E) :
  _root_.times_cont_diff 𝕜 n (f ∘ e) ↔ _root_.times_cont_diff 𝕜 n f :=
by simp_rw [← times_cont_diff_on_univ, ← e.times_cont_diff_on_comp_iff, preimage_univ]

lemma comp_times_cont_diff_iff (e : F ≃L[𝕜] G) :
  _root_.times_cont_diff 𝕜 n (e ∘ f) ↔ _root_.times_cont_diff 𝕜 n f :=
by simp_rw [← times_cont_diff_on_univ, ← e.comp_times_cont_diff_on_iff]

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
  { exact lt_of_le_of_lt h ε_pos },
  { rwa real.norm_of_nonneg h.le at hN },
end
