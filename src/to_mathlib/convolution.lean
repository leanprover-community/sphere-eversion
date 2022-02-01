import measure_theory.integral.interval_integral
import measure_theory.group.action
import measure_theory.group.prod
import to_mathlib.measure_theory.parametric_interval_integral
import analysis.calculus.fderiv_measurable

noncomputable theory
open topological_space measure_theory measure_theory.measure function set
open_locale pointwise topological_space nnreal measure_theory

lemma iff.not {p q : Prop} (h : p ↔ q) : ¬ p ↔ ¬ q :=
not_iff_not.mpr h

namespace set

variables {α : Type*} {s : set α} {x : α}

lemma compl_ne_univ : sᶜ ≠ univ ↔ s.nonempty :=
compl_univ_iff.not.trans ne_empty_iff_nonempty

lemma not_mem_compl_iff  : x ∉ sᶜ ↔ x ∈ s := not_not

lemma antitone_ball {P : α → Prop} : antitone (λ s : set α, ∀ x ∈ s, P x) :=
λ s t hst h x hx, h x $ hst hx

end set
open set

section

variables {α M : Type*} {s : set α} [has_one M]

@[to_additive] lemma mul_support_disjoint_iff {f : α → M} {s : set α} :
  disjoint (mul_support f) s ↔ ∀ x ∈ s, f x = 1 :=
by simp_rw [disjoint_iff_subset_compl_right, mul_support_subset_iff', not_mem_compl_iff]

@[to_additive] lemma disjoint_mul_support_iff {f : α → M} {s : set α} :
  disjoint s (mul_support f) ↔ ∀ x ∈ s, f x = 1 :=
by rw [disjoint.comm, mul_support_disjoint_iff]

@[to_additive] lemma mul_support_disjoint_iff_eq_on {f : α → M} {s : set α} :
  disjoint (mul_support f) s ↔ eq_on f 1 s :=
mul_support_disjoint_iff

@[to_additive] lemma disjoint_mul_support_iff_eq_on {f : α → M} {s : set α} :
  disjoint s (mul_support f) ↔ eq_on f 1 s :=
disjoint_mul_support_iff

end

namespace filter

variables {α : Type*} {f : filter α}

lemma exists_mem_and_iff {P : set α → Prop} {Q : set α → Prop} (hP : antitone P) (hQ : antitone Q) :
  (∃ u ∈ f, P u) ∧ (∃ u ∈ f, Q u) ↔ (∃ u ∈ f, P u ∧ Q u) :=
begin
  split,
  { rintro ⟨⟨u, huf, hPu⟩, v, hvf, hQv⟩, exact ⟨u ∩ v, inter_mem huf hvf,
    hP (inter_subset_left _ _) hPu, hQ (inter_subset_right _ _) hQv⟩ },
  { rintro ⟨u, huf, hPu, hQu⟩, exact ⟨⟨u, huf, hPu⟩, u, huf, hQu⟩ }
end

end filter
open filter (hiding map_map map_id map map_id')

section

variables {α β γ : Type*} [topological_space α] [topological_space β] {f : α → β}
lemma antitone_continuous_on : antitone (continuous_on f) :=
λ s t hst hf, hf.mono hst

end

section

variables {α β γ : Type*} [topological_space α] [has_one β] [has_one γ]
variables {g : β → γ} {f : α → β} {x : α}

@[to_additive]
lemma not_mem_closure_mul_support_iff_eventually_eq : x ∉ closure (mul_support f) ↔ f =ᶠ[𝓝 x] 1 :=
by simp_rw [mem_closure_iff_nhds, not_forall, not_nonempty_iff_eq_empty,
    ← disjoint_iff_inter_eq_empty, disjoint_mul_support_iff_eq_on, eventually_eq_iff_exists_mem]

/-- A function `f` *has compact multiplicative support* or is *compactly supported* if the closure
of the multiplicative support of `f` is compact. In other words: `f` is equal to `1` outside a
compact set. -/
@[to_additive
/-" A function `f` *has compact support* or is *compactly supported* if the closure of the support
of `f` is compact. In other words: `f` is equal to `0` outside a compact set. "-/]
def has_compact_mul_support (f : α → β) : Prop :=
is_compact (closure (mul_support f))

@[to_additive]
lemma has_compact_mul_support_def :
  has_compact_mul_support f ↔ is_compact (closure (mul_support f)) :=
by refl

@[to_additive]
lemma has_compact_mul_support.mono' {f' : α → γ} (hf : has_compact_mul_support f)
  (hff' : mul_support f' ⊆ closure (mul_support f)) : has_compact_mul_support f' :=
compact_of_is_closed_subset hf is_closed_closure $ closure_minimal hff' is_closed_closure

@[to_additive]
lemma has_compact_mul_support.mono {f' : α → γ} (hf : has_compact_mul_support f)
  (hff' : mul_support f' ⊆ mul_support f) : has_compact_mul_support f' :=
hf.mono' $ hff'.trans subset_closure

@[to_additive]
lemma has_compact_mul_support.comp_left (hf : has_compact_mul_support f) (hg : g 1 = 1) :
  has_compact_mul_support (g ∘ f) :=
hf.mono $ mul_support_comp_subset hg f

@[to_additive]
lemma has_compact_mul_support_comp_left (hg : ∀ {x}, g x = 1 ↔ x = 1) :
  has_compact_mul_support (g ∘ f) ↔ has_compact_mul_support f :=
by simp_rw [has_compact_mul_support, mul_support_comp_eq g @hg f]



end

section

variables {α β : Type*} [topological_space α] [normed_group β]
variables {f : α → β} {x : α}

lemma has_compact_support_norm_iff : has_compact_support (λ x, ∥ f x ∥) ↔ has_compact_support f :=
has_compact_support_comp_left $ λ x, norm_eq_zero

alias has_compact_support_norm_iff ↔ _ has_compact_support.norm

end

section

variables {α β : Type*} [conditionally_complete_linear_order α] [topological_space α]
  [order_topology α] [topological_space β]

-- topology.algebra.ordered.compact
/-- The **extreme value theorem**: if a continuous function `f` is larger than a value in its range
away from compact sets, then it has a global minimum. -/
lemma continuous.exists_forall_le' {f : β → α} (hf : continuous f) (x₀ : β)
  (h : ∀ᶠ x in cocompact β, f x₀ ≤ f x) : ∃ (x : β), ∀ (y : β), f x ≤ f y :=
begin
  obtain ⟨K : set β, hK : is_compact K, hKf : ∀ x ∉ K, f x₀ ≤ f x⟩ :=
  (has_basis_cocompact.eventually_iff).mp h,
  obtain ⟨x, -, hx⟩ : ∃ x ∈ insert x₀ K, ∀ y ∈ insert x₀ K, f x ≤ f y :=
  (hK.insert x₀).exists_forall_le (nonempty_insert _ _) hf.continuous_on,
  refine ⟨x, λ y, _⟩,
  by_cases hy : y ∈ K,
  exacts [hx y (or.inr hy), (hx _ (or.inl rfl)).trans (hKf y hy)]
end

-- better proof
lemma continuous.exists_forall_le'' [nonempty β] {f : β → α}
  (hf : continuous f) (hlim : tendsto f (cocompact β) at_top) :
  ∃ x, ∀ y, f x ≤ f y :=
by { inhabit β, exact hf.exists_forall_le' default (hlim.eventually $ eventually_ge_at_top _) }

lemma continuous.exists_forall_le_of_has_compact_support [nonempty β] [has_zero α]
  {f : β → α} (hf : continuous f) (h : has_compact_support f) :
  ∃ (x : β), ∀ (y : β), f x ≤ f y :=
begin
  -- we use `continuous.exists_forall_le'` with as `x₀` any element outside the support of `f`,
  -- if such an element exists (and otherwise an arbitrary element).
  refine hf.exists_forall_le' (classical.epsilon $ λ x, f x = 0)
    (eventually_of_mem h.compl_mem_cocompact $ λ x hx, _),
  have : f x = 0 := nmem_support.mp (mt (λ h2x, subset_closure h2x) hx),
  exact ((classical.epsilon_spec ⟨x, this⟩).trans this.symm).le
end

lemma continuous.exists_forall_ge_of_has_compact_support [nonempty β] [has_zero α]
  {f : β → α} (hf : continuous f) (h : has_compact_support f) :
  ∃ (x : β), ∀ (y : β), f y ≤ f x :=
@continuous.exists_forall_le_of_has_compact_support (order_dual α) _ _ _ _ _ _ _ _ hf h

lemma continuous.bdd_below_range_of_has_compact_support [nonempty β] [has_zero α]
  {f : β → α} (hf : continuous f) (h : has_compact_support f) :
  bdd_below (range f) :=
begin
  obtain ⟨x, hx⟩ := hf.exists_forall_le_of_has_compact_support h,
  refine ⟨f x, _⟩, rintro _ ⟨x', rfl⟩, exact hx x'
end

lemma continuous.bdd_above_range_of_has_compact_support [nonempty β] [has_zero α]
  {f : β → α} (hf : continuous f) (h : has_compact_support f) :
  bdd_above (range f) :=
@continuous.bdd_below_range_of_has_compact_support (order_dual α) _ _ _ _ _ _ _ _ hf h

end

section

-- lemma times_cont_diff_primitive_of_times_cont_diff
--   {F : H → ℝ → E} {n : with_top ℕ} (hF : times_cont_diff ℝ n ↿F) (h2F : ∀ x, integrable (F x)) :
--   times_cont_diff ℝ n (λ x : H, ∫ t, F x t) :=
-- sorry

-- lemma fderiv_parametric_integral
--   {F : H → ℝ → E} {n : with_top ℕ} (hF : times_cont_diff ℝ n ↿F) (h2F : ∀ x, integrable (F x)) :
--   times_cont_diff ℝ n (λ x : H, ∫ t, F x t) :=
-- sorry
end

section
variables {𝕜 E F : Type*} [nondiscrete_normed_field 𝕜] [normed_group E]
  [normed_space 𝕜 E] [normed_group F] [normed_space 𝕜 F] {f : E → F} {x : E}

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



lemma times_cont_diff_at.continuous_at_fderiv {n : with_top ℕ}
  (h : times_cont_diff_at 𝕜 n f x) (hn : 1 ≤ n) :
  continuous_at (fderiv 𝕜 f) x :=
sorry

lemma support_fderiv_subset : support (fderiv 𝕜 f) ⊆ closure (support f) :=
begin
  intros x,
  rw [← not_imp_not],
  intro h2x,
  rw [not_mem_closure_support_iff_eventually_eq] at h2x,
  exact nmem_support.mpr (h2x.fderiv_eq.trans $ fderiv_const_apply 0),
end

lemma has_compact_support.fderiv (h : has_compact_support f) : has_compact_support (fderiv 𝕜 f) :=
h.mono' support_fderiv_subset


end

section

variables {α : Type*} [measurable_space α]
variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
variables {E : Type*} [normed_group E] [normed_space 𝕜 E] [measurable_space E] [borel_space E]
variables {F : Type*} [normed_group F] [normed_space 𝕜 F]
variables {G : Type*} [normed_group G] [measurable_space G] [opens_measurable_space G]
variables {μ : measure α}

@[simp] lemma map_id' : map (λ x, x) μ = μ :=
map_id

lemma integral_norm_eq_lintegral_nnnorm {f : α → G} (hf : ae_measurable f μ) :
  ∫ x, ∥f x∥ ∂μ = ennreal.to_real ∫⁻ x, ∥f x∥₊ ∂μ :=
begin
  rw integral_eq_lintegral_of_nonneg_ae _ hf.norm,
  { simp_rw [of_real_norm_eq_coe_nnnorm], },
  { refine ae_of_all _ _, simp, },
end


-- lemma measurable_continuous_linear_map  {φ : α → F →L[𝕜] E} :
--   measurable φ ↔ ∀ v : F, measurable (λ a, φ a v) :=
-- begin
--   refine ⟨λ h, h.apply_continuous_linear_map, _⟩,
--   intro h,
--   refine measurable_generate_from _,
--   intros t ht, dsimp at ht,
--   -- have := continuous_linear_map.apply 𝕜 F E,
-- end

end

-- section
-- variables {α γ : Type*} [topological_space α] [measurable_space α] [opens_measurable_space α]
--   [topological_space γ] [measurable_space γ] [borel_space γ] {f : α → γ} {μ : measure α}

-- lemma ae_measurable_of_ae_continuous_at (h : ∀ᵐ x ∂μ, continuous_at f x) :
--   ae_measurable f μ :=
-- begin

-- end
-- end

open metric
section


variables
{𝕂 : Type*} [is_R_or_C 𝕂]
{E' : Type*} [normed_group E'] [normed_space 𝕂 E']
{F' : Type*} [normed_group F'] [normed_space 𝕂 F']

-- todo: reformulate using times_cont_diff_on
lemma times_cont_diff_on.exists_lipschitz_on_with {f : E' → F'}
  {t : set E'} (ht : is_compact t) (hf : ∀ x ∈ t, times_cont_diff_at 𝕂 1 f x) :
  ∃ K, lipschitz_on_with K f t :=
begin
  have hf_cont : continuous_on (λ x, ∥fderiv 𝕂 f x∥₊) t :=
  λ x hx, ((hf x hx).continuous_at_fderiv le_rfl).continuous_within_at.nnnorm,
  rcases t.eq_empty_or_nonempty with rfl|h2t, { simp },
  resetI,
  obtain ⟨x, hxt, hfx⟩ := ht.exists_forall_le h2t hf_cont,
  refine ⟨∥fderiv 𝕂 f x∥₊, _⟩,
  sorry
end

-- lemma times_cont_diff_integral {F : H → α → E} {n : with_top ℕ}
--   (hF_int : ∀ x, integrable (F x) μ)
--   (h_diff : ∀ᵐ a ∂μ, times_cont_diff ℝ n (λ x, F x a)) :
--   times_cont_diff ℝ n (λ x, ∫ a, F x a ∂μ) :=
-- begin
--   sorry
-- end

variables {α : Type*} [measurable_space α]
[topological_space α] [opens_measurable_space α] {μ : measure α}
[is_locally_finite_measure μ]
  {𝕜 : Type*} [is_R_or_C 𝕜]
          {E : Type*} [normed_group E] [normed_space ℝ E]
          [complete_space E] [second_countable_topology E]
          [measurable_space E] [borel_space E]
          {H : Type*} [normed_group H] [normed_space ℝ H] [second_countable_topology $ H →L[ℝ] E]
          [proper_space H]

-- version similar to https://encyclopediaofmath.org/wiki/Parameter-dependent_integral#References
lemma has_fderiv_at_integral' {F : H → α → E} {bound : α → ℝ}
  {x₀ : H}
  -- (hF_int : integrable (F x₀) μ) -- we only need this for one value(!?)
  (hF_int : ∀ᶠ x in 𝓝 x₀, integrable (F x) μ)
  -- (h_diff : ∀ x, ∀ᵐ a ∂μ, times_cont_diff_at ℝ 1 (λ x, F x a) x)
  (hF_bound : ∀ᵐ a ∂μ, ∀ x, ∥partial_fderiv_fst ℝ F x a∥ ≤ bound a)
  (h_bound : integrable bound μ)
  (h_diff : ∀ a, differentiable ℝ (λ x, F x a))
  (h_cont : continuous (partial_fderiv_fst ℝ F x₀)) : -- is this assumption needed?
  has_fderiv_at (λ x, ∫ a, F x a ∂μ) (∫ a, partial_fderiv_fst ℝ F x₀ a ∂μ) x₀ :=
begin
  have h_fderiv : ∀ᵐ a ∂μ, ∀ x ∈ metric.ball x₀ 1,
    has_fderiv_at (λ x, F x a) (partial_fderiv_fst ℝ F x a) x :=
  eventually_of_forall (λ a x hx, (h_diff a).differentiable_at.has_fderiv_at),
  have hf_meas : ∀ᶠ x in 𝓝 x₀, ae_measurable (F x) μ :=
  hF_int.mono (λ x h, h.ae_measurable),
  have h_meas: ae_measurable (λ a, fderiv ℝ (λ (x : H), F x a) x₀) μ :=
  continuous.ae_measurable h_cont μ,
  refine has_fderiv_at_integral_of_dominated_of_fderiv_le zero_lt_one hf_meas hF_int.self_of_nhds
    h_meas (hF_bound.mono $ λ a h x hx, h x) h_bound h_fderiv
end

lemma times_cont_diff_one_integral {F : H → α → E}
  (hF_int : ∀ x, integrable (F x) μ)
  (hF'_int : ∀ x, integrable (λ a, partial_fderiv_fst ℝ F x a) μ)
  (h_diff : ∀ a, differentiable ℝ (λ x, F x a))
  (h_cont : continuous ↿(partial_fderiv_fst ℝ F)) :
  times_cont_diff ℝ 1 (λ x, ∫ a, F x a ∂μ) :=
begin
  simp_rw [times_cont_diff_one_iff_fderiv],
  -- have : ∀ x, has_fderiv_at (λ x, ∫ a, F x a ∂μ) (∫ a, partial_fderiv_fst ℝ F x a ∂μ) x,
  -- { intro x, refine has_fderiv_at_integral' hF_int },
  -- refine ⟨λ x, ∫ a, partial_fderiv_fst ℝ F x a ∂μ, _, _⟩,
  -- have h_fderiv : ∀ᵐ a ∂μ, ∀ x ∈ metric.ball x₀ 1,
  --   has_fderiv_at (λ x, F x a) (partial_fderiv_fst ℝ F x a) x,
  -- { exact eventually_of_forall
  --     (λ a x hx, ((h_diff a).differentiable le_rfl).differentiable_at.has_fderiv_at) },
  -- have hf_cont : ∀ a, continuous_on (λ x, ∥partial_fderiv_fst ℝ F x a∥) (closed_ball x₀ 1) :=
  -- λ a x hx, ((h_diff a).continuous_fderiv le_rfl).continuous_within_at.norm,
  -- -- probably need sigma-finiteness for this
  -- obtain ⟨f, h1f, h2f⟩ : ∃ f : α → ℝ, integrable f μ ∧ ∀ a, 0 < f a := sorry,
  -- have hf_meas : ∀ᶠ x in 𝓝 x₀, ae_measurable (F x) μ :=
  -- eventually_of_forall (λ x, (hF_int x).ae_measurable),
  -- have :=
  -- λ a, (is_compact_closed_ball x₀ 1).exists_forall_ge (nonempty_closed_ball.mpr zero_le_one)
  --   (hf_cont a),
  -- choose y hy h2y using this,
  -- have := has_fderiv_at_integral_of_dominated_of_fderiv_le zero_lt_one hf_meas (hF_int x₀)
  --   (hF'_int x₀).ae_measurable
  --   (eventually_of_forall $ λ a x hx, h2y a x $ ball_subset_closed_ball hx) _ h_fderiv,

  -- obtain ⟨h1, h2⟩ :=
  --   has_fderiv_at_integral_of_dominated_loc_of_lip zero_lt_one hf_meas (hF_int x₀)
  --     (hF'_int x₀).ae_measurable _ ((hF'_int x₀).norm.add h1f) h_fderiv,
  -- { sorry },
  -- { refine eventually_of_forall (λ a, _),
  --   -- have := (h_diff a).times_cont_diff_at,
  --   have := (h_diff a).times_cont_diff_at.exists_lipschitz_on_with_of_nnnorm_lt (_ + ⟨f a, (h2f a).le⟩)
  --     (lt_add_of_pos_right _ _), sorry }
  all_goals { sorry },
end
-- #print is_compact.exists_forall_ge
-- version similar to https://encyclopediaofmath.org/wiki/Parameter-dependent_integral#References
lemma times_cont_diff_one_integral_compact
 [topological_space α] [t2_space α] [opens_measurable_space α] [is_locally_finite_measure μ]
  {F : H → α → E} {x₀ : H}
  (h_diff : ∀ᵐ a ∂μ, times_cont_diff ℝ 1 (λ x, F x a))
  (h_supp : ∀ a, has_compact_support (λ x, F x a))
  (h2_supp : ∀ x, has_compact_support (F x)) :
  has_fderiv_at (λ x, ∫ a, F x a ∂μ) (∫ a, partial_fderiv_fst ℝ F x₀ a ∂μ) x₀ :=
begin
  have hF'_supp : ∀ a, has_compact_support (λ x, partial_fderiv_fst ℝ F x a) :=
  λ a, (h_supp a).fderiv,
  have hnF'_supp : ∀ a, has_compact_support (λ x, ∥ partial_fderiv_fst ℝ F x a ∥) :=
  λ a, (hF'_supp a).norm,
  have hF_cont : ∀ᶠ x in 𝓝 x₀, continuous (F x),
  { sorry, },
  have hF_int : ∀ᶠ x in 𝓝 x₀, integrable (F x) μ,
  { exact hF_cont.mono (λ x h, h.integrable_of_compact_closure_support (h2_supp x)) },
  let bound : α → ℝ := λ a, ⨆ x, ∥ partial_fderiv_fst ℝ F x a ∥,
  have h_int : integrable bound μ,
  { sorry },
  sorry,
  -- refine has_fderiv_at_integral' hF_int _ h_int h_diff,
  -- refine h_diff.mono (λ a h x, _),
  -- exact le_csupr (((h.continuous_fderiv le_rfl).norm).bdd_above_range_of_has_compact_support $ hnF'_supp a) x,
end

end
variables {𝕜 G G₀ X M R E F : Type*}
  [measurable_space G] [measurable_space G] [measurable_space G₀] [measurable_space X]
  [normed_group E] [second_countable_topology E] [normed_space ℝ E]
  [complete_space E] [measurable_space E] [borel_space E]
  {μ : measure G}

namespace measure_theory

section smul
variables [group G] [mul_action G X] [has_measurable_smul G X]

@[to_additive]
def integral_smul_eq_self {μ : measure X} [smul_invariant_measure G X μ] (f : X → E) {m : G} :
  ∫ x, f (m • x) ∂μ = ∫ x, f x ∂μ :=
begin
  have h : measurable_embedding (λ x : X, m • x) :=
  (measurable_equiv.smul m).measurable_embedding,
  rw [← h.integral_map, map_smul]
end

end smul


section mul

variables [group G] [topological_space G] [topological_group G] [borel_space G] {A : set G}
variables {f : G → E}

@[to_additive]
lemma integral_div_right_eq_self (f : G → E) (μ : measure G) [is_mul_right_invariant μ] (x' : G) :
  ∫ x, f (x / x') ∂μ = ∫ x, f x ∂μ :=
by simp_rw [div_eq_mul_inv, integral_mul_right_eq_self f x'⁻¹]

@[to_additive]
lemma map_inv_absolutely_continuous [second_countable_topology G]
  (μ : measure G) [is_mul_left_invariant μ] [sigma_finite μ] :
  map has_inv.inv μ ≪ μ :=
begin
  refine absolutely_continuous.mk (λ s hs, _),
  rw [map_apply measurable_inv hs, measure_inv_null], exact id,
end

@[to_additive]
lemma absolutely_continuous_map_inv [second_countable_topology G]
  (μ : measure G) [is_mul_left_invariant μ] [sigma_finite μ] :
  μ ≪ map has_inv.inv μ :=
begin
  refine absolutely_continuous.mk (λ s hs, _),
  rw [map_apply measurable_inv hs, measure_inv_null], exact id
end

@[to_additive]
lemma map_mul_right_absolutely_continuous [second_countable_topology G]
  (μ : measure G) [is_mul_left_invariant μ] [sigma_finite μ] (g : G) :
  map (* g) μ ≪ μ :=
begin
  refine absolutely_continuous.mk (λ s hs, _),
  rw [map_apply (measurable_mul_const g) hs, measure_mul_right_null], exact id,
end

@[to_additive]
lemma absolutely_continuous_map_mul_right [second_countable_topology G]
  (μ : measure G) [is_mul_left_invariant μ] [sigma_finite μ] (g : G) :
  μ ≪ map (* g) μ :=
begin
  refine absolutely_continuous.mk (λ s hs, _),
  rw [map_apply (measurable_mul_const g) hs, measure_mul_right_null], exact id
end

@[to_additive]
lemma map_div_left_absolutely_continuous [second_countable_topology G]
  (μ : measure G) [is_mul_left_invariant μ] [sigma_finite μ] (g : G) :
  map (λ h, g / h) μ ≪ μ :=
begin
  simp_rw [div_eq_mul_inv],
  rw [← map_map (measurable_const_mul g) measurable_inv],
  refine ((map_inv_absolutely_continuous μ).map _).trans _,
  rw [map_mul_left_eq_self]
end

@[to_additive]
lemma absolutely_continuous_map_div_left [second_countable_topology G]
  (μ : measure G) [is_mul_left_invariant μ] [sigma_finite μ] (g : G) :
  μ ≪ map (λ h, g / h) μ :=
begin
  simp_rw [div_eq_mul_inv],
  rw [← map_map (measurable_const_mul g) measurable_inv],
  conv_lhs { rw [← map_mul_left_eq_self μ g] },
  apply (absolutely_continuous_map_inv μ).map
end

end mul

namespace measure

/-- A measure is invariant under negation if `- μ = μ`. Equivalently, this means that for all
measurable `A` we have `μ (- A) = μ A`, where `- A` is the pointwise negation of `A`. -/
class is_neg_invariant [has_neg G] (μ : measure G) : Prop :=
(neg_eq_self : μ.neg = μ)

/-- A measure is invariant under inversion if `μ⁻¹ = μ`. Equivalently, this means that for all
measurable `A` we have `μ (A⁻¹) = μ A`, where `A⁻¹` is the pointwise inverse of `A`. -/
@[to_additive] class is_inv_invariant [has_inv G] (μ : measure G) : Prop :=
(inv_eq_self : μ.inv = μ)

@[simp, to_additive]
lemma inv_eq_self [has_inv G] (μ : measure G) [is_inv_invariant μ] : μ.inv = μ :=
is_inv_invariant.inv_eq_self

@[simp, to_additive]
lemma map_inv_eq_self [has_inv G] (μ : measure G) [is_inv_invariant μ] :
  map has_inv.inv μ = μ :=
is_inv_invariant.inv_eq_self

/-
@[to_additive]
lemma measure_preimage_inv' [has_inv G] [has_measurable_inv G] (μ : measure G)
  [is_inv_invariant μ] (hA : measurable_set A) : μ (has_inv.inv ⁻¹' A) = μ A :=
by rw [← map_apply measurable_inv hA, map_inv_eq_self μ]

@[to_additive]
lemma measure_inv' [has_inv G] [has_measurable_inv G] (μ : measure G) [is_inv_invariant μ]
  (hA : measurable_set A) : μ A⁻¹ = μ A :=
measure_preimage_inv' μ hA
-/

-- todo: simplify these classes after bump
variables [group G] [has_measurable_mul G] [has_measurable_inv G] {A : set G} [is_inv_invariant μ]

@[to_additive]
lemma measure_preimage_inv (μ : measure G) [is_inv_invariant μ] (A : set G) :
  μ (has_inv.inv ⁻¹' A) = μ A :=
by { conv_rhs { rw [← map_inv_eq_self μ] }, exact ((measurable_equiv.inv G).map_apply A).symm }

@[to_additive]
lemma measure_inv (μ : measure G) [is_inv_invariant μ]
  (A : set G) : μ A⁻¹ = μ A :=
measure_preimage_inv μ A

lemma measure_preimage_inv₀ [group_with_zero G₀] [has_measurable_inv G₀] (μ : measure G₀)
  [is_inv_invariant μ] (A : set G₀) : μ (has_inv.inv ⁻¹' A) = μ A :=
by { conv_rhs { rw [← map_inv_eq_self μ] }, exact ((measurable_equiv.inv₀ G₀).map_apply A).symm }

lemma measure_inv₀ [group_with_zero G₀] [has_measurable_inv G₀] (μ : measure G₀)
  [is_inv_invariant μ] (A : set G₀) : μ A⁻¹ = μ A :=
by { conv_rhs { rw [← map_inv_eq_self μ] }, exact ((measurable_equiv.inv₀ G₀).map_apply A).symm }



-- @[to_additive]
-- lemma integral_inv_eq_self [smul_invariant_measure _ _ μ] (f : G → E) : ∫ x, f (x⁻¹) ∂μ = ∫ x, f x ∂μ :=
-- begin
--   have h : measurable_embedding (λ x : G, x⁻¹) :=
--   (measurable_equiv.inv G).measurable_embedding,
--   rw [← h.integral_map, map_inv_eq_self]
-- end

end measure
open measure
variables [group G] [has_measurable_mul G] [has_measurable_inv G]

@[to_additive]
lemma integral_inv_eq_self (f : G → E) (μ : measure G) [is_inv_invariant μ] :
  ∫ x, f (x⁻¹) ∂μ = ∫ x, f x ∂μ :=
begin
  have h : measurable_embedding (λ x : G, x⁻¹) :=
  (measurable_equiv.inv G).measurable_embedding,
  rw [← h.integral_map, map_inv_eq_self]
end

@[to_additive]
lemma integral_div_left_eq_self (f : G → E) (μ : measure G) [is_inv_invariant μ]
  [is_mul_left_invariant μ] (x' : G) : ∫ x, f (x' / x) ∂μ = ∫ x, f x ∂μ :=
by simp_rw [div_eq_mul_inv, integral_inv_eq_self (λ x, f (x' * x)) μ,
  integral_mul_left_eq_self f x']


end measure_theory
open measure_theory measure_theory.measure

section noncomm

variables {f f' : G → 𝕜} {g g' : G → E}
    {x x' : G} {y y' : 𝕜}
variables [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [smul_comm_class ℝ 𝕜 E]

/-- The convolution of `f` and `g` exists when the function `t ↦ f t * g (x - t)` is integrable
  for all `x : G`. There are various conditions on `f` and `g` to prove this. -/
def convolution_exists [has_sub G] (f : G → 𝕜) (g : G → E) (μ : measure G . volume_tac) : Prop :=
∀ x : G, integrable (λ t, f t • g (x - t)) μ

def convolution [has_sub G] (f : G → 𝕜) (g : G → E) (μ : measure G . volume_tac) (x : G) : E :=
∫ t, f t • g (x - t) ∂μ

notation f ` ⋆[`:67 μ:67 `] `:0 g:66 := convolution f g μ
notation f ` ⋆ `:67 g:11 := f ⋆[volume] g
-- localized "notation f ` ⋆[`:67 μ `] `:67 g := convolution f g μ" in convolution
-- localized "notation f ` ⋆ `:67 g := convolution f g (volume _)" in convolution

lemma convolution_exists.integrable [has_sub G] (h : convolution_exists f g μ) (x : G) :
  integrable (λ t, f t • g (x - t)) μ :=
h x

lemma convolution_def [has_sub G] : (f ⋆[μ] g) x = ∫ t, f t • g (x - t) ∂μ := rfl

-- todo: reduce type-class constraints
variables [add_comm_group G] [topological_space G] [topological_add_group G] [borel_space G]
  [second_countable_topology G]
  [is_add_left_invariant μ] [sigma_finite μ]
variables [measurable_space 𝕜] [borel_space 𝕜] [has_measurable_smul₂ 𝕜 E]

lemma continuous.convolution_integrand_snd (hf : continuous f) (hg : continuous g) (x : G) :
  continuous (λ t, f t • g (x - t)) :=
hf.smul (hg.comp $ continuous_const.sub continuous_id)

lemma ae_measurable.convolution_integrand_snd
  (hf : ae_measurable f μ) (hg : ae_measurable g μ)
  (x : G) : ae_measurable (λ t, f t • g (x - t)) μ :=
begin
  refine hf.smul (ae_measurable.comp_measurable _ $ measurable_id.const_sub x),
  exact hg.mono' (map_sub_left_absolutely_continuous μ x)
end

lemma ae_measurable.convolution_integrand (hf : ae_measurable f μ) (hg : ae_measurable g μ) :
  ae_measurable (λ p : G × G, f p.2 • g (p.1 - p.2)) (μ.prod μ) :=
begin
  refine hf.snd.smul (ae_measurable.comp_measurable _ $ measurable_fst.sub measurable_snd),
  refine hg.mono' _,
  refine absolutely_continuous.mk (λ s hs h2s, _),
  rw [map_apply measurable_sub hs],
  sorry,
end

lemma continuous.convolution_integrand_fst (hg : continuous g) (t : G) :
  continuous (λ x, f t • g (x - t)) :=
continuous_const.smul (hg.comp $ continuous_id.sub continuous_const)

lemma convolution_add_distrib (hfg : convolution_exists f g μ)
  (hfg' : convolution_exists f g' μ) : f ⋆[μ] (g + g') = f ⋆[μ] g + f ⋆[μ] g' :=
by { ext, simp only [convolution_def, smul_add, pi.add_apply, integral_add (hfg x) (hfg' x)] }

lemma add_convolution_distrib (hfg : convolution_exists f g μ)
  (hfg' : convolution_exists f' g μ) : (f + f') ⋆[μ] g = f ⋆[μ] g + f' ⋆[μ] g :=
by { ext, simp only [convolution_def, add_smul, pi.add_apply, integral_add (hfg x) (hfg' x)] }

lemma smul_convolution : (y • f) ⋆[μ] g = y • (f ⋆[μ] g) :=
by { ext, simp only [pi.smul_apply, convolution_def, ← integral_smul, smul_assoc] }

lemma convolution_smul : f ⋆[μ] (y • g) = y • (f ⋆[μ] g) :=
by { ext, simp only [pi.smul_apply, convolution_def, ← integral_smul, smul_comm y] }

lemma integrable.convolution_exists [sigma_finite μ] [second_countable_topology G]
  (hf : integrable f μ) (hg : integrable g μ) : convolution_exists f g μ :=
begin
  have : ae_measurable (λ p : G × G, f p.2 • g (p.1 - p.2)) (μ.prod μ) :=
    hf.ae_measurable.convolution_integrand hg.ae_measurable,
  have h : integrable (λ p : G × G, f p.2 • g (p.1 - p.2)) (μ.prod μ),
  { -- We can probably also do this for nonabelian groups, but this exact proof doesn't work
    -- for that case
    simp_rw [integrable_prod_iff' this],
    refine ⟨eventually_of_forall (λ t, _), _⟩,
    { refine integrable.smul _ _,
      rw [← map_add_right_eq_self μ t, integrable_map_measure, function.comp],
      { simp_rw [add_sub_cancel], exact hg },
      { refine ae_measurable.comp_measurable _ (measurable_id.sub_const t),
        simp_rw [map_map (measurable_id'.sub_const t) (measurable_id'.add_const t),
          function.comp, add_sub_cancel, map_id'],
        exact hg.ae_measurable },
      exact measurable_add_const t },
    simp_rw [norm_smul, integral_mul_left, integral_sub_right_eq_self (λ t, ∥ g t ∥) μ],
    exact hf.norm.mul_const _, },
  simp_rw [integrable_prod_iff this] at h,
  -- this only gives existence a.e.
  sorry
end

lemma integrable.integrable_convolution (hf : integrable f μ) (hg : integrable g μ) :
  integrable (f ⋆[μ] g) μ :=
begin
  have : ae_measurable (λ p : G × G, f p.2 • g (p.1 - p.2)) (μ.prod μ) :=
    hf.ae_measurable.convolution_integrand hg.ae_measurable,
  have h : integrable (λ p : G × G, f p.2 • g (p.1 - p.2)) (μ.prod μ),
  { -- We can probably also do this for nonabelian groups, but this exact proof doesn't work
    -- for that case
    simp_rw [integrable_prod_iff' this],
    refine ⟨eventually_of_forall (λ t, _), _⟩,
    { refine integrable.smul _ _,
      rw [← map_add_right_eq_self μ t, integrable_map_measure, function.comp],
      { simp_rw [add_sub_cancel], exact hg },
      { refine ae_measurable.comp_measurable _ (measurable_id.sub_const t),
        simp_rw [map_map (measurable_id'.sub_const t) (measurable_id'.add_const t),
          function.comp, add_sub_cancel, map_id'],
        exact hg.ae_measurable },
      exact measurable_add_const t },
    simp_rw [norm_smul, integral_mul_left, integral_sub_right_eq_self (λ t, ∥ g t ∥) μ],
    exact hf.norm.mul_const _, },
  exact h.integral_prod_left
end

lemma has_compact_support.convolution_exists_left (h1f : has_compact_support f)
  (h2f : integrable f μ) (hg : ∀ K, is_compact K → integrable_on g K μ) :
  convolution_exists f g μ :=
sorry

lemma has_compact_support.convolution_exists_right (hf : ∀ K, is_compact K → integrable_on f K μ)
  (h1g : has_compact_support g) (h2g : integrable g μ) : convolution_exists f g μ :=
sorry

end noncomm

section normed

variables {f f' : ℝ → ℝ} {g g' : ℝ → E} {x x' : ℝ}
variables [normed_space ℝ E]
variables {n : with_top ℕ}


lemma has_compact_support.continuous_convolution_left (h1f : has_compact_support f)
  (h2f : continuous f) (hg : continuous g) : continuous (f ⋆ g) :=
begin
  sorry
end

lemma has_compact_support.continuous_convolution_right (hf : continuous f)
  (h1g : has_compact_support g) (h2g : continuous g) : continuous (f ⋆ g) :=
sorry

lemma continuous_supr {α β} [topological_space α] [compact_space α] [topological_space β]
  {f : α → β → ℝ} (hf : continuous (uncurry f)) : continuous (⨆ i, f i) :=
begin
  sorry
end

-- lemma continuous_supr {α β γ} [topological_space α] [topological_space β] [topological_space γ]
--   (f : α → β → γ)

lemma has_fderiv_at_left (hfg : convolution_exists f g) (hf : times_cont_diff ℝ 1 f)
  (hg : continuous g) (x₀ : ℝ) : has_deriv_at (f ⋆ g) ((deriv f ⋆ g) x₀) x₀ :=
begin
  have h_cont : ∀ x, continuous (λ t, f t • g (x - t)) :=
  hf.continuous.convolution_integrand_snd hg,
  have h2_cont : ∀ x, continuous (λ t, deriv f t • g (x - t)) :=
  sorry, --λ x, (hf.continuous_deriv le_rfl).smul (hg.comp $ continuous_const.sub continuous_id),
  -- refine has_deriv_at_integral_of_dominated_of_fderiv_le zero_lt_one _ _ _ _ _ _,
  -- sorry,
  -- exact eventually_of_forall (λ x, (h_cont x).ae_measurable _),
  -- exact hfg x₀,
  -- exact (h2_cont x₀).ae_measurable _,
  -- exact (hf.smul $ (hg.continuous_fderiv le_rfl).comp $ continuous_const.sub continuous_id).ae_measurable _,
  sorry
end

lemma has_fderiv_at_right (hfg : convolution_exists f g) (hf : continuous f)
  (hg : times_cont_diff ℝ 1 g) (x₀ : ℝ) : has_fderiv_at (f ⋆ g) ((f ⋆ fderiv ℝ g) x₀) x₀ :=
begin
  have h_cont : ∀ x, continuous (λ t, f t • g (x - t)) :=
  hf.convolution_integrand_snd hg.continuous,
  have h2_cont : ∀ x, continuous (λ t, f t • fderiv ℝ g (x - t)) :=
  λ x, hf.smul ((hg.continuous_fderiv le_rfl).comp $ continuous_const.sub continuous_id),
  refine has_fderiv_at_integral_of_dominated_of_fderiv_le zero_lt_one _ (hfg x₀) _ _ _ _,
  refine λ t, |f t| * ⨆ x ∈ closed_ball x₀ 1, ∥ g (x - t) ∥,
  exact eventually_of_forall (λ x, (h_cont x).ae_measurable _),
  exact (h2_cont x₀).ae_measurable _,
  refine eventually_of_forall (λ t x hx, _),
  sorry,
  -- exact (hf.smul $ (hg.continuous_fderiv le_rfl).comp $ continuous_const.sub continuous_id).ae_measurable _,
end
-- continuous.integrable_on_compact

lemma times_cont_diff_convolution_right (hf : continuous f) (hg : times_cont_diff ℝ n g) :
  times_cont_diff ℝ n (f ⋆ g) :=
-- have : times_cont_diff ℝ n ↿(λ x t, _)
sorry

lemma times_cont_diff_convolution_left (hf : times_cont_diff ℝ n f) (hg : continuous g) :
  times_cont_diff ℝ n (f ⋆ g) :=
sorry

-- lemma times_cont_diff_convolution_right (hf : continuous f) (hg : times_cont_diff 𝕜 n g) :
--   times_cont_diff 𝕜 n (f ⋆[μ] g) :=
-- times_cont_diff_parametric_primitive_of_times_cont_diff _ _ _

-- lemma times_cont_diff_convolution_left (hf : times_cont_diff 𝕜 n f) (hg : continuous g) :
--   times_cont_diff 𝕜 n (f ⋆[μ] g) :=
-- sorry

end normed

section comm_group

variables  [nondiscrete_normed_field 𝕜] [measurable_space 𝕜] [borel_space 𝕜] [complete_space 𝕜]
  [normed_space ℝ 𝕜] [second_countable_topology 𝕜] [smul_comm_class ℝ 𝕜 𝕜]
--[normed_space 𝕜 E]
-- [normed_comm_ring R] [second_countable_topology R] [normed_space ℝ R]
--   [complete_space R] [measurable_space R] [borel_space R]
  [add_comm_group G] [topological_space G] [topological_add_group G] [borel_space G]
  [is_neg_invariant μ] [is_add_left_invariant μ]
  {f g h : G → 𝕜} {x x' : G} {y y' : R}

lemma convolution_comm : f ⋆[μ] g = g ⋆[μ] f :=
by { ext, simp_rw [convolution_def], rw [← integral_sub_left_eq_self _ μ x],
  simp_rw [sub_sub_self, smul_eq_mul, mul_comm] }

lemma convolution_assoc : (f ⋆[μ] g) ⋆[μ] h = f ⋆[μ] (g ⋆[μ] h) :=
by { ext, simp [convolution_def], sorry }

end comm_group

end measure_theory
