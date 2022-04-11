import measure_theory.integral.interval_integral
import measure_theory.group.integration
import analysis.calculus.specific_functions
import to_mathlib.analysis.cont_diff_bump


import notations
import loops.basic

import to_mathlib.partition -- get our finsum stuff

noncomputable theory
open set function measure_theory.measure_space
open_locale topological_space big_operators filter

section
/-! ## Bump family

In this section we construct `bump (n : ℕ)`, a bump function with support in
`Ioo (-1/(n+2)) (1/(n+2))`.
-/

lemma aux (n : ℕ) : Ioo (-(1/(n+2 : ℝ))) (1/(n+2)) ∈ 𝓝 (0 : ℝ) :=
begin
  have key : (0 : ℝ) < 1/(n+2),
  { rw show (n : ℝ) + 2 = ((n+1 :ℕ) : ℝ) + 1, from by norm_cast,
    apply nat.one_div_pos_of_nat },
  apply Ioo_mem_nhds _ key,
  rwa neg_lt_zero
end

lemma neg_one_div_succ_lt (n : ℕ) : -(1/(n+2 : ℝ)) < 1/(n+2) :=
begin
  rw neg_lt_iff_pos_add,
  field_simp,
  apply div_pos (zero_lt_two : (0 : ℝ) < 2),
  exact_mod_cast (n + 1).succ_pos
end

/-- `bump n` is a bump function on `ℝ` which has support `Ioo (-(1/(n+2))) (1/(n+2))`
and equals one on `Icc (-(1/(n+3))) (1/(n+3))`.
-/
def bump (n : ℕ) : cont_diff_bump_of_inner (0 : ℝ) :=
{ r := 1/(n+3),
  R := 1/(n+2),
  r_pos := begin
    apply one_div_pos.mpr,
    exact_mod_cast (nat.succ_pos _)
  end,
  r_lt_R := begin
    apply one_div_lt_one_div_of_lt,
    exact_mod_cast (nat.succ_pos _),
    exact_mod_cast lt_add_one (n + 2)
  end }

lemma support_bump (n : ℕ) : support (bump n) = Ioo (-(1/(n+2))) (1/(n+2)) :=
by rw [(bump n).support_eq, real.ball_eq_Ioo, zero_sub, zero_add, bump]

lemma tsupport_bump (n : ℕ) : tsupport (bump n) = Icc (-(1/(n+2))) (1/(n+2)) :=
by rw [(bump n).tsupport_eq, real.closed_ball_eq_Icc, zero_sub, zero_add, bump]

lemma support_bump_subset (n : ℕ) : support (bump n) ⊆ Ioc (-(1/2)) (1/2) :=
begin
  have ineg : 1 / (n + 2 : ℝ) ≤ 1 / 2,
  { apply one_div_le_one_div_of_le ; norm_num },
  rw support_bump n,
  exact Ioo_subset_Ioc_self.trans (Ioc_subset_Ioc (neg_le_neg ineg) ineg)
end

lemma tsupport_bump_subset (n : ℕ) : tsupport (bump n) ⊆ Icc (-(1/2)) (1/2) :=
by { rw [tsupport, ← closure_Ioc], exact closure_mono (support_bump_subset n), norm_num }

lemma bump_nonneg (n : ℕ) (x : ℝ) : 0 ≤ bump n x :=
(bump n).nonneg

lemma continuous_bump (n : ℕ) : continuous (bump n) :=
(bump n).continuous

-- def integral_bump (n : ℕ) : ℝ := ∫ t in -(1/2)..1/2, bump n t

-- lemma integral_bump_pos (n : ℕ) : 0 < integral_bump n :=
-- begin
--   have ineq : -(1/2 : ℝ) < 1/2, by norm_num,
--   dsimp [integral_bump],
--   rw [interval_integral.integral_eq_integral_of_support_subset (support_bump_subset n)],
--   exact (bump n).integral_pos
-- end

end

section finprod
/-! ## Missing finprod/finsum lemmas -/

variables {M : Type*} [comm_monoid M] {ι ι' : Type*}

@[to_additive]
lemma finset.prod_equiv [decidable_eq ι] {e : ι ≃ ι'} {f : ι' → M} {s' : finset ι'} {s : finset ι}
  (h : s = finset.image e.symm s') :
  ∏ i' in s', f i' = ∏ i in s, f (e i) :=
begin
  rw [h, finset.prod_bij' (λ i' hi', e.symm i') _ _ (λ i hi, e i)],
  { simp },
  { simp },
  { rintro a ha,
    rcases finset.mem_image.mp ha with ⟨i', hi', rfl⟩,
    simp [hi'] },
  { exact λ i' hi',  finset.mem_image_of_mem _ hi' },
  { simp },
end

lemma equiv.preimage_eq_image {α β : Type*} (e : α ≃ β) (s : set β) : ⇑e ⁻¹' s = e.symm '' s :=
by simp [e.symm.image_eq_preimage]

@[to_additive]
lemma finprod_comp_equiv {e : ι ≃ ι'} {f : ι' → M} : ∏ᶠ i', f i' = ∏ᶠ i, f (e i) :=
begin
  classical,
  have supp : mul_support (λ i, f (e i)) = e ⁻¹' (mul_support f),
  { apply mul_support_comp_eq_preimage },
  cases (finite_or_infinite : (mul_support f).finite ∨ _) with H H,
  { have H' : (mul_support (λ i, f (e i))).finite,
    { rw [supp, e.preimage_eq_image],
      exact H.image (equiv.symm e) },
    rw [finprod_eq_prod f H, finprod_eq_prod _ H', finset.prod_equiv],
    apply finset.coe_injective,
    simp [e.preimage_eq_image, supp] },
  { rw finprod_of_infinite_mul_support H,
    rw [finprod_of_infinite_mul_support],
    rw supp,
    apply infinite_of_infinite_image,
    rwa e.image_preimage }
end

end finprod

section
/-! ## The standard ℤ action on ℝ is properly discontinuous

TODO: use that in to_mathlib.topology.periodic?
-/
instance : has_vadd ℤ ℝ := ⟨λ n x, (n : ℝ) + x⟩

instance : properly_discontinuous_vadd ℤ ℝ := sorry
end

section
/-! # Periodize

In this section we turn any function `f : ℝ → E` into a 1-periodic function
`λ t : ℝ, ∑ᶠ n : ℤ, f (t+n)`.
-/

variables {M : Type*} [add_comm_monoid M]

def periodize (f : ℝ → M) (t : ℝ) : M :=
∑ᶠ n : ℤ, f (t + n)

lemma periodic_periodize (f : ℝ → M) : periodic (periodize f) 1 :=
begin
  intros t,
  unfold periodize,
  have : (λ n : ℤ, f (t + 1 + ↑n)) = λ n, f (t + (n+1 : ℤ)),
  { ext n, simp_rw [int.cast_add, int.cast_one, add_assoc, add_comm] },
  simp_rw this,
  let e := equiv.add_right (1 : ℤ),
  let F : ℤ → M := λ n, f (t + n),
  change ∑ᶠ (n : ℤ), F (e n) = ∑ᶠ (n : ℤ), f (t + ↑n),
  exact finsum_comp_equiv.symm,
end

lemma periodize_nonneg {f : ℝ → ℝ} (h : ∀ t, 0 ≤ f t) (t : ℝ) : 0 ≤ periodize f t :=
begin
  unfold periodize,
  cases (finite_or_infinite : (support (λ i : ℤ, f (t+i))).finite ∨ _) with H H,
  { rw [finsum_eq_sum _ H],
    apply finset.sum_nonneg,
    exact λ i hi, h _ },
  { rwa finsum_of_infinite_support },
end

variables {E : Type*} [normed_group E] [normed_space ℝ E]

lemma cont_diff.periodize {f : ℝ → E} {n : with_top ℕ} (h : cont_diff ℝ n f)
  (h' : has_compact_support f) : cont_diff ℝ n (periodize f) :=
begin
  apply cont_diff_iff_cont_diff_at.mpr (λ x, cont_diff_at_finsum _ _),
  { intros y,
    dsimp,
    set N := Ioo (y - 1) (y + 1),
    refine ⟨N, (nhds_basis_Ioo_pos y).mem_of_mem zero_lt_one, _⟩,
    let e := λ i : ℤ, equiv.add_right (i : ℝ),
    change {i : ℤ | (support (λ (x : ℝ), f (e i x)) ∩ N).nonempty}.finite,
    have hsupp : ∀ i : ℤ, support (λ (x : ℝ), f (e i x)) = (e i)⁻¹' (support f),
    { intro i,
      rw support_comp_eq_preimage },
    have hsupp' : ∀ i, ((e i)⁻¹' (support f) ∩ N).nonempty ↔ (support f ∩ e i '' N).nonempty,
    { intros i,
      conv_lhs { rw [← (e i).preimage_image N, ← preimage_inter] },
      rw (e i).surjective.nonempty_preimage },
    simp_rw [hsupp, hsupp', inter_comm (support f)], clear hsupp hsupp',
    refine (properly_discontinuous_vadd.finite_disjoint_inter_image (is_compact_Icc : is_compact $ Icc (y-1) (y+1)) h').subset _,
    intros i hi,
    rw [mem_set_of_eq, ne_empty_iff_nonempty],
    apply nonempty.mono _ hi,
    mono,
    { rw show (e i : ℝ → ℝ) = (has_vadd.vadd i), by { ext x, exact add_comm x i },
      exact image_subset _ Ioo_subset_Icc_self },
    exact subset_tsupport f },
  { intros i,
    exact (h.cont_diff_at).comp _ (cont_diff_at_id.add cont_diff_at_const) },
end

-- This isn't quite the right statement. We'll need something more general.
lemma integral_periodize (f : ℝ → ℝ) (hf : support f ⊆ Ioo (-(1/2)) (1/2)) :
  ∫ t in (-(1/2))..(1/2), periodize f t = ∫ t in (-(1/2))..(1/2), f t :=
begin

  sorry
end

end

section small_sets
open_locale filter
open filter
variables {α ι : Type*}

def filter.small_sets (f : filter α) : filter (set α) :=
⨅ t ∈ f, 𝓟 {s | s ⊆ t}

lemma filter.has_basis_small_sets (f : filter α) :
  has_basis f.small_sets (λ t : set α, t ∈ f) (λ t, {s | s ⊆ t}) :=
begin
  apply has_basis_binfi_principal _ _,
  { rintros u (u_in : u ∈ f) v (v_in : v ∈ f),
    use [u ∩ v, inter_mem u_in v_in],
    split,
    rintros w (w_sub : w ⊆ u ∩ v),
    exact w_sub.trans (inter_subset_left u v),
    rintros w (w_sub : w ⊆ u ∩ v),
    exact w_sub.trans (inter_subset_right u v) },
  { use univ,
    exact univ_mem },
end

lemma filter.has_basis.small_sets {f : filter α} {p : ι → Prop} {s : ι → set α}
  (h : has_basis f p s) : has_basis f.small_sets p (λ i, {u | u ⊆ s i}) :=
⟨begin
  intros t,
  rw f.has_basis_small_sets.mem_iff,
  split,
  { rintro ⟨u, u_in, hu : {v : set α | v ⊆ u} ⊆ t⟩,
    rcases h.mem_iff.mp u_in with ⟨i, hpi, hiu⟩,
    use [i, hpi],
    apply subset.trans _ hu,
    intros v hv x hx,
    exact hiu (hv hx) },
  { rintro ⟨i, hi, hui⟩,
    exact ⟨s i, h.mem_of_mem hi, hui⟩ }
end⟩

-- sanity check
example {κ : Type*} {a : filter κ} {f : filter α} {g : κ → set α} :
  tendsto g a f.small_sets ↔ ∀ t : set α, t ∈ f → ∀ᶠ k in a, g k ⊆ t :=
f.has_basis_small_sets.tendsto_right_iff

end small_sets


section
open filter
open_locale filter

lemma tendsto_sup_dist {X Y : Type*} [topological_space X] [locally_compact_space X]
  [metric_space Y] {f : X → Y} (h : continuous f)
  {t : X} {s : ℕ → set X} (hs : tendsto s at_top (𝓝 t).small_sets) :
  tendsto (λ (n : ℕ), ⨆ x ∈ s n, dist (f x) (f t)) at_top (𝓝 0) :=
begin
  sorry
end

end

section
variables {α E : Type*} [normed_group E]

lemma support_norm (f : α → E) : support (λ a, ∥f a∥) = support f :=
function.support_comp_eq norm (λ x, norm_eq_zero) f

end

section mollify_on_real

/-! ## Mollifiers on ℝ -/
open_locale filter
open filter measure_theory

variables {δ : ℕ → ℝ → ℝ} (δ_nonneg : ∀ n x, 0 ≤ δ n x) (int_δ : ∀ n, ∫ s, δ n s = 1)
  (supp_δ : tendsto (λ n, support (δ n)) at_top (𝓝 0).small_sets)

variables {E : Type*} [normed_group E] [normed_space ℝ E] [complete_space E]

@[to_additive]
lemma has_compact_mul_support_of_subset {α β : Type*} [topological_space α] [t2_space α]
  [has_one β] {f : α → β} {K : set α} (hK : is_compact K) (hf : mul_support f ⊆ K) :
  has_compact_mul_support f :=
compact_of_is_closed_subset hK (is_closed_mul_tsupport f) (closure_minimal hf hK.is_closed)

lemma tendsto_truc {δ : ℕ → ℝ → ℝ} (δ_nonneg : ∀ n x, 0 ≤ δ n x) (int_δ : ∀ n, ∫ s, δ n s = 1)
  (supp_δ : tendsto (λ n, support (δ n)) at_top (𝓝 0).small_sets) (δ_cont : ∀ n, continuous (δ n))
  (δ_meas_supp : ∀ n, measurable_set $ support (δ n))
  {f : ℝ → E} {t : ℝ} (h : continuous f) :
  tendsto (λ n, ∫ s, δ n (t - s) • f s) at_top (𝓝 $ f t) :=
begin
  have : ∀ n, ∫ s, δ n (t - s) • f s = ∫ s, δ n s  • f (t - s),
  sorry { intros n,
    rw ← measure_theory.integral_sub_left_eq_self _ volume t,
    simp_rw [sub_sub_self] },
  rw funext this,
  have : tendsto (λ n, ⨆ x ∈ support (δ n), ∥f (t - x) - f t∥) at_top (𝓝 0),
  sorry { set F := λ x, f (t - x),
    suffices : tendsto (λ n, ⨆ x ∈ support (δ n), ∥F x - F 0∥) at_top (𝓝 0),
    { simp_rw [F, sub_zero t] at this, exact this },
    simp_rw ← dist_eq_norm,
    exact tendsto_sup_dist (h.comp $ continuous_sub_left t) supp_δ },
  rw tendsto_iff_norm_tendsto_zero,
  apply squeeze_zero_norm' _ this,
  have : ∀ᶠ n in at_top, support (δ n) ⊆ Icc (-1) 1,
  sorry { have : Icc (-(1 : ℝ)) 1 ∈ 𝓝 (0 : ℝ),
    apply Icc_mem_nhds ; norm_num,
    exact (𝓝 (0 : ℝ)).has_basis_small_sets.tendsto_right_iff.mp supp_δ _ this },
  apply this.mono,
  intros n hn,
  have cpct₁ : has_compact_support (δ n),
  sorry { apply has_compact_support_of_subset is_compact_Icc hn },
  rw norm_norm,
  have : (∫ (s : ℝ), δ n s • f (t - s)) - f t = ∫ (s : ℝ), δ n s • (f (t - s) - f t),
  sorry { conv_lhs { rw [show f t = (1 : ℝ) • f t, by simp only [one_smul], ← int_δ n] },
    have δ_integrable : integrable (δ n),
    { exact (δ_cont n).integrable_of_has_compact_support cpct₁, },
    rw [← integral_smul_const, ← measure_theory.integral_sub],
    simp [smul_sub],
    { apply continuous.integrable_of_has_compact_support,
      exact (δ_cont n).smul (h.comp (continuous_const.sub continuous_id')),
      exact has_compact_support.smul_right cpct₁, },
    { apply continuous.integrable_of_has_compact_support,
      exact (δ_cont n).smul continuous_const,
      exact has_compact_support.smul_right cpct₁ } },
  rw this,
  calc ∥∫ (s : ℝ), δ n s • (f (t - s) - f t)∥ ≤ ∫ s, ∥δ n s • (f (t - s) - f t)∥ : _
  ... = ∫ s, ∥δ n s∥ * ∥(f (t - s) - f t)∥ : by simp_rw norm_smul
  ... = ∫ s in support (δ n), ∥δ n s∥ * ∥(f (t - s) - f t)∥ : _
  ... ≤ ∫ s in support (δ n), ∥δ n s∥ * ⨆ s ∈ support (δ n), ∥(f (t - s) - f t)∥ : _
  ... = (∫ s in support (δ n), ∥δ n s∥) * ⨆ s ∈ support (δ n), ∥(f (t - s) - f t)∥ : _
  ... = ⨆ (x : ℝ) (H : x ∈ support (δ n)), ∥f (t - x) - f t∥ : _,
  exact norm_integral_le_integral_norm _,
  { have : support (λ s, ∥δ n s∥ * ∥f (t - s) - f t∥) ⊆ support (δ n),
    { rw ← support_norm (δ n),
      apply support_mul_subset_left },
    conv_lhs { rw ← indicator_eq_self.mpr this },
    rw integral_indicator (δ_meas_supp n) },
  all_goals { sorry }
end

end mollify_on_real

section delta_approx

/-- ## An approximate Dirac "on the circle". -/

def approx_dirac (n : ℕ) : ℝ → ℝ :=
periodize $ (bump n).normed volume

lemma periodic_const {α β : Type*} [has_add α] {a : α} {b : β} : periodic (λ x, b) a :=
λ x, rfl

lemma periodic_approx_dirac (n : ℕ) : periodic (approx_dirac n) 1 :=
begin
  intros t,
  unfold approx_dirac,
  rw periodic_periodize
end

lemma approx_dirac_nonneg (n : ℕ) (t : ℝ): 0 ≤ approx_dirac n t :=
periodize_nonneg (bump n).nonneg_normed t

lemma approx_dirac_smooth (n : ℕ) : 𝒞 ∞ (approx_dirac n) :=
(bump n).cont_diff_normed.periodize (bump n).has_compact_support_normed

end delta_approx

/-- A stictly positive, smooth approximation to the Dirac delta function on the circle, centered at
`t` (regarded as a point of the circle) and converging to the Dirac delta function as `η → 0`.

TODO: When constructing these, we can just do `t = 0` case and then translate. -/
def delta_mollifier (η t : ℝ) : ℝ → ℝ := sorry

variables {η : ℝ} (hη : η ≠ 0) (t : ℝ)
include hη

lemma delta_mollifier_periodic : periodic (delta_mollifier η t) 1 := sorry

lemma delta_mollifier_pos (s : ℝ) : 0 < delta_mollifier η t s := sorry

-- TODO Maybe just drop this, we'll probably only ever need `delta_mollifier_smooth'`.
lemma delta_mollifier_smooth : 𝒞 ∞ ↿(delta_mollifier η) := sorry

lemma delta_mollifier_smooth' : 𝒞 ∞ (delta_mollifier η t) :=
(delta_mollifier_smooth hη).comp (cont_diff_prod_mk t)

@[simp] lemma delta_mollifier_integral_eq_one : ∫ s in 0..1, delta_mollifier η t s = 1 := sorry

omit hη

variables {F : Type*} [normed_group F] [normed_space ℝ F] [finite_dimensional ℝ F]
variables [measurable_space F] [borel_space F]

-- TODO Relocate to `src/loops/basic.lean` if this turns out to be useful.
instance loop.has_norm : has_norm (loop F) := ⟨λ γ, ⨆ t, ∥γ t∥⟩

-- TODO Come up with a better name for this.
def loop.mollify (γ : loop F) (η t : ℝ) : F :=
if η = 0 then γ t else ∫ s in 0..1, delta_mollifier η t s • γ s

lemma loop.mollify_eq_of_ne_zero (γ : loop F) (η t : ℝ) (hη : η ≠ 0) :
  γ.mollify η t = ∫ s in 0..1, delta_mollifier η t s • γ s :=
if_neg hη

/-- I doubt this is exactly the right property and I think we may be able to get away with something
a good deal weaker. The plan is to try finishing the reparametrization lemma and see what
convergence property it requires. -/
lemma loop.eval_at_sub_mollify_lt {ε : ℝ} (hε : 0 < ε) :
  ∀ᶠ η in 𝓝 0, ∀ (γ : loop F) (hf : continuous γ), ∥γ t - γ.mollify η t∥ < ε * ∥γ∥ :=
sorry
