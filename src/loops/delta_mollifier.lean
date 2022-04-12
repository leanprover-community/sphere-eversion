import measure_theory.integral.interval_integral
import measure_theory.group.integration
import analysis.calculus.specific_functions

import to_mathlib.convolution
import to_mathlib.analysis.cont_diff_bump
import to_mathlib.data.real_basic
import to_mathlib.topology.periodic

import notations
import loops.basic

import to_mathlib.partition -- get our finsum stuff

noncomputable theory
open set function measure_theory.measure_space continuous_linear_map filter
open_locale topological_space big_operators filter convolution



variables {F : Type*} [normed_group F] [normed_space ℝ F] [finite_dimensional ℝ F]
variables [measurable_space F] [borel_space F]

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

lemma support_shifted_normed_bump_subset (n : ℕ) (t : ℝ) :
  support (λ x, (bump n).normed volume (x - t)) ⊆ Ioc (t - 1/2) (t + 1/2) :=
begin
  rw [function.support_comp_eq_preimage],
  simp_rw [(bump n).support_normed_eq, ← (bump n).support_eq],
  refine (preimage_mono (support_bump_subset n)).trans _,
  simp_rw [preimage_sub_const_Ioc, sub_eq_add_neg, add_comm]
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

instance : properly_discontinuous_vadd ℤ ℝ :=
⟨begin
  intros K L hK hL,
  rcases eq_empty_or_nonempty K with rfl | hK' ; rcases eq_empty_or_nonempty L with rfl | hL' ;
  try { simp },
  have hSK:= (hK.is_lub_Sup hK').1,
  have hIK:= (hK.is_glb_Inf hK').1,
  have hSL:= (hL.is_lub_Sup hL').1,
  have hIL:= (hL.is_glb_Inf hL').1,
  apply (finite_Icc ⌈Inf L - Sup K⌉ ⌊Sup L - Inf K⌋).subset,
  rintros n (hn : has_vadd.vadd n '' K ∩ L ≠ ∅),
  rcases ne_empty_iff_nonempty.mp hn with ⟨l, ⟨k, hk, rfl⟩, hnk : (n : ℝ) + k ∈ L⟩,
  split,
  { rw int.ceil_le,
    linarith [hIL hnk, hSK hk] },
  { rw int.le_floor,
    linarith [hSL hnk, hIK hk] }
end⟩

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

lemma periodize_comp_sub (f : ℝ → M) (x t : ℝ) :
  periodize (λ x', f (x' - t)) x = periodize f (x - t) :=
by simp_rw [periodize, sub_add_eq_add_sub]

lemma periodize_smul_periodic (f : ℝ → ℝ) {g : ℝ → E} (hg : periodic g 1) (t : ℝ) :
  (periodize f t) • g t = periodize (λ x, f x • g x) t :=
begin
  dsimp only [periodize],
  rw finsum_smul,
  congr' 1,
  ext n,
  rw one_periodic.add_int hg
end

open measure_theory

lemma integral_periodize [complete_space E] (f : ℝ → E) {a : ℝ} (hf : support f ⊆ Ioc a (a + 1)) :
  ∫ t in a..a+1, periodize f t = ∫ t in a..a+1, f t :=
begin
  apply interval_integral.integral_congr_ae,
  have : ∀ᵐ (x : ℝ), x ∈ interval_oc a (a + 1) → x ∈ Ioo a (a+1),
  {
    sorry },
  apply this.mono,
  intros t ht ht',
  specialize ht ht', clear ht',
  dsimp only [periodize],
  --rw interval_of_le (le_add_of_nonneg_right (zero_le_one : (0 :ℝ) ≤ 1)) at ht,
  have : support (λ n : ℤ, f (t + n)) ⊆ ({0} : finset ℤ),
  { intros n hn,
    suffices : n = 0, by simpa,
    replace hn : t + n ∈ Ioc a (a + 1) := hf (mem_support.mpr hn),
    cases ht,
    cases hn,
    have : -(1 : ℝ) < n, by linarith,
    have : -1 < n,
    exact_mod_cast this,
    have : (n : ℝ) < 1, by linarith,
    norm_cast at this,
    linarith },
  simp [finsum_eq_sum_of_support_subset _ this]
end

-- if convenient we could set `[c,d] = [0,1]`
lemma interval_integral_periodize_smul (f : ℝ → ℝ) (γ : loop F)
  {a b c d : ℝ} (h : b ≤ a + 1) (h2 : d = c + 1)
  (hf : support f ⊆ Ioc a b) :
  ∫ t in c..d, periodize f t • γ t = ∫ t, f t • γ t :=
begin
  rw h2,
  have : support (λ t, f t • γ t) ⊆ Ioc a (a+1),
  { erw support_smul,
    exact ((inter_subset_left _ _).trans hf).trans (Ioc_subset_Ioc_right h) },
  conv_rhs { rw ← indicator_eq_self.mpr this },
  rw integral_indicator (measurable_set_Ioc : measurable_set $ Ioc a $ a+1),
  simp_rw [periodize_smul_periodic _ γ.periodic,
   ← interval_integral.integral_of_le (le_add_of_nonneg_right zero_le_one),

   function.periodic.interval_integral_add_eq (periodic_periodize (λ (x : ℝ), f x • γ x)) c a],
  exact integral_periodize _ this
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

lemma tendsto_sup_dist {X Y : Type*} [topological_space X] [metric_space Y]
  {f : X → Y} {t : X} (h : continuous_at f t)
  {s : ℕ → set X} (hs : tendsto s at_top (𝓝 t).small_sets) :
  tendsto (λ (n : ℕ), ⨆ x ∈ s n, dist (f x) (f t)) at_top (𝓝 0) :=
begin
  rw metric.tendsto_nhds,
  have nonneg : ∀ n, 0 ≤ ⨆ x ∈ s n, dist (f x) (f t),
    from λ n, real.bcsupr_nonneg (λ _ _, dist_nonneg),
  simp only [dist_zero_right, real.norm_eq_abs, abs_of_nonneg, nonneg],
  intros ε ε_pos,
  apply ((𝓝 t).has_basis_small_sets.tendsto_right_iff.mp hs _ $
         metric.tendsto_nhds.mp h (ε/2) (half_pos ε_pos)).mono (λ n hn, _),
  apply lt_of_le_of_lt _ (half_lt_self ε_pos),
  exact real.bcsupr_le (half_pos ε_pos).le (λ x hx, (hn hx).out.le),
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
    exact tendsto_sup_dist (h.comp $ continuous_sub_left t).continuous_at supp_δ },
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

lemma approx_dirac_integral_eq_one (n : ℕ) {a b : ℝ} (h : b = a + 1) :
  ∫ s in a..b, approx_dirac n s = 1 :=
begin
  sorry
end


end delta_approx


section version_of_delta_mollifier_using_n
def delta_mollifier' (n : ℕ) (t : ℝ) : ℝ → ℝ :=
λ x, n / (n+1) * approx_dirac n (x - t) + 1 / (n+1)

variables {n : ℕ} {t : ℝ}
lemma delta_mollifier'_periodic : periodic (delta_mollifier' n t) 1 :=
λ x, by simp_rw [delta_mollifier', ← sub_add_eq_add_sub, periodic_approx_dirac n (x - t)]

lemma delta_mollifier'_pos (s : ℝ) : 0 < delta_mollifier' n t s :=
add_pos_of_nonneg_of_pos
  (mul_nonneg (div_nonneg n.cast_nonneg n.cast_add_one_pos.le) (approx_dirac_nonneg n _))
  (div_pos zero_lt_one n.cast_add_one_pos)

lemma delta_mollifier'_smooth : 𝒞 ∞ (delta_mollifier' n t) :=
(cont_diff_const.mul $ (approx_dirac_smooth n).comp $
  (cont_diff_id.sub cont_diff_const : 𝒞 ∞ (λ x : ℝ, x - t))).add cont_diff_const

open interval_integral
@[simp] lemma delta_mollifier'_integral_eq_one : ∫ s in 0..1, delta_mollifier' n t s = 1 :=
begin
  simp_rw [delta_mollifier'],
  rw [integral_comp_sub_right (λ x, (n : ℝ) / (n+1) * approx_dirac n x + 1 / (n+1)) t, integral_add,
    const_mul, integral_const, zero_sub, sub_neg_eq_add, sub_add_cancel, one_smul,
    approx_dirac_integral_eq_one, mul_one, div_add_div_same, div_self],
  { exact n.cast_add_one_pos.ne' },
  { rw [sub_eq_add_neg, add_comm] },
  { exact ((approx_dirac_smooth n).continuous.interval_integrable _ _).const_mul _ },
  { exact interval_integrable_const }
end

def loop.mollify' (γ : loop F) (n : ℕ) (t : ℝ) : F :=
∫ s in 0..1, delta_mollifier' n t s • γ s

lemma loop.mollify'_eq_convolution (γ : loop F) (hγ : continuous γ) (t : ℝ) :
  γ.mollify' n t = ((n : ℝ) / (n+1)) • ((bump n).normed volume ⋆[lsmul ℝ ℝ] γ) t +
    ((1 : ℝ) / (n+1)) • ∫ t in 0..1, γ t :=
begin
  simp_rw [loop.mollify', delta_mollifier', add_smul, mul_smul],
  rw [integral_add],
  simp_rw [integral_smul, approx_dirac, ← periodize_comp_sub],
  rw [interval_integral_periodize_smul _ γ _ _ (support_shifted_normed_bump_subset n t)],
  simp_rw [convolution_eq_swap, ← neg_sub t, (bump n).normed_neg, lsmul_apply],
  { linarith },
  { rw [zero_add] },
  { exact (continuous_const.smul (((approx_dirac_smooth n).continuous.comp
      (continuous_id.sub continuous_const)).smul hγ)).interval_integrable _ _ },
  { exact (continuous_const.smul hγ).interval_integrable _ _ }
end

lemma loop.tendsto_mollify' (γ : loop F) (hγ : continuous γ) (t : ℝ) :
  tendsto (λ n, γ.mollify' n t) at_top (𝓝 (γ t)) :=
begin
  simp_rw [γ.mollify'_eq_convolution hγ],
  rw [← add_zero (γ t)],
  refine tendsto.add _ _,
  { rw [← one_smul ℝ (γ t)],
    refine tendsto_self_div_add_at_top_nhds_1_nat.smul _,
    refine cont_diff_bump_of_inner.convolution_tendsto _ hγ t,
    simp_rw [bump], norm_cast,
    exact (tendsto_add_at_top_iff_nat 2).2 (tendsto_const_div_at_top_nhds_0_nat 1) },
  { rw [← zero_smul ℝ (_ : F)],
    exact tendsto_one_div_add_at_top_nhds_0_nat.smul tendsto_const_nhds }
end

end version_of_delta_mollifier_using_n

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

def loop.mollify (γ : loop F) (η t : ℝ) : F :=
if η = 0 then γ t else ∫ s in 0..1, delta_mollifier η t s • γ s

@[simp] lemma loop.mollify_eq_of_eq_zero (γ : loop F) (t : ℝ) :
  γ.mollify 0 t = γ t :=
if_pos rfl

lemma loop.mollify_eq_of_ne_zero (γ : loop F) (η t : ℝ) (hη : η ≠ 0) :
  γ.mollify η t = ∫ s in 0..1, delta_mollifier η t s • γ s :=
if_neg hη

lemma loop.mollify_sub (γ₁ γ₂ : loop F) (hγ₁ : continuous γ₁) (hγ₂ : continuous γ₂) (η t : ℝ) :
  γ₁.mollify η t - γ₂.mollify η t = (γ₁ - γ₂).mollify η t :=
begin
  rcases eq_or_ne η 0 with hη | hη,
  { simp [hη], },
  { simp only [loop.mollify_eq_of_ne_zero _ _ _ hη, loop.sub_apply, smul_sub],
    rw interval_integral.integral_sub,
    exacts [((delta_mollifier_smooth' hη t).continuous.smul hγ₁).interval_integrable 0 1,
            ((delta_mollifier_smooth' hη t).continuous.smul hγ₂).interval_integrable 0 1], },
end

lemma loop.tendsto_mollify (γ : loop F) (hf : continuous γ) (t : ℝ) :
  tendsto (λ η, γ.mollify η t) (𝓝 0) (𝓝 (γ t)) :=
sorry
