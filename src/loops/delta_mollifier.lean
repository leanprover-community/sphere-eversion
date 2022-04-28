import measure_theory.integral.interval_integral
import measure_theory.group.integration
import analysis.calculus.specific_functions

import to_mathlib.convolution
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
  { rw interval_oc_of_le (le_add_of_nonneg_right (zero_le_one : (0 :ℝ) ≤ 1)),
    have : ∀ᵐ x : ℝ, x ≠ a + 1,
    { rw ae_iff,
      simp },
    apply this.mono,
    rintros x (x_ne : x ≠ a + 1) ⟨hx, hx'⟩,
    exact ⟨hx, x_ne.le_iff_lt.mp hx'⟩ },
  apply this.mono,
  intros t ht ht',
  specialize ht ht', clear ht',
  dsimp only [periodize],
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
  rw ← interval_integral.integral_eq_integral_of_support_subset this,
  simp_rw [periodize_smul_periodic _ γ.periodic,
    function.periodic.interval_integral_add_eq (periodic_periodize (λ (x : ℝ), f x • γ x)) c a],
  exact integral_periodize _ this
end

end

section delta_approx

/-- ## An approximate Dirac "on the circle". -/

def approx_dirac (n : ℕ) : ℝ → ℝ :=
periodize $ (bump n).normed volume

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
  have supp : support ((bump n).normed volume) ⊆ Ioc (-(1 / 2)) (-(1 / 2) + 1),
  { rw [show -(1/2 : ℝ) + 1 = 1/2, by norm_num,
        show support ((bump n).normed volume) = _, from (bump n).support_normed_eq,
        real.ball_zero_eq, show (bump n).R = 1/(n+2 : ℝ), from rfl],
    have key : 1 / (n + 2 : ℝ) ≤ 1 / 2,
    { apply one_div_le_one_div_of_le,
      norm_num,
      norm_cast,
      norm_num },
    exact (Ioo_subset_Ioo (neg_le_neg key) key).trans (Ioo_subset_Ioc_self) },
  rw [approx_dirac, h,
      function.periodic.interval_integral_add_eq (periodic_periodize _) a (-(1/2 : ℝ)),
      integral_periodize _ supp,
      interval_integral.integral_eq_integral_of_support_subset supp],
  exact (bump n).integral_normed
end

end delta_approx

section version_of_delta_mollifier_using_n
def delta_mollifier (n : ℕ) (t : ℝ) : ℝ → ℝ :=
λ x, n / (n+1) * approx_dirac n (x - t) + 1 / (n+1)

variables {n : ℕ} {t : ℝ}
lemma delta_mollifier_periodic : periodic (delta_mollifier n t) 1 :=
λ x, by simp_rw [delta_mollifier, ← sub_add_eq_add_sub, periodic_approx_dirac n (x - t)]

lemma delta_mollifier_pos (s : ℝ) : 0 < delta_mollifier n t s :=
add_pos_of_nonneg_of_pos
  (mul_nonneg (div_nonneg n.cast_nonneg n.cast_add_one_pos.le) (approx_dirac_nonneg n _))
  (div_pos zero_lt_one n.cast_add_one_pos)

lemma delta_mollifier_smooth : 𝒞 ∞ (delta_mollifier n t) :=
(cont_diff_const.mul $ (approx_dirac_smooth n).comp $
  (cont_diff_id.sub cont_diff_const : 𝒞 ∞ (λ x : ℝ, x - t))).add cont_diff_const

open interval_integral
@[simp] lemma delta_mollifier_integral_eq_one : ∫ s in 0..1, delta_mollifier n t s = 1 :=
begin
  simp_rw [delta_mollifier],
  rw [integral_comp_sub_right (λ x, (n : ℝ) / (n+1) * approx_dirac n x + 1 / (n+1)) t, integral_add,
    const_mul, integral_const, zero_sub, sub_neg_eq_add, sub_add_cancel, one_smul,
    approx_dirac_integral_eq_one, mul_one, div_add_div_same, div_self],
  { exact n.cast_add_one_pos.ne' },
  { rw [sub_eq_add_neg, add_comm] },
  { exact ((approx_dirac_smooth n).continuous.interval_integrable _ _).const_mul _ },
  { exact interval_integrable_const }
end

def loop.mollify (γ : loop F) (n : ℕ) (t : ℝ) : F :=
∫ s in 0..1, delta_mollifier n t s • γ s

lemma loop.mollify_eq_convolution (γ : loop F) (hγ : continuous γ) (t : ℝ) :
  γ.mollify n t = ((n : ℝ) / (n+1)) • ((bump n).normed volume ⋆[lsmul ℝ ℝ] γ) t +
    ((1 : ℝ) / (n+1)) • ∫ t in 0..1, γ t :=
begin
  simp_rw [loop.mollify, delta_mollifier, add_smul, mul_smul],
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

lemma loop.tendsto_mollify (γ : loop F) (hγ : continuous γ) (t : ℝ) :
  tendsto (λ n, γ.mollify n t) at_top (𝓝 (γ t)) :=
begin
  simp_rw [γ.mollify_eq_convolution hγ],
  rw [← add_zero (γ t)],
  refine tendsto.add _ _,
  { rw [← one_smul ℝ (γ t)],
    refine tendsto_self_div_add_at_top_nhds_1_nat.smul _,
    refine cont_diff_bump_of_inner.convolution_tendsto_right _ hγ t,
    simp_rw [bump], norm_cast,
    exact (tendsto_add_at_top_iff_nat 2).2 (tendsto_const_div_at_top_nhds_0_nat 1) },
  { rw [← zero_smul ℝ (_ : F)],
    exact tendsto_one_div_add_at_top_nhds_0_nat.smul tendsto_const_nhds }
end

lemma loop.mollify_sub (γ₁ γ₂ : loop F) (hγ₁ : continuous γ₁) (hγ₂ : continuous γ₂)
  (n : ℕ) (t : ℝ) :
  γ₁.mollify n t - γ₂.mollify n t = (γ₁ - γ₂).mollify n t :=
begin
  simp only [loop.mollify, loop.sub_apply, smul_sub],
  rw interval_integral.integral_sub,
  exacts [(delta_mollifier_smooth.continuous.smul hγ₁).interval_integrable 0 1,
          (delta_mollifier_smooth.continuous.smul hγ₂).interval_integrable 0 1],
end

end version_of_delta_mollifier_using_n
