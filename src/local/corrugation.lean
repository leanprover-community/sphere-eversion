import analysis.asymptotics.asymptotics
import linear_algebra.dual
import measure_theory.integral.interval_integral
import analysis.calculus.parametric_integral

import to_mathlib.topology.periodic
import to_mathlib.analysis.calculus
import to_mathlib.filter
import to_mathlib.measure_theory.parametric_interval_integral

import loops.basic

noncomputable theory


local notation `D` := fderiv ℝ
local notation `∂₁` := partial_fderiv_fst ℝ
local notation `𝒞` := times_cont_diff ℝ
local notation u ` ⬝ `:70 φ:65 :=
  continuous_linear_map.comp (continuous_linear_map.to_span_singleton ℝ u) φ

open set function finite_dimensional asymptotics filter topological_space int measure_theory
     continuous_linear_map
open_locale topological_space

section c0
variables {E : Type*}
          {F : Type*} [normed_group F] [normed_space ℝ F] [measurable_space F] [borel_space F]
          [finite_dimensional ℝ F]

/-- Theillière's corrugations. -/
def corrugation (π : E → ℝ) (N : ℝ) (γ : E → loop F) : E → F :=
λ x, (1/N) • ∫ t in 0..(N*π x), (γ x t - (γ x).average)

def corrugate (f : E → F) (π : E → ℝ) (N : ℝ) (γ : E → loop F) : E → F :=
λ x, f x + (1/N) • ∫ t in 0..(N*π x), (γ x t - (γ x).average)

lemma per_corrugation (γ : loop F) (hγ : ∀ s t, interval_integrable γ volume s t) :
  one_periodic (λ s, ∫ t in 0..s, γ t - γ.average) :=
begin
  have int_avg : ∀ s t,  interval_integrable (λ u : ℝ, γ.average) volume s t,
    from λ s t, interval_integrable_const,
  intros s,
  have int₁ : interval_integrable (λ t, γ t - γ.average) volume 0 s,
    from (hγ _ _).sub (int_avg _ _),
  have int₂ : interval_integrable (λ t, γ t - γ.average) volume s (s + 1),
    from (hγ _ _).sub (int_avg _ _),
  have int₃ : interval_integrable γ volume s (s + 1), from hγ _ _,
  have int₄ : interval_integrable (λ t, γ.average) volume s (s + 1), from int_avg _ _,
  dsimp only,
  /- Rmk: Lean doesn't want to rewrite using `interval_integral.integral_sub` without being
    given the integrability assumptions :-( -/
  rw [← interval_integral.integral_add_adjacent_intervals int₁ int₂,
      interval_integral.integral_sub int₃ int₄, interval_integral_periodic γ.per hγ, loop.average],
  simp only [add_zero, add_tsub_cancel_left, interval_integral.integral_const, one_smul, sub_self]
end

variables (π : E → ℝ) (N : ℝ) {γ : E → loop F} [topological_space E]

@[simp] lemma corrugation_const {x : E} (h : (γ x).is_const) : corrugation π N γ x = 0 :=
begin
  unfold corrugation,
  rw loop.is_const_iff_const_avg at h,
  rw h,
  simp only [add_zero, interval_integral.integral_const, loop.const_apply, loop.average_const, smul_zero, sub_self]
end

lemma corrugation.support : support (corrugation π N γ) ⊆ loop.support γ :=
begin
  intros x x_in,
  apply subset_closure,
  intro h,
  apply x_in,
  simp [h]
end

/-- If a loop family has compact support then the corresponding corrugation is
`O(1/N)` uniformly in the source point. -/
lemma corrugation.c0_small [first_countable_topology E]
  [locally_compact_space E] (hγ : is_compact (loop.support γ))
  (hγ_cont : continuous ↿γ) {ε : ℝ} (ε_pos : 0 < ε) :
  ∀ᶠ N in at_top, ∀ x, ∥corrugation π N γ x∥ < ε :=
begin
  obtain ⟨C, hC⟩ : ∃ C, ∀ x b, ∥∫ t in 0..b, (γ x t - (γ x).average)∥ ≤ C,
  { apply continuous.bounded_of_one_periodic_of_compact _ _ hγ,
    { intros x hx,
      ext t,
      rw loop.const_of_not_mem_support hx,
      simp },
    { let φ : E → ℝ → F := λ x s, (γ x) s - (γ x).average,
      have cont_φ : continuous (λ p : E × ℝ, φ p.1 p.2),
        from hγ_cont.sub ((loop.continuous_average hγ_cont).comp continuous_fst),
      exact continuous_parametric_primitive_of_continuous cont_φ },
    { intro x,
      exact per_corrugation _ (loop.continuous_of_family hγ_cont x).interval_integrable } },
  apply (const_mul_one_div_lt ε_pos C).mono,
  intros N hN x,
  rw [corrugation, norm_smul, mul_comm],
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (hC x (N*π x)) (norm_nonneg $ 1/N)) hN,
end

end c0

section c1

variables {E : Type*} [normed_group E] [normed_space ℝ E] [finite_dimensional ℝ E]
          {F : Type*} [normed_group F] [normed_space ℝ F] [measurable_space F] [borel_space F]
          [finite_dimensional ℝ F]


variables (π : E → ℝ) (N : ℝ) (γ : E → loop F)
          (hγ : is_compact (loop.support γ))

def corrugation.remainder (π : E → ℝ) (N : ℝ) (γ : E → loop F) : E → (E →L[ℝ] F) :=
λ x, (1/N) • ∫ t in 0..(N*π x), ∂₁ (λ x t, (γ x).normalize t) x t

local notation `R` := corrugation.remainder π
local notation `𝒯` := corrugation π

lemma remainder_eq (N : ℝ) {γ : E → loop F} (h : 𝒞 1 ↿γ) :
R N γ = λ x, (1/N) • ∫ t in 0..(N*π x), (loop.diff γ x).normalize t :=
by { simp_rw loop.diff_normalize h, refl }

lemma remainder_eq' (x : E) {γ : E → loop F} (h : 𝒞 1 ↿γ) :
(λ (N : ℝ), R N γ x) = λ N, (1/N) • ∫ t in 0..(N*π x), (loop.diff γ x).normalize t :=
begin
  ext N,
  rw remainder_eq π _ h
end

variables {π} {γ}

lemma corrugation.times_cont_diff {n : with_top ℕ} (hπ_diff : 𝒞 n π) (hγ_diff : 𝒞 n ↿γ) :
  𝒞 n (𝒯 N γ) :=
begin
  apply times_cont_diff.const_smul,
  apply times_cont_diff_parametric_primitive_of_times_cont_diff _ (hπ_diff.const_smul N) 0,
  exact times_cont_diff_sub_average hγ_diff
end

lemma corrugation.fderiv_eq (hN : N ≠ 0) (hπ_diff : 𝒞 1 π) (hγ_diff : 𝒞 1 ↿γ) :
  D (𝒯 N γ) = λ x : E, (γ x (N*π x) - (γ x).average) ⬝ (D π x) + R N γ x :=
begin
  ext1 x₀,
  have diff := times_cont_diff_sub_average hγ_diff,
  have key :=
    (has_fderiv_at_parametric_primitive_of_times_cont_diff' diff (hπ_diff.const_smul N) x₀ 0).2,
  erw [fderiv_const_smul key.differentiable_at,
       key.fderiv,
       smul_add, add_comm],
  congr' 1,
  rw fderiv_const_smul (hπ_diff.differentiable le_rfl).differentiable_at N,
  simp only [smul_smul, inv_mul_cancel hN, one_div, algebra.id.smul_eq_mul, one_smul,
              continuous_linear_map.comp_smul]
end

lemma remainder_c0_small (hγ : is_compact (loop.support γ))
  (hγ_diff : 𝒞 1 ↿γ) {ε : ℝ} (ε_pos : 0 < ε) :
  ∀ᶠ N in at_top, ∀ x, ∥R N γ x∥ < ε :=
begin
  have : is_compact (loop.support $ loop.diff γ),
    from loop.compact_support_diff hγ,
  apply (corrugation.c0_small π this (loop.continuous_diff hγ_diff) ε_pos).mono,
  intros N H x,
  have key := congr_fun (remainder_eq' π x hγ_diff) N,
  dsimp only at key,
  rw key,
  exact H x
end

variables {π}

lemma corrugation.fderiv (hπ : 𝒞 1 π) (hγ_diff : 𝒞 1 ↿γ) (hγ_supp : is_compact (loop.support γ)) {ε : ℝ} (ε_pos : 0 < ε) :
  ∀ᶠ N in at_top, ∀ x, ∥D (𝒯 N γ) x - (γ x (N*π x) - (γ x).average) ⬝ (D π x)∥ < ε :=
begin
  apply ((remainder_c0_small π hγ_supp hγ_diff ε_pos).and (eventually_ne_at_top (0 : ℝ))).mono,
  rintros N ⟨hN, N_ne⟩ x,
  simpa only [corrugation.fderiv_eq N N_ne hπ hγ_diff, add_sub_cancel'] using hN x
end

lemma corrugation.fderiv_ker (hπ : 𝒞 1 π) (hγ_diff : 𝒞 1 ↿γ) (hγ_supp : is_compact (loop.support γ)) {ε : ℝ} (ε_pos : 0 < ε) :
  ∀ᶠ N in at_top, ∀ x, ∀ w ∈ (D π x : E →ₗ[ℝ] ℝ).ker,
  ∥D (𝒯 N γ) x w∥ ≤ ε*∥w∥ :=
begin
  apply (corrugation.fderiv hπ hγ_diff hγ_supp ε_pos).mono,
  intros N hN x w hw,
  let φ := D (corrugation π N γ) x - (γ x (N * π x) - (γ x).average) ⬝ D π x,
  rw linear_map.mem_ker at hw,
  change D π x w = 0 at hw,
  have : D (corrugation π N γ) x w = φ w,
  { simp only [φ, hw, continuous_linear_map.coe_comp', continuous_linear_map.coe_sub', sub_zero, 
               comp_app, pi.sub_apply, continuous_linear_map.map_zero] },
  rw this,
  exact φ.le_of_op_norm_le (hN x).le w
end
 
lemma corrugation.fderiv_u (hπ : 𝒞 1 π) (hγ_diff : 𝒞 1 ↿γ) (hγ_supp : is_compact (loop.support γ))
  {u : E} (hu : ∀ x, D π x u = 1) {ε : ℝ} (ε_pos : 0 < ε) :
  ∀ᶠ N in at_top, ∀ x, ∥D (𝒯 N γ) x u - (γ x (N*π x) - (γ x).average)∥ ≤  ε*∥u∥ :=
begin
  apply (corrugation.fderiv hπ hγ_diff hγ_supp ε_pos).mono,
  intros N hN x,
  let φ := D (corrugation π N γ) x - (γ x (N * π x) - (γ x).average) ⬝ D π x,
  rw show (D (corrugation π N γ) x) u - (γ x (N * π x) - (γ x).average) = φ u,
    by simp [φ, hu, continuous_linear_map.to_span_singleton_apply],
  exact le_of_op_norm_le φ (hN x).le u
end

structure corrugation_data (f : E → F) (U : set E):=
(π : E →L[ℝ] ℝ)
(u : E)
(hu : ∥u∥ = 1)
(hπu : π u = 1)
(γ : E → loop F)
(hγ_diff : 𝒞 ⊤ ↿γ)
(hγ_supp : is_compact (loop.support γ))
(hγ_avg : ∀ {x}, x ∈ U → (γ x).average = D f x u)

def corrugation_data.fun {f : E → F} {U : set E} (d : corrugation_data f U) : ℝ → E → F :=
λ N, f + corrugation d.π N d.γ

lemma corrugation_data.C1_π {f : E → F} {U : set E} (d : corrugation_data f U) : 𝒞 1 d.π :=
d.π.times_cont_diff

lemma corrugation_data.C1_γ {f : E → F} {U : set E} (d : corrugation_data f U) : 𝒞 1 ↿d.γ :=
d.hγ_diff.of_le le_top

lemma corrugation_data.Dπu {f : E → F} {U : set E} (d : corrugation_data f U) : 
  ∀ x, D d.π x d.u = 1  :=
λ x, by { rw d.π.fderiv, exact d.hπu }

lemma corrugation_data.C1_corrugation {f : E → F} {U : set E} (d : corrugation_data f U) (N : ℝ) :
  𝒞 1 (corrugation ⇑(d.π) N d.γ) :=
corrugation.times_cont_diff N d.C1_π d.C1_γ

lemma corrugation_data.Dfun {f : E → F} {U : set E} (d : corrugation_data f U) (hf : 𝒞 1 f) (N : ℝ) :
  D(d.fun N) = D f + D (corrugation d.π N d.γ) :=
begin
  ext x,
  erw [corrugation_data.fun, fderiv_add],
  refl,
  apply (hf.differentiable le_rfl).differentiable_at,
  apply ((d.C1_corrugation N).differentiable le_rfl).differentiable_at,
end

lemma corrugation_data.C1_fun {f : E → F} {U : set E} (d : corrugation_data f U) (hf : 𝒞 1 f) (N : ℝ) :
  𝒞 1 (d.fun N) :=
hf.add (d.C1_corrugation N)

lemma corrugation_data.c0_close {f : E → F} {U : set E} (d : corrugation_data f U) {ε : ℝ} (ε_pos : 0 < ε)  :
  ∀ᶠ N in at_top, ∀ x, ∥d.fun N x - f x∥ < ε :=
begin
  apply (corrugation.c0_small d.π d.hγ_supp d.hγ_diff.continuous ε_pos).mono,
  intros N hN x,
  simpa [corrugation_data.fun] using hN x
end

lemma corrugation_data.deriv_ker_π {f : E → F} {U : set E} (d : corrugation_data f U) (hf : 𝒞 1 f) {ε : ℝ} (ε_pos : 0 < ε)  :
  ∀ᶠ N in at_top, ∀ x ∈ U, ∀ w ∈ d.π.ker, ∥D (d.fun N) x w - D f x w∥ ≤ ε*∥w∥ :=
begin
  apply (corrugation.fderiv_ker d.C1_π d.C1_γ d.hγ_supp ε_pos).mono,
  simp_rw d.π.fderiv,
  intros N hN x x_in w w_in,
  simpa [d.Dfun hf] using hN x w w_in  
end

lemma corrugation_data.deriv_u {f : E → F} {U : set E} (d : corrugation_data f U) (hf : 𝒞 1 f) {ε : ℝ} (ε_pos : 0 < ε)  :
  ∀ᶠ N in at_top, ∀ x ∈ U, ∥D (d.fun N) x d.u -  d.γ x (N*d.π x)∥ ≤ ε :=
begin
  apply (corrugation.fderiv_u d.C1_π d.C1_γ d.hγ_supp d.Dπu ε_pos).mono,
  intros N hN x x_in,
  specialize hN x,
  rw [d.hγ_avg x_in, d.hu, mul_one] at hN,
  convert hN using 2,
  rw [d.Dfun hf],
  abel
end

lemma theilliere {f : E → F} {U : set E} (d : corrugation_data f U) (hf : 𝒞 1 f) {ε : ℝ} (ε_pos : 0 < ε)  :
  ∀ᶠ N in at_top, ∀ x, 
∥d.fun N x - f x∥ < ε ∧ (x ∈ U → ((∀ w ∈ d.π.ker, ∥D (d.fun N) x w - D f x w∥ ≤ ε*∥w∥) ∧ ∥D (d.fun N) x d.u -  d.γ x (N*d.π x)∥ ≤ ε)) :=
begin
  apply ((d.c0_close ε_pos).and ((d.deriv_ker_π hf ε_pos).and (d.deriv_u hf ε_pos))).mono,
  tauto
end

lemma corrugation_data.relative {f : E → F} {U : set E} (d : corrugation_data f U) :
∀ x, (d.γ x).is_const → d.fun N x = f x :=
begin
  intros x hx,
  change f x + corrugation d.π N d.γ x = _,
  simp only [hx, add_zero, corrugation_const]  
end

end c1

open module (dual)

variables (E : Type*) [normed_group E] [normed_space ℝ E]

-- TODO: move mathlib's dual_pair out of the root namespace!

structure dual_pair'
(π : dual ℝ E)
(v : E)
(pairing : π v = 1)
