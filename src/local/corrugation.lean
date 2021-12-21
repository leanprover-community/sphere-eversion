import analysis.asymptotics.asymptotics
import linear_algebra.dual
import measure_theory.integral.interval_integral
import analysis.calculus.parametric_integral
import algebra.periodic

import to_mathlib.topology.tsupport
import to_mathlib.analysis.calculus
import to_mathlib.filter
import to_mathlib.measure_theory.parametric_interval_integral

import loops.basic

noncomputable theory

/-

TODO generalize many lemmas to any period and add to algebra/periodic.lean

-/

local notation `D` := fderiv ℝ
local notation `∂₁` := partial_fderiv_fst ℝ
local notation `𝒞` := times_cont_diff ℝ

open set function finite_dimensional asymptotics filter topological_space int
open_locale topological_space


section one_periodic

variables {α : Type*}

def ℤ_sub_ℝ : add_subgroup ℝ := add_monoid_hom.range (int.cast_add_hom ℝ)

def trans_one : setoid ℝ := quotient_add_group.left_rel ℤ_sub_ℝ

def one_periodic (f : ℝ → α) : Prop := periodic f 1

lemma one_periodic.add_nat {f : ℝ → α} (h : one_periodic f) : ∀ k : ℕ, ∀ x, f (x + k) = f x :=
begin
  intros k x,
  induction k with k hk,
  { simp },
  change f (x + (k + 1)) = _,
  rw [← hk, ← add_assoc, h]
end

lemma one_periodic.add_int {f : ℝ → α} (h : one_periodic f) : ∀ k : ℤ, ∀ x, f (x + k) = f x :=
begin
  intros k x,
  induction k with k k,
  { erw h.add_nat },
  have : x + -[1+ k] + (k + 1 : ℕ) = x, by { simp, ring },
  rw [← h.add_nat (k+1) (x + -[1+ k]), this]
end

/-- The circle `𝕊₁ := ℝ/ℤ`. -/
@[derive [topological_space, inhabited]]
def 𝕊₁ := quotient trans_one

lemma trans_one_rel_iff {a b : ℝ} : trans_one.rel a b ↔ ∃ k : ℤ, b = a + k :=
begin
  apply exists_congr,
  intro k,
  change (k : ℝ) = _ ↔ _,
  split ; intro h ; linarith [h]
end

section
local attribute [instance] trans_one

def proj_𝕊₁ : ℝ → 𝕊₁ := quotient.mk

@[simp]
lemma proj_𝕊₁_add_int (t : ℝ) (k : ℤ) : proj_𝕊₁ (t + k) = proj_𝕊₁ t :=
begin
  symmetry,
  apply quotient.sound,
  exact (trans_one_rel_iff.mpr ⟨k, rfl⟩)
end

def 𝕊₁.repr (x : 𝕊₁) : ℝ := let t := quotient.out x in fract t

lemma 𝕊₁.repr_mem (x : 𝕊₁) : x.repr ∈ (Ico 0 1 : set ℝ) :=
⟨fract_nonneg _, fract_lt_one _⟩

lemma 𝕊₁.proj_repr (x : 𝕊₁) : proj_𝕊₁ (x.repr) = x :=
begin
  symmetry,
  conv_lhs { rw ← quotient.out_eq x },
  rw ← fract_add_floor (quotient.out x),
  apply proj_𝕊₁_add_int
end

lemma image_proj_𝕊₁_Ico : proj_𝕊₁ '' (Ico 0 1) = univ :=
begin
  rw eq_univ_iff_forall,
  intro x,
  use [x.repr, x.repr_mem, x.proj_repr],
end

lemma image_proj_𝕊₁_Icc : proj_𝕊₁ '' (Icc 0 1) = univ :=
eq_univ_of_subset (image_subset proj_𝕊₁ Ico_subset_Icc_self) image_proj_𝕊₁_Ico

@[continuity]
lemma continuous_proj_𝕊₁ : continuous proj_𝕊₁ := continuous_quotient_mk

lemma is_open_map_proj_𝕊₁ : is_open_map proj_𝕊₁ :=
quotient_add_group.is_open_map_coe ℤ_sub_ℝ

lemma quotient_map_id_proj_𝕊₁ {X : Type*} [topological_space X] :
  quotient_map (λ p : X × ℝ, (p.1, proj_𝕊₁ p.2)) :=
(is_open_map.id.prod is_open_map_proj_𝕊₁).to_quotient_map (continuous_id.prod_map continuous_proj_𝕊₁)
  (surjective_id.prod_map quotient.exists_rep)


def one_periodic.lift {f : ℝ → α} (h : one_periodic f) : 𝕊₁ → α :=
quotient.lift f (by { intros a b hab, rcases trans_one_rel_iff.mp hab with ⟨k, rfl⟩, rw h.add_int })

end

local notation `π` := proj_𝕊₁

instance : compact_space 𝕊₁ :=
⟨by { rw ← image_proj_𝕊₁_Icc, exact is_compact_Icc.image continuous_proj_𝕊₁ }⟩

variables {X E : Type*} [topological_space X] [normed_group E]

lemma continuous.bounded_of_one_periodic_of_compact {f : X → ℝ → E} (cont : continuous ↿f)
  (hper : ∀ x, one_periodic (f x)) {K : set X} (hK : is_compact K) (hfK : ∀ x ∉ K, f x = 0) :
  ∃ C, ∀ x t, ∥f x t∥ ≤ C :=
begin
  let F : X × 𝕊₁ → E := λ p : X × 𝕊₁, (hper p.1).lift p.2,
  have Fcont : continuous F,
  { have qm : quotient_map (λ p : X × ℝ, (p.1, π p.2)) := quotient_map_id_proj_𝕊₁,
    let φ := ↿f, -- avoid weird elaboration issue
    have : φ = F ∘ (λ p : X × ℝ, (p.1, π p.2)), by { ext p, refl },
    dsimp [φ] at this,
    rwa [this,  ← qm.continuous_iff] at cont },
  have hFK : ∀ x : X × 𝕊₁, x ∉ (K.prod (univ : set 𝕊₁)) → F x = 0,
  { rintros ⟨x, ⟨t⟩⟩ hxt,
    have : ∀ a, f x a = 0, by simpa using congr_fun (hfK x $ λ hx, hxt (by simp [hx])),
    apply this },
  obtain ⟨C, hC⟩ : ∃ C, ∀ (x : X × 𝕊₁), ∥F x∥ ≤ C :=
    Fcont.bounded_of_vanishing_outside_compact (hK.prod compact_univ) hFK,
  exact ⟨C, λ x t, hC (x, π t)⟩,
end

end one_periodic

section c0
variables {E : Type*}
          {F : Type*} [normed_group F] [normed_space ℝ F] [measurable_space F] [borel_space F]
          [finite_dimensional ℝ F]

open measure_theory

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

@[simp] lemma loop.average_const {f : F} : (loop.const f).average = f :=
by simp [loop.average]

@[simp] lemma corrugation_const {x : E} (h : (γ x).is_const) : corrugation π N γ x = 0 :=
begin
  unfold corrugation,
  rw loop.is_const_iff_const_avg at h,
  rw h,
  simp only [add_zero, interval_integral.integral_const, loop.const_apply, loop.average_const, smul_zero, sub_self]
end

lemma support_aux {γ : loop F} (h : γ = loop.const (γ.average)) (b : ℝ) :
  ∫ t in 0..b, γ t - γ.average = 0  :=
begin
  rw h,
  simp -- Note: one cannot use `simp [h]` because `γ` appears on both side.
end

lemma corrugation.support : support (corrugation π N γ) ⊆ loop.support γ :=
begin
  intros x x_in,
  apply subset_closure,
  intro h,
  apply x_in,
  simp [h]
end

lemma continuous_average [first_countable_topology E] [locally_compact_space E]
  (hγ_cont : continuous ↿γ) : continuous (λ x, (γ x).average) :=
continuous_parametric_interval_integral_of_continuous' hγ_cont _ _

/-
The lemma below is ridiculously painful, but Patrick isn't patient enough.
-/
lemma foo' {ε : ℝ} (ε_pos : 0 < ε) (C : ℝ) : ∀ᶠ (N : ℝ) in at_top, C*∥1/N∥ < ε :=
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
      exact support_aux (loop.const_of_not_mem_support hx) t },
    { let φ : E → ℝ → F := λ x s, (γ x) s - (γ x).average,
      have cont_φ : continuous (λ p : E × ℝ, φ p.1 p.2),
        from hγ_cont.sub ((continuous_average hγ_cont).comp continuous_fst),
      exact continuous_parametric_primitive_of_continuous cont_φ },
    { intro x,
      exact per_corrugation _ (loop.continuous_of_family hγ_cont x).interval_integrable } },
  apply (foo' ε_pos C).mono,
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

open linear_map



def loop.diff (γ : E → loop F) (e : E) : loop (E →L[ℝ] F) :=
{ to_fun := λ t, ∂₁ (λ e t, γ e t) e t,
  per' := λ t, by simp only [partial_fderiv_fst, loop.per] }

@[simp]
lemma loop.diff_apply (γ : E → loop F) (e : E) (t : ℝ) : loop.diff γ e t = ∂₁ (λ e t, γ e t) e t :=
rfl

lemma loop.average_diff {γ : E → loop F} (hγ_diff : 𝒞 1 ↿γ) (e : E) :
(loop.diff γ e).average = D (λ e, (γ e).average) e :=
begin
  change 𝒞 1 ↿(λ (e : E) (t : ℝ), γ e t) at hγ_diff,
  simpa only [loop.average, hγ_diff.fderiv_parametric_integral]
end

lemma loop.continuous_diff {γ : E → loop F} (h : 𝒞 1 ↿γ) : continuous (↿(loop.diff γ)) :=
times_cont_diff.continuous_partial_fst (h : _)

def loop.normalize (γ : loop F) : loop F :=
{ to_fun := λ t, γ t - γ.average,
  per' := λ t, by simp [γ.per] }

@[simp]
lemma loop.normalize_apply (γ : loop F) (t : ℝ) : loop.normalize γ t = γ t - γ.average :=
rfl

lemma times_cont_diff.partial_loop {γ : E → loop F} (hγ_diff : 𝒞 1 ↿γ) :
  ∀ t, 𝒞 1 (λ e, γ e t) :=
λ t, hγ_diff.comp ((times_cont_diff_prod_left t).of_le le_top)

lemma times_cont_diff.loop_average {γ : E → loop F} {n : with_top ℕ} (hγ_diff : 𝒞 n ↿γ) :
  𝒞 n (λ e, (γ e).average) :=
times_cont_diff_parametric_integral_of_times_cont_diff hγ_diff _ _

lemma loop.diff_normalize {γ : E → loop F} (hγ_diff : 𝒞 1 ↿γ) (e : E) :
  (loop.diff γ e).normalize = loop.diff (λ e, (γ e).normalize) e :=
begin
  ext t x,
  simp only [loop.diff_apply, loop.normalize_apply, partial_fderiv_fst],
  rw [fderiv_sub ((hγ_diff.partial_loop t).differentiable le_rfl).differentiable_at,
      loop.average_diff hγ_diff],
  exact (hγ_diff.loop_average.differentiable le_rfl).differentiable_at
end

lemma loop.support_diff {γ : E → loop F} (h : 𝒞 1 ↿γ) :
  loop.support (loop.diff γ) ⊆ loop.support γ :=
begin
  unfold loop.support,
  erw [closure_compl, closure_compl],
  rw compl_subset_compl,
  intros x hx,
  rw mem_interior_iff_mem_nhds at *,
  rcases mem_nhds_iff.mp hx with ⟨U, hU, U_op, hxU⟩,
  have U_nhds : U ∈ 𝓝 x, from is_open.mem_nhds U_op hxU,
  apply mem_of_superset U_nhds,
  intros y hy,
  have Hy : ∀ t, (λ z, γ z t) =ᶠ[𝓝 y] (λ z, (γ z).average),
  { intro t,
    apply mem_of_superset (U_op.mem_nhds hy),
    intros z hz,
    exact loop.is_const_iff_forall_avg.mp (hU hz) t },
  have : ∀ (t : ℝ), loop.diff γ y t = D (λ (z : E), (γ z).average) y := λ t, (Hy t).fderiv_eq,
  intros t s,
  simp [this, loop.average_diff h]
end

lemma loop.compact_support_diff {γ : E → loop F} (h : 𝒞 1 ↿γ) (h' : is_compact (loop.support γ)):
  is_compact (loop.support $ loop.diff γ) :=
compact_of_is_closed_subset h' is_closed_closure (loop.support_diff h)

def corrugation.remainder (π : E → ℝ) (N : ℝ) (γ : E → loop F) : E → (E →L[ℝ] F) :=
λ x, (1/N) • ∫ t in 0..(N*π x), ∂₁ (λ x t, (γ x).normalize t) x t

local notation `R` := corrugation.remainder π
local notation `𝒯` := corrugation π
local notation u ` ⬝ `:70 φ:65 :=
  continuous_linear_map.comp (continuous_linear_map.to_span_singleton ℝ u) φ

lemma remainder_eq (N : ℝ) {γ : E → loop F} (h : 𝒞 1 ↿γ) :
R N γ = λ x, (1/N) • ∫ t in 0..(N*π x), (loop.diff γ x).normalize t :=
by { simp_rw loop.diff_normalize h, refl }

lemma remainder_eq' (x : E) {γ : E → loop F} (h : 𝒞 1 ↿γ) :
(λ (N : ℝ), R N γ x) = λ N, (1/N) • ∫ t in 0..(N*π x), (loop.diff γ x).normalize t :=
begin
  ext N,
  rw remainder_eq π _ h
end

variable {γ}

lemma times_cont_diff_average {n : with_top ℕ} (hγ_diff : 𝒞 n ↿γ) : 𝒞 n (λ x, (γ x).average) :=
times_cont_diff_parametric_primitive_of_times_cont_diff hγ_diff times_cont_diff_const 0

lemma times_cont_diff_sub_average {n : with_top ℕ} (hγ_diff : 𝒞 n ↿γ) :
  𝒞 n ↿(λ (x : E) (t : ℝ), (γ x) t - (γ x).average) :=
hγ_diff.sub ((times_cont_diff_average hγ_diff).comp times_cont_diff_fst)

variable {π}

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
    from loop.compact_support_diff hγ_diff hγ,
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
  ∀ᶠ N in at_top, ∀ x, ∀ w ∈ ker (D π x : E →ₗ[ℝ] ℝ),
  ∥D (𝒯 N γ) x w∥ ≤ ε*∥w∥ :=
begin
  apply (corrugation.fderiv hπ hγ_diff hγ_supp ε_pos).mono,
  intros N hN x w hw,
  let φ := D (corrugation π N γ) x - (γ x (N * π x) - (γ x).average) ⬝ D π x,
  rw mem_ker at hw,
  change D π x w = 0 at hw,
  have : D (corrugation π N γ) x w = φ w,
  { simp only [φ, hw, continuous_linear_map.coe_comp', continuous_linear_map.coe_sub', sub_zero, 
               comp_app, pi.sub_apply, continuous_linear_map.map_zero] },
  rw this,
  exact φ.le_of_op_norm_le (hN x).le w
end
 

open continuous_linear_map

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
