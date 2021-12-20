import analysis.asymptotics.asymptotics
import linear_algebra.dual
import measure_theory.integral.interval_integral
import analysis.calculus.parametric_integral
import algebra.periodic

import parametric_interval_integral
import loops.basic

noncomputable theory

/-

TODO generalize many lemmas to any period and add to algebra/periodic.lean

-/

open int

section interval_integral

open topological_space (second_countable_topology)
open measure_theory set classical filter

open_locale classical topological_space filter

variables {α β E F : Type*} [measurable_space α] {μ : measure α} [normed_group E]
          [second_countable_topology E] [complete_space E] [normed_space ℝ E] [measurable_space E] [borel_space E]

namespace measure_theory
lemma ae_restrict_eq_iff {s : set α} {f g : α → β} (h : measurable_set {x | f x = g x}) :
  f =ᵐ[μ.restrict s] g ↔ ∀ᵐ x ∂μ, x ∈ s → f x = g x :=
ae_restrict_iff h

end measure_theory

end interval_integral

local notation `D` := fderiv ℝ

open set function finite_dimensional asymptotics filter topological_space
open_locale topological_space

section topological_support

variables {X α : Type*} [has_zero α]

lemma support_empty_iff {f : X → α} : support f = ∅ ↔ ∀ x, f x = 0 :=
by simp_rw [← nmem_support, eq_empty_iff_forall_not_mem]

variables [topological_space X]

/-- The topological support of a function, is the closure of its support. -/
def tsupport (f : X → α) : set X := closure (support f)

lemma support_subset_tsupport (f : X → α) : support f ⊆ tsupport f :=
subset_closure

lemma tsupport_empty_iff {f : X → α} : tsupport f = ∅ ↔ ∀ x, f x = 0 :=
by erw [closure_empty_iff, support_empty_iff]

lemma image_eq_zero_of_nmem_tsupport {f : X → α} {x : X} (hx : x ∉ tsupport f) : f x = 0 :=
support_subset_iff'.mp (support_subset_tsupport f) x hx

variables {E : Type*} [normed_group E]

lemma continuous.bounded_of_vanishing_outside_compact {f : X → E} (hf : continuous f)
  {K : set X} (hK : is_compact K) (hfK : ∀ x ∉ K, f x = 0) : ∃ C, ∀ x, ∥f x∥ ≤ C :=
begin
  rcases eq_empty_or_nonempty K with h|h,
  { use 0,
    simp [h, hfK, le_refl] },
  { obtain ⟨x, x_in, hx⟩ : ∃ x ∈ K, ∀ y ∈ K, ∥f y∥ ≤ ∥f x∥ :=
      hK.exists_forall_ge h (continuous_norm.comp hf).continuous_on,
    use ∥f x∥,
    intros y,
    by_cases hy : y ∈ K,
    { exact hx y hy },
    { simp [hfK y hy] } }
end

lemma continuous.bounded_of_compact_support {f : X → E} (hf : continuous f)
  (hsupp : is_compact (tsupport f)) : ∃ C, ∀ x, ∥f x∥ ≤ C :=
hf.bounded_of_vanishing_outside_compact hsupp (λ x, image_eq_zero_of_nmem_tsupport)

end topological_support

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

lemma support_aux {γ : loop F} (h : γ = loop.const (γ.average)) (b : ℝ) :
  ∫ t in 0..b, γ t - γ.average = 0  :=
begin
  rw h,
  simp -- Note: one cannot use `simp [h]` because `γ` appears on both side.
end

lemma corrugation.support (hγ : ∀ x, continuous (γ x)) :
  support (corrugation π N γ) ⊆ loop.support γ :=
begin
  intros x x_in,
  apply subset_closure,
  intro h,
  apply x_in,
  simp only [corrugation, one_div, inv_eq_zero, smul_eq_zero],
  right,
  rw interval_integral.integral_zero_ae,
  apply eventually_of_forall,
  intros t t_in,
  conv_lhs { congr, rw h },
  simp
end

lemma continuous_average [first_countable_topology E] [locally_compact_space E]
  (hγ_cont : continuous ↿γ) : continuous (λ x, (γ x).average) :=
continuous_parametric_interval_integral_of_continuous' hγ_cont _ _

/-- If a loop family has compact support then the corresponding corrugation is
`O(1/N)` uniformly in the source point. -/
lemma corrugation.c0_small [first_countable_topology E]
  [locally_compact_space E] (hγ : is_compact (loop.support γ))
  (hγ_cont : continuous ↿γ) :
  ∃ C, ∀ x, is_O_with C (λ N, corrugation π N γ x) (λ N, 1/N) at_top :=
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
  use C,
  intro x,
  apply is_O_with_of_le',
  intro N,
  rw [corrugation, norm_smul, mul_comm],
  exact mul_le_mul_of_nonneg_right (hC x (N*π x)) (norm_nonneg _)
end

end c0

section c1

variables {E : Type*} [normed_group E] [normed_space ℝ E] [finite_dimensional ℝ E]
          {F : Type*} [normed_group F] [normed_space ℝ F] [measurable_space F] [borel_space F]
          [finite_dimensional ℝ F]


variables (π : E → ℝ) (N : ℝ) (γ : E → loop F)
          (hγ : is_compact (loop.support γ))

open linear_map

local notation `∂₁` := partial_fderiv_fst ℝ
local notation `𝒞` := times_cont_diff ℝ

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

lemma times_cont_diff.partial_loop {γ : E → loop F} (e : E) (hγ_diff : 𝒞 1 ↿γ) :
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
  rw [fderiv_sub ((hγ_diff.partial_loop e t).differentiable le_rfl).differentiable_at,
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
    change γ z t = (γ z).average,
    rw show γ z = _, from hU hz,
    simp only [loop.const_apply, loop.average_const] },
  have : ∀ (t : ℝ), loop.diff γ y t = D (λ (z : E), (γ z).average) y := λ t, (Hy t).fderiv_eq,
  ext t z,
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

variable {γ}

lemma times_cont_diff_average {n : with_top ℕ} (hγ_diff : 𝒞 n ↿γ) : 𝒞 n (λ x, (γ x).average) :=
times_cont_diff_parametric_primitive_of_times_cont_diff hγ_diff times_cont_diff_const 0

lemma times_cont_diff_sub_average {n : with_top ℕ} (hγ_diff : 𝒞 n ↿γ) :
  𝒞 n ↿(λ (x : E) (t : ℝ), (γ x) t - (γ x).average) :=
hγ_diff.sub ((times_cont_diff_average hγ_diff).comp times_cont_diff_fst)

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
  (hγ_cont : 𝒞 1 ↿γ) :
  ∃ C, ∀ x, is_O_with C (λ N, R N γ x) (λ N, 1/N) at_top :=
begin
  have : is_compact (loop.support $ loop.diff γ),
    from loop.compact_support_diff hγ_cont hγ,
  rcases corrugation.c0_small π this (loop.continuous_diff hγ_cont) with ⟨C, hC⟩,
  use C,
  intro e,
  rw remainder_eq' π e hγ_cont,
  exact hC e
end

lemma corrugation.fderiv (hγ_diff : 𝒞 1 ↿γ) :
  ∃ C, ∀ x, ∀ v, is_O_with C
  (λ N, D (𝒯 N γ) x v - (D π x v) • (γ x (N*π v) - (γ x).average)) (λ N, ∥v∥/N) at_top :=
  sorry

lemma corrugation.fderiv_ker (hγ_diff : 𝒞 1 ↿γ) :
  ∃ C, ∀ x, ∀ w ∈ ker (D π x : E →ₗ[ℝ] ℝ),
  is_O_with C (λ N, D (𝒯 N γ) x w) (λ N, ∥w∥/N) at_top :=
sorry

lemma corrugation.fderiv_u (hγ_diff : 𝒞 1 ↿γ) {u : E} (hu : ∀ x, fderiv ℝ π x u = 1) :
  ∃ C, ∀ x, is_O_with C
  (λ N, D (𝒯 N γ) x u - (γ x (N*π u) - (γ x).average)) (λ N, ∥u∥/N) at_top :=
sorry

end c1

open module (dual)

variables (E : Type*) [normed_group E] [normed_space ℝ E]

-- TODO: move mathlib's dual_pair out of the root namespace!

structure dual_pair'
(π : dual ℝ E)
(v : E)
(pairing : π v = 1)
