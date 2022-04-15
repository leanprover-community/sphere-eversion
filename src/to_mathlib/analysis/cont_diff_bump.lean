import analysis.calculus.specific_functions
import measure_theory.function.locally_integrable
import measure_theory.integral.interval_integral
import to_mathlib.topology.misc

noncomputable theory
open metric measure_theory function topological_space set filter
open_locale topological_space

-- move to topology.algebra.order.basic
lemma continuous_at.eventually_lt {X Y : Type*} [topological_space X] [topological_space Y]
  [linear_order Y] [order_closed_topology Y] [densely_ordered Y]
  {f g : X → Y} {x₀ : X} (hf : continuous_at f x₀) (hg : continuous_at g x₀) (hfg : f x₀ < g x₀) :
  ∀ᶠ x in 𝓝 x₀, f x < g x :=
begin
  obtain ⟨z, hfz, hzg⟩ := exists_between hfg,
  filter_upwards [hf.preimage_mem_nhds (Iio_mem_nhds hfz), hg.preimage_mem_nhds (Ioi_mem_nhds hzg)],
  exact λ x, lt_trans
end

lemma measure_theory.integrable.div_const {α : Type*} [measurable_space α] {μ : measure α}
  {f : α → ℝ} (h : integrable f μ) (c : ℝ) : integrable (λ x, f x / c) μ :=
by simp_rw [div_eq_mul_inv, h.mul_const]

namespace cont_diff_bump_of_inner

variables {𝕜 X E : Type*} [inner_product_space ℝ E]
variables [normed_group X] [normed_space ℝ X]
variables {c : E} {n : with_top ℕ}
variables (f : cont_diff_bump_of_inner c)

lemma nonneg' (x : E) : 0 ≤ f x := nonneg _

protected lemma continuous : continuous f :=
cont_diff_zero.mp f.cont_diff

lemma tsupport_eq : tsupport f = closed_ball c f.R :=
by simp_rw [tsupport, f.support_eq, closure_ball _ f.R_pos.ne']

protected lemma has_compact_support [finite_dimensional ℝ E] :
  has_compact_support f :=
by simp_rw [has_compact_support, f.tsupport_eq, is_compact_closed_ball]

protected lemma _root_.cont_diff_at.cont_diff_bump {c g : X → E}
  {f : ∀ x, cont_diff_bump_of_inner (c x)} {x : X}
  (hc : cont_diff_at ℝ n c x) (hr : cont_diff_at ℝ n (λ x, (f x).r) x)
  (hR : cont_diff_at ℝ n (λ x, (f x).R) x)
  (hg : cont_diff_at ℝ n g x) : cont_diff_at ℝ n (λ x, f x (g x)) x :=
begin
  rcases eq_or_ne (g x) (c x) with hx|hx,
  { have : (λ x, f x (g x)) =ᶠ[𝓝 x] (λ x, 1),
    { have : dist (g x) (c x) < (f x).r, { simp_rw [hx, dist_self, (f x).r_pos] },
      have := continuous_at.eventually_lt (hg.continuous_at.dist hc.continuous_at) hr.continuous_at
        this,
      exact eventually_of_mem this
        (λ x hx, (f x).one_of_mem_closed_ball (mem_set_of_eq.mp hx).le) },
    exact cont_diff_at_const.congr_of_eventually_eq this },
  { refine real.smooth_transition.cont_diff_at.comp x _,
    refine ((hR.sub $ hg.dist hc hx).div (hR.sub hr) (sub_pos.mpr (f x).r_lt_R).ne') }
end

lemma _root_.cont_diff.cont_diff_bump {c g : X → E} {f : ∀ x, cont_diff_bump_of_inner (c x)}
  (hc : cont_diff ℝ n c) (hr : cont_diff ℝ n (λ x, (f x).r)) (hR : cont_diff ℝ n (λ x, (f x).R))
  (hg : cont_diff ℝ n g) : cont_diff ℝ n (λ x, f x (g x)) :=
by { rw [cont_diff_iff_cont_diff_at] at *, exact λ x, (hc x).cont_diff_bump (hr x) (hR x) (hg x) }

protected lemma «def» (x : E) : f x = real.smooth_transition ((f.R - dist x c) / (f.R - f.r)) :=
rfl

protected lemma sub (x : E) : f (c - x) = f (c + x) :=
by simp_rw [f.def, dist_self_sub_left, dist_self_add_left]

protected lemma neg (f : cont_diff_bump_of_inner (0 : E)) (x : E) : f (- x) = f x :=
by simp_rw [← zero_sub, f.sub, zero_add]


variables [measurable_space E] {μ : measure E}

/-- A bump function normed so that `∫ x, f.normed μ x ∂μ = 1`. -/
protected def normed (μ : measure E) : E → ℝ :=
λ x, f x / ∫ x, f x ∂μ

lemma normed_def {μ : measure E} (x : E) : f.normed μ x = f x / ∫ x, f x ∂μ :=
rfl

lemma nonneg_normed (x : E) : 0 ≤ f.normed μ x :=
div_nonneg f.nonneg $ integral_nonneg f.nonneg'

lemma cont_diff_normed {n : with_top ℕ} : cont_diff ℝ n (f.normed μ) :=
f.cont_diff.div_const

lemma continuous_normed : continuous (f.normed μ) :=
f.continuous.div_const

lemma normed_sub (x : E) : f.normed μ (c - x) = f.normed μ (c + x) :=
by simp_rw [f.normed_def, f.sub]

lemma normed_neg (f : cont_diff_bump_of_inner (0 : E)) (x : E) : f.normed μ (- x) = f.normed μ x :=
by simp_rw [f.normed_def, f.neg]

variables [borel_space E] [finite_dimensional ℝ E] [is_locally_finite_measure μ]

protected lemma integrable : integrable f μ :=
f.continuous.integrable_of_has_compact_support f.has_compact_support

protected lemma integrable_normed : integrable (f.normed μ) μ :=
f.integrable.div_const _

variables [μ .is_open_pos_measure]

lemma integral_pos : 0 < ∫ x, f x ∂μ :=
begin
  refine (integral_pos_iff_support_of_nonneg f.nonneg' f.integrable).mpr _,
  rw [f.support_eq],
  refine is_open_ball.measure_pos _ (nonempty_ball.mpr f.R_pos)
end

lemma integral_normed : ∫ x, f.normed μ x ∂μ = 1 :=
begin
  simp_rw [cont_diff_bump_of_inner.normed, div_eq_mul_inv, mul_comm (f _), ← smul_eq_mul,
    integral_smul],
  exact inv_mul_cancel (f.integral_pos.ne')
end

lemma support_normed_eq : support (f.normed μ) = metric.ball c f.R :=
by simp_rw [cont_diff_bump_of_inner.normed, support_div, f.support_eq,
  support_const f.integral_pos.ne', inter_univ]

lemma tsupport_normed_eq : tsupport (f.normed μ) = metric.closed_ball c f.R :=
by simp_rw [tsupport, f.support_normed_eq, closure_ball _ f.R_pos.ne']

lemma has_compact_support_normed : has_compact_support (f.normed μ) :=
by simp_rw [has_compact_support, f.tsupport_normed_eq, is_compact_closed_ball]

variable (μ)
lemma integral_normed_smul (z : X) [complete_space X] :
  ∫ x, f.normed μ x • z ∂μ = z :=
by simp_rw [integral_smul_const, f.integral_normed, one_smul]
variable {μ}

end cont_diff_bump_of_inner
