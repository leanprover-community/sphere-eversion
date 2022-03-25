import analysis.calculus.specific_functions
import measure_theory.function.locally_integrable
import measure_theory.integral.interval_integral

noncomputable theory
open metric measure_theory function topological_space set filter
open_locale topological_space

section graph_nhd

variables {X Y : Type*} [metric_space Y] {c : X → Y} {ε : X → ℝ}

/-- is this useful? (currently unused) -/
def graph_nhd (c : X → Y) (ε : X → ℝ) : set (X × Y) :=
{x : X × Y | dist (c x.1) x.2 < ε x.1 }

variables [topological_space X]
lemma is_open_graph_nhd (hc : continuous c) (hε : continuous ε) : is_open (graph_nhd c ε) :=
sorry

end graph_nhd

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

namespace cont_diff_bump_of_inner

variables {𝕜 X G E : Type*} [inner_product_space ℝ G]
variables [normed_group E] [normed_space ℝ E]
variables [normed_group X] [normed_space ℝ X]
variables [measurable_space E] [borel_space E] [complete_space E] [second_countable_topology E]
variables {a : G} {n : with_top ℕ}
-- variables [nondiscrete_normed_field 𝕜] [normed_group X] [normed_space 𝕜 E]

/-- A version with `x` explicit -/
lemma nonneg' (φ : cont_diff_bump_of_inner a) (x : G) : 0 ≤ φ x :=
φ.nonneg

protected lemma continuous (φ : cont_diff_bump_of_inner a) : continuous φ :=
cont_diff_zero.mp φ.cont_diff

lemma tsupport_eq (φ : cont_diff_bump_of_inner a) : tsupport φ = closed_ball a φ.R :=
by simp_rw [tsupport, φ.support_eq, closure_ball _ φ.R_pos.ne']

protected lemma has_compact_support [finite_dimensional ℝ G] (φ : cont_diff_bump_of_inner a) :
  has_compact_support φ :=
by simp_rw [has_compact_support, φ.tsupport_eq, is_compact_closed_ball]

protected lemma _root_.cont_diff_at.cont_diff_bump {c g : X → G}
  {φ : ∀ x, cont_diff_bump_of_inner (c x)} {x : X}
  (hc : cont_diff_at ℝ n c x) (hr : cont_diff_at ℝ n (λ x, (φ x).r) x)
  (hR : cont_diff_at ℝ n (λ x, (φ x).R) x)
  (hg : cont_diff_at ℝ n g x) : cont_diff_at ℝ n (λ x, φ x (g x)) x :=
begin
  rcases eq_or_ne (g x) (c x) with hx|hx,
  { have : (λ x, φ x (g x)) =ᶠ[𝓝 x] (λ x, 1),
    { have : dist (g x) (c x) < (φ x).r, { simp_rw [hx, dist_self, (φ x).r_pos] },
      have := continuous_at.eventually_lt (hg.continuous_at.dist hc.continuous_at) hr.continuous_at
        this,
      exact eventually_of_mem this
        (λ x hx, (φ x).one_of_mem_closed_ball (mem_set_of_eq.mp hx).le) },
    exact cont_diff_at_const.congr_of_eventually_eq this },
  { refine real.smooth_transition.cont_diff_at.comp x _,
    refine ((hR.sub $ hg.dist hc hx).div (hR.sub hr) (sub_pos.mpr (φ x).r_lt_R).ne') }
end

lemma _root_.cont_diff.cont_diff_bump {c g : X → G} {φ : ∀ x, cont_diff_bump_of_inner (c x)}
  (hc : cont_diff ℝ n c) (hr : cont_diff ℝ n (λ x, (φ x).r)) (hR : cont_diff ℝ n (λ x, (φ x).R))
  (hg : cont_diff ℝ n g) : cont_diff ℝ n (λ x, φ x (g x)) :=
by { rw [cont_diff_iff_cont_diff_at] at *, exact λ x, (hc x).cont_diff_bump (hr x) (hR x) (hg x) }


variables [measurable_space G] {μ : measure G}

/-- A bump function normed so that `∫ x, φ.normed μ x ∂μ = 1`. -/
protected def normed (φ : cont_diff_bump_of_inner a) (μ : measure G) : G → ℝ :=
λ x, φ x / ∫ x, φ x ∂μ

lemma nonneg_normed (φ : cont_diff_bump_of_inner a) (x : G) : 0 ≤ φ.normed μ x :=
div_nonneg φ.nonneg $ integral_nonneg φ.nonneg'

variables [borel_space G] [finite_dimensional ℝ G] [is_locally_finite_measure μ]

protected lemma integrable (φ : cont_diff_bump_of_inner a) : integrable φ μ :=
φ.continuous.integrable_of_has_compact_support φ.has_compact_support

variables [μ .is_open_pos_measure]

lemma integral_pos (φ : cont_diff_bump_of_inner a) : 0 < ∫ x, φ x ∂μ :=
begin
  refine (integral_pos_iff_support_of_nonneg φ.nonneg' φ.integrable).mpr _,
  rw [φ.support_eq],
  refine is_open_ball.measure_pos _ (nonempty_ball.mpr φ.R_pos)
end

lemma integral_normed (φ : cont_diff_bump_of_inner a) :
  ∫ x, φ.normed μ x ∂μ = 1 :=
begin
  simp_rw [cont_diff_bump_of_inner.normed, div_eq_mul_inv, mul_comm (φ _), ← smul_eq_mul,
    integral_smul],
  exact inv_mul_cancel (φ.integral_pos.ne')
end

lemma support_normed_eq (φ : cont_diff_bump_of_inner a) :
  support (φ.normed μ) = metric.ball a φ.R :=
by simp_rw [cont_diff_bump_of_inner.normed, support_div, φ.support_eq,
  support_const φ.integral_pos.ne', inter_univ]

lemma tsupport_normed_eq (φ : cont_diff_bump_of_inner a) :
  tsupport (φ.normed μ) = metric.closed_ball a φ.R :=
by simp_rw [tsupport, φ.support_normed_eq, closure_ball _ φ.R_pos.ne']

lemma has_compact_support_normed (φ : cont_diff_bump_of_inner a) :
  has_compact_support (φ.normed μ) :=
by simp_rw [has_compact_support, φ.tsupport_normed_eq, is_compact_closed_ball]

variable (μ)
lemma integral_normed_smul (φ : cont_diff_bump_of_inner a) (c : E) :
  ∫ x, φ.normed μ x • c ∂μ = c :=
by simp_rw [integral_smul_const, φ.integral_normed, one_smul]
variable {μ}

end cont_diff_bump_of_inner
