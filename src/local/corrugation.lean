import analysis.asymptotics
import linear_algebra.dual

import parametric_integral
import loops.basic

noncomputable theory

section interval_integral

open topological_space (second_countable_topology)
open measure_theory set classical filter

open_locale classical topological_space filter

variables {α β E F : Type*} [measurable_space α] {μ : measure α} [normed_group E]
          [second_countable_topology E] [complete_space E] [normed_space ℝ E] [measurable_space E] [borel_space E]

namespace measure_theory
lemma ae_restrict_eq_iff {s : set α} {f g : α → β} (h : is_measurable {x | f x = g x}) :
  f =ᵐ[μ.restrict s] g ↔ ∀ᵐ x ∂μ, x ∈ s → f x = g x :=
ae_restrict_iff h

lemma set_integral_eq_zero_of_ae {s : set α} {f : α → E} (hf : measurable f) 
  (h : ∀ᵐ x ∂μ, x ∈ s → f x = 0) : ∫ x in s, f x ∂ μ = 0 :=
begin
  rw measure_theory.integral_eq_zero_of_ae, 
  rw ae_restrict_eq_iff,
  { simpa using h },
  exact hf (is_measurable_singleton (0 : E))
end

variables  [decidable_linear_order α] 

lemma interval_integral_eq_zero_of_ae {a b : α} {f : α → E} (hf : measurable f) 
  (h : ∀ᵐ x ∂μ, x ∈ Ioc a b → f x = 0) (h' : ∀ᵐ x ∂μ, x ∈ Ioc b a → f x = 0) :
∫ x in a..b, f x ∂ μ = 0 :=
begin
  unfold interval_integral,
  rw [measure_theory.set_integral_eq_zero_of_ae hf, measure_theory.set_integral_eq_zero_of_ae hf, sub_zero];
  assumption
end

-- This lemma is silly, `hf` shouldn't be needed
lemma interval_integral_eq_zero_of_zero {a b : α} {f : α → E} (hf : measurable f) 
  (h : ∀ x ∈ Ioc a b, f x = 0) (h' : ∀ x ∈ Ioc b a, f x = 0) :
∫ x in a..b, f x ∂ μ = 0 :=
begin
  apply interval_integral_eq_zero_of_ae hf;
  { apply ae_of_all, assumption }
end

end measure_theory

end interval_integral

local notation `D` := fderiv ℝ

open set function finite_dimensional asymptotics filter
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

def one_periodic (f : ℝ → α) : Prop := ∀ x, f (x + 1) = f x

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
@[derive topological_space]
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
quotient_add_group.open_coe ℤ_sub_ℝ

lemma quotient_map_id_proj_𝕊₁ {X : Type*} [topological_space X] :
  quotient_map (λ p : X × ℝ, (p.1, proj_𝕊₁ p.2)) :=
(is_open_map.id.prod is_open_map_proj_𝕊₁).to_quotient_map (continuous_id.prod_map continuous_proj_𝕊₁)
  (surjective_id.prod_map quotient.exists_rep)


def one_periodic.lift {f : ℝ → α} (h : one_periodic f) : 𝕊₁ → α :=
quotient.lift f (by { intros a b hab, rcases trans_one_rel_iff.mp hab with ⟨k, rfl⟩, rw h.add_int })

end

local notation `π` := proj_𝕊₁

instance : compact_space 𝕊₁ :=
⟨by { rw ← image_proj_𝕊₁_Icc,exact compact_Icc.image continuous_proj_𝕊₁ }⟩

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


variables {E : Type*}
          {F : Type*} [normed_group F] [normed_space ℝ F] [measurable_space F] [borel_space F]
          [finite_dimensional ℝ F]

/-- Theillière's corrugations. -/
def corrugation (π : E → ℝ) (N : ℝ) (γ : E → loop F) : E → F :=
λ x, (1/N) • ∫ t in 0..(N*π x), (γ x t - (γ x).average)

def corrugate (f : E → F) (π : E → ℝ) (N : ℝ) (γ : E → loop F) : E → F :=
λ x, f x + (1/N) • ∫ t in 0..(N*π x), (γ x t - (γ x).average)

lemma per_corrugation (γ : loop F) : one_periodic (λ s, ∫ t in 0..s, γ t - γ.average) :=
begin
  
  sorry
end

variables (π : E → ℝ) (N : ℝ) (γ : E → loop F) [topological_space E] 

lemma support_aux {γ : loop F} (h : γ = const_loop (γ.average)) (b : ℝ) :
  ∫ t in 0..b, γ t - γ.average = 0  :=
begin
  
  sorry
end

lemma corrugation.support (hγ : ∀ x, continuous (γ x)) :
  support (corrugation π N γ) ⊆ loop.support γ :=
begin
  intros x x_in,
  apply subset_closure,
  intro h,
  apply x_in,
  simp [corrugation],
  rw [measure_theory.interval_integral_eq_zero_of_zero ((hγ x).sub continuous_const).measurable, smul_zero],
  all_goals { intros t t_in,
    change γ x t - (γ x).average = 0,
    conv_lhs { congr, rw h },
    simp }
end

/-- If a loop family has compact support then the corresponding corrugation is
`O(1/N)` uniformly in the source point. -/
lemma corrugation.c0_small [topological_space E] (hγ : is_compact (loop.support γ)) 
  (hγ_cont : continuous ↿γ) : 
  ∃ C, ∀ x, is_O_with C (λ N, corrugation π N γ x) (λ N, 1/N) at_top :=
begin
  obtain ⟨C, hC⟩ : ∃ C, ∀ x b, ∥∫ t in 0..b, (γ x t - (γ x).average)∥ ≤ C,
  { apply continuous.bounded_of_one_periodic_of_compact _ _ hγ, 
    { intros x hx,
      ext t,
      exact support_aux (loop.const_of_not_mem_support hx) t },
    { change continuous ↿(λ (x : E) (t : ℝ), ∫ s in 0..t, (γ x) s - (γ x).average),
      sorry },
    { intro x,
      apply per_corrugation } }, 
  use C,
  intro x, -- TODO: learn is_O API better to get nicer proof below
  rw is_O_with_iff,
  apply eventually_of_forall,
  intro N,
  rw [corrugation, norm_smul, mul_comm],
  specialize hC x (N*π x),
  exact mul_le_mul hC (le_refl _) (norm_nonneg _) (le_trans (norm_nonneg _) hC),
end

variables [normed_group E] [normed_space ℝ E]
          (hγ : is_compact (loop.support γ)) (hγ_diff : times_cont_diff ℝ 1 ↿γ)

open linear_map

lemma corrugation.fderiv  :
  ∃ C, ∀ x, ∀ v, is_O_with C
  (λ N, D (corrugation π N γ) x v - (D π x v) • (γ x (N*π v) - (γ x).average)) (λ N, ∥v∥/N) at_top :=
sorry

lemma corrugation.fderiv_ker :
  ∃ C, ∀ x, ∀ w ∈ ker (D π x : E →ₗ[ℝ] ℝ),
  is_O_with C (λ N, D (corrugation π N γ) x w) (λ N, ∥w∥/N) at_top :=
sorry

lemma corrugation.fderiv_u {u : E} (hu : ∀ x, fderiv ℝ π x u = 1) :
  ∃ C, ∀ x, is_O_with C
  (λ N, D (corrugation π N γ) x u - (γ x (N*π u) - (γ x).average)) (λ N, ∥u∥/N) at_top :=
sorry

open module (dual)

variables (E)

-- TODO: move mathlib's dual_pair out of the root namespace!

structure dual_pair'
(π : dual ℝ E)
(v : E)
(pairing : π v = 1)