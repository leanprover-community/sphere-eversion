import analysis.calculus.specific_functions
import topology.metric_space.hausdorff_distance

import to_mathlib.topology.misc
import to_mathlib.topology.nhds_set
import to_mathlib.topology.hausdorff_distance
import to_mathlib.linear_algebra.basic

import notations

/-! # Spaces of 1-jets and their sections

For real normed spaces `E` and `F`, this file defines the space `one_jet_sec E F` of 1-jets
of maps from `E` to `F` as `E × F × (E →L[ℝ] F)`.

A section `𝓕 : jet_sec E F` of this space is a map `(𝓕.f, 𝓕.φ) : E → F × (E →L[ℝ] F)`.

It is holonomic at `x`, spelled `𝓕.is_holonomic_at x` if the differential of `𝓕.f` at `x`
is `𝓕.φ x`.

We then introduced parametrized families of sections, and especially homotopies of sections,
with type `htpy_jet_sec E F` and their concatenation operation `htpy_jet_sec.comp`.


Implementation note: the time parameter `t` for homotopies is any real number, but all the
homotopies we will construct will be constant for `t ≤ 0` and `t ≥ 1`. It looks like this imposes
more smoothness constraints at `t = 0` and `t = 1` (requiring flat functions), but this is needed
for smooth concatenations anyway.
 -/

noncomputable theory

open set function real filter
open_locale unit_interval topological_space

variables (E : Type*) [normed_add_comm_group E] [normed_space ℝ E]
variables (F : Type*) [normed_add_comm_group F] [normed_space ℝ F]
variables (P : Type*) [normed_add_comm_group P] [normed_space ℝ P]

/-! ## Spaces of 1-jets -/

/-- The space of 1-jets of maps from `E` to `F`. -/
@[derive metric_space]
def one_jet := E × F × (E →L[ℝ] F)

/-- A smooth section of J¹(E, F) → E. -/
@[ext] structure jet_sec :=
(f : E → F)
(f_diff : 𝒞 ∞ f)
(φ : E → E →L[ℝ] F)
(φ_diff : 𝒞 ∞ φ)

namespace jet_sec

variables {E F}

instance : has_coe_to_fun (jet_sec E F) (λ S, E → F × (E →L[ℝ] F)) :=
⟨λ 𝓕, λ x, (𝓕.f x, 𝓕.φ x)⟩

lemma coe_apply (𝓕 : jet_sec E F) (x : E) : 𝓕 x = (𝓕.f x, 𝓕.φ x) := rfl

lemma eq_iff {𝓕 𝓕' : jet_sec E F} {x : E} :
  𝓕 x = 𝓕' x ↔ 𝓕.f x = 𝓕'.f x ∧ 𝓕.φ x = 𝓕'.φ x :=
begin
  split,
  { intro h,
    exact ⟨congr_arg prod.fst h, congr_arg prod.snd h⟩ },
  { rintros ⟨h, h'⟩,
    ext1,
    exacts [h, h'] }
end

lemma ext' {𝓕 𝓕' : jet_sec E F} (h : ∀ x, 𝓕 x = 𝓕' x) : 𝓕 = 𝓕' :=
begin
  ext : 2,
  { exact congr_arg prod.fst (h x) },
  { ext1 x, exact congr_arg prod.snd (h x) },
end

/-! ## Holonomic sections-/

/-- A jet section `𝓕` is holonomic if its linear map part at `x`
is the derivative of its function part at `x`. -/
def is_holonomic_at (𝓕 : jet_sec E F) (x : E) : Prop := D 𝓕.f x = 𝓕.φ x

lemma is_holonomic_at.congr {𝓕 𝓕' : jet_sec E F} {x} (h : is_holonomic_at 𝓕 x)
  (h' : 𝓕 =ᶠ[𝓝 x] 𝓕') : is_holonomic_at 𝓕' x :=
begin
  have h'' : 𝓕.f =ᶠ[𝓝 x] 𝓕'.f,
  { apply h'.mono,
    dsimp only,
    simp_rw eq_iff,
    tauto },
  unfold jet_sec.is_holonomic_at,
  rwa [h''.symm.fderiv_eq, ← (eq_iff.mp h'.self_of_nhds).2]
end

/-- A formal solution `𝓕` of `R` is partially holonomic in the direction of some subspace `E'`
if its linear map part at `x` is the derivative of its function part at `x` in restriction to
`E'`. -/
def is_part_holonomic_at (𝓕 : jet_sec E F) (E' : submodule ℝ E) (x : E) :=
∀ v ∈ E', D 𝓕.f x v = 𝓕.φ x v

lemma _root_.filter.eventually.is_part_holonomic_at_congr {𝓕 𝓕' : jet_sec E F} {s : set E}
  (h : ∀ᶠ x near s, 𝓕 x = 𝓕' x) (E' : submodule ℝ E) :
  ∀ᶠ x near s, 𝓕.is_part_holonomic_at E' x ↔ 𝓕'.is_part_holonomic_at E' x :=
begin
  apply h.eventually_nhds_set.mono,
  intros x hx,
  have hf : 𝓕.f =ᶠ[𝓝 x] 𝓕'.f,
  { apply hx.mono,
    dsimp only,
    simp_rw eq_iff,
    tauto },
  unfold jet_sec.is_part_holonomic_at,
  rw [hf.fderiv_eq, (eq_iff.mp hx.self_of_nhds).2]
end

lemma is_part_holonomic_at.sup (𝓕 : jet_sec E F) {E' E'' : submodule ℝ E} {x : E}
  (h' : 𝓕.is_part_holonomic_at E' x) (h'' : 𝓕.is_part_holonomic_at E'' x) :
  𝓕.is_part_holonomic_at (E' ⊔ E'') x :=
λ v : E, linear_map.eq_on_sup h' h''

lemma is_part_holonomic_at.mono {𝓕 : jet_sec E F}
  {E' E'' : submodule ℝ E} {x : E} (h : 𝓕.is_part_holonomic_at E' x) (h' : E'' ≤ E') :
  𝓕.is_part_holonomic_at E'' x :=
λ v v_in, h v $ set_like.coe_subset_coe.mpr h' v_in

lemma is_part_holonomic_top {𝓕 : jet_sec E F} {x : E} :
  is_part_holonomic_at 𝓕 ⊤ x ↔ is_holonomic_at 𝓕 x :=
begin
  simp only [is_part_holonomic_at, submodule.mem_top, forall_true_left, is_holonomic_at],
  rw [← funext_iff, continuous_linear_map.coe_fn_injective.eq_iff]
end

@[simp] lemma is_part_holonomic_bot (𝓕 : jet_sec E F) :
  is_part_holonomic_at 𝓕 ⊥ = λ x, true :=
begin
  ext x,
  simp only [is_part_holonomic_at, submodule.mem_bot, forall_eq, map_zero, eq_self_iff_true]
end

end jet_sec

/-! ## Homotopies of sections -/

section htpy_jet_sec

/-- A parametrized family of sections of J¹(E, F). -/
structure family_jet_sec :=
(f : P → E → F)
(f_diff : 𝒞 ∞ ↿f)
(φ : P → E → E →L[ℝ] F)
(φ_diff : 𝒞 ∞ ↿φ)


/-- A homotopy of sections of J¹(E, F). -/
@[reducible] def htpy_jet_sec := family_jet_sec E F ℝ

variables  {E F P}

instance : has_coe_to_fun (family_jet_sec E F P) (λ S, P → jet_sec E F) :=
⟨λ S t,
 { f := S.f t,
   f_diff := S.f_diff.comp (cont_diff_const.prod cont_diff_id),
   φ := S.φ t,
   φ_diff := S.φ_diff.comp (cont_diff_const.prod cont_diff_id) }⟩

namespace family_jet_sec

lemma cont_diff_f (𝓕 : family_jet_sec E F P) {n : ℕ∞} : 𝒞 n ↿𝓕.f :=
𝓕.f_diff.of_le le_top

lemma cont_diff_φ (𝓕 : family_jet_sec E F P) {n : ℕ∞} : 𝒞 n ↿𝓕.φ :=
𝓕.φ_diff.of_le le_top

end family_jet_sec

/-- The constant homotopy of formal solutions at a given formal solution. It will be used
as junk value for constructions of formal homotopies that need additional assumptions and also
for trivial induction initialization. -/
def jet_sec.const_htpy (𝓕 : jet_sec E F) : htpy_jet_sec E F :=
{ f := λ t, 𝓕.f,
  f_diff := 𝓕.f_diff.snd',
  φ := λ t, 𝓕.φ,
  φ_diff := 𝓕.φ_diff.snd' }

@[simp] lemma jet_sec.const_htpy_apply (𝓕 : jet_sec E F) :
  ∀ t, 𝓕.const_htpy t = 𝓕 :=
λ t, by ext x ; refl

/-! ## Concatenation of homotopies of sections

In this part of the file we build a concatenation operation for homotopies of 1-jet sections.
We first need to introduce a smooth step function on `ℝ`. There is already a version
of this in mathlib called `smooth_transition` but that version is not locally constant
near `0` and `1`, which is not convenient enough for gluing purposes.
-/

/-- A smooth step function on `ℝ`. -/
def smooth_step : ℝ → ℝ := λ t, smooth_transition (2 * t - 1/2)

lemma smooth_step.smooth : 𝒞 ∞ smooth_step :=
smooth_transition.cont_diff.comp $ (cont_diff_id.const_smul (2 : ℝ)).sub cont_diff_const

@[simp]
lemma smooth_step.zero : smooth_step 0 = 0 :=
begin
  apply smooth_transition.zero_of_nonpos,
  norm_num
end

@[simp]
lemma smooth_step.one : smooth_step 1 = 1 :=
begin
  apply smooth_transition.one_of_one_le,
  norm_num
end

lemma smooth_step.mem (t : ℝ) : smooth_step t ∈ I :=
⟨smooth_transition.nonneg _, smooth_transition.le_one _⟩

lemma smooth_step.abs_le (t : ℝ) : |smooth_step t| ≤ 1 :=
abs_le.mpr ⟨by linarith [(smooth_step.mem t).1], smooth_transition.le_one _⟩

lemma smooth_step.of_lt {t : ℝ} (h : t < 1/4) : smooth_step t = 0 :=
begin
  apply smooth_transition.zero_of_nonpos,
  linarith
end

lemma smooth_step.pos_of_gt {t : ℝ} (h : 1/4 < t) : 0 < smooth_step t :=
begin
  apply smooth_transition.pos_of_pos,
  linarith
end

lemma smooth_step.of_gt {t : ℝ} (h : 3/4 < t) : smooth_step t = 1 :=
begin
  apply smooth_transition.one_of_one_le,
  linarith
end

lemma htpy_jet_sec_comp_aux {f g : ℝ → E → F} (hf : 𝒞 ∞ ↿f) (hg : 𝒞 ∞ ↿g)
  (hfg : f 1 = g 0) :
  𝒞 ∞ ↿(λ t x, if t ≤ 1/2 then f (smooth_step $ 2*t) x else g (smooth_step $ 2*t - 1) x : ℝ → E → F) :=
begin
  have s₁ : 𝒞 ∞ (λ p : ℝ × E, (smooth_step $ 2*p.1, p.2)),
  { change 𝒞 ∞ ((prod.map smooth_step id) ∘ (λ p : ℝ × E, (2*p.1, p.2))),
    apply (smooth_step.smooth.prod_map cont_diff_id).comp,
    apply cont_diff.prod,
    apply cont_diff_const.mul cont_diff_fst,
    apply cont_diff_snd },
  replace hf := hf.comp s₁,
  have s₂ : 𝒞 ∞ (λ p : ℝ × E, (smooth_step $ 2*p.1 - 1, p.2)),
  { change 𝒞 ∞ ((prod.map smooth_step id) ∘ (λ p : ℝ × E, (2*p.1 - 1, p.2))),
    apply (smooth_step.smooth.prod_map cont_diff_id).comp,
    apply cont_diff.prod,
    apply cont_diff.sub,
    apply cont_diff_const.mul cont_diff_fst,
    apply cont_diff_const,
    apply cont_diff_snd },
  replace hg := hg.comp s₂,
  rw cont_diff_iff_cont_diff_at at *,
  rintros ⟨t₀ , x₀⟩,
  rcases lt_trichotomy t₀ (1/2) with ht|rfl|ht,
  { apply (hf (t₀, x₀)).congr_of_eventually_eq,
    have : (Iio (1/2) : set ℝ) ×ˢ univ ∈ 𝓝 (t₀, x₀),
      from prod_mem_nhds_iff.mpr ⟨Iio_mem_nhds ht, univ_mem⟩,
    filter_upwards [this] with p hp,
    cases p with t x,
    replace hp : t < 1/2 := (prod_mk_mem_set_prod_eq.mp hp).1,
    change ite (t ≤ 1 / 2) (f (smooth_step (2 * t)) x) (g (smooth_step (2 * t - 1)) x) = _,
    rw if_pos hp.le,
    refl },
  { apply (hf (1/2, x₀)).congr_of_eventually_eq,
    have : (Ioo (3/8) (5/8) : set ℝ) ×ˢ univ ∈ 𝓝 (1/(2 : ℝ), x₀),
    { refine prod_mem_nhds_iff.mpr ⟨Ioo_mem_nhds _ _, univ_mem⟩ ; norm_num },
    filter_upwards [this] with p hp,
    cases p with t x,
    cases (prod_mk_mem_set_prod_eq.mp hp).1 with lt_t t_lt,
    change ite (t ≤ 1 / 2) (f (smooth_step (2 * t)) x) (g (smooth_step (2 * t - 1)) x) = _,
    split_ifs,
    { refl },
    { change g _ x = f (smooth_step $ 2*t) x,
      apply congr_fun,
      rw [show smooth_step (2 * t - 1) = 0, by { apply smooth_step.of_lt, linarith },
          show smooth_step (2 * t) = 1, by { apply smooth_step.of_gt, linarith }, hfg] }, },
  { apply (hg (t₀, x₀)).congr_of_eventually_eq,
    have : (Ioi (1/2) : set ℝ) ×ˢ univ ∈ 𝓝 (t₀, x₀),
      from prod_mem_nhds_iff.mpr ⟨Ioi_mem_nhds ht, univ_mem⟩,
    filter_upwards [this] with p hp,
    cases p with t x,
    replace hp : ¬ (t ≤ 1/2) := by push_neg ; exact (prod_mk_mem_set_prod_eq.mp hp).1,
    change ite (t ≤ 1 / 2) (f (smooth_step (2 * t)) x) (g (smooth_step (2 * t - 1)) x) = _,
    rw if_neg hp,
    refl }
end

/-- Concatenation of homotopies of formal solution. The result depend on our choice of
a smooth step function in order to keep smoothness with respect to the time parameter. -/
def htpy_jet_sec.comp (𝓕 𝓖 : htpy_jet_sec E F) (h : 𝓕 1 = 𝓖 0) : htpy_jet_sec E F :=
{ f := λ t x, if t ≤ 1/2 then 𝓕.f (smooth_step $ 2*t) x else 𝓖.f (smooth_step $ 2*t - 1) x,
  f_diff :=
  htpy_jet_sec_comp_aux 𝓕.f_diff 𝓖.f_diff (show (𝓕 1).f = (𝓖 0).f, by rw h),
  φ := λ t x, if t ≤ 1/2 then 𝓕.φ (smooth_step $ 2*t) x else  𝓖.φ (smooth_step $ 2*t - 1) x,
  φ_diff :=
  htpy_jet_sec_comp_aux 𝓕.φ_diff 𝓖.φ_diff (show (𝓕 1).φ = (𝓖 0).φ, by rw h) }

@[simp]
lemma htpy_jet_sec.comp_of_le (𝓕 𝓖 : htpy_jet_sec E F) (h) {t : ℝ} (ht : t ≤ 1/2) :
  𝓕.comp 𝓖 h t = 𝓕 (smooth_step $ 2*t) :=
begin
  dsimp [htpy_jet_sec.comp],
  ext x,
  change (if t ≤ 1/2 then _ else  _) = _,
  rw if_pos ht,
  refl,
  ext1 x,
  change (if t ≤ 1 / 2 then _ else _) = (𝓕 _).φ x,
  rw if_pos ht,
  refl
end


@[simp]
lemma htpy_jet_sec.comp_0 (𝓕 𝓖 : htpy_jet_sec E F) (h) : 𝓕.comp 𝓖 h 0 = 𝓕 0 :=
begin
  rw htpy_jet_sec.comp_of_le _ _ h (by norm_num : (0 : ℝ) ≤ 1/2),
  simp
end

@[simp]
lemma htpy_jet_sec.comp_of_not_le (𝓕 𝓖 : htpy_jet_sec E F) (h) {t : ℝ} (ht : ¬ t ≤ 1/2) :
  𝓕.comp 𝓖 h t = 𝓖 (smooth_step $ 2*t - 1) :=
begin
  dsimp [htpy_jet_sec.comp],
  ext x,
  change (if t ≤ 1/2 then _ else  _) = _,
  rw if_neg ht,
  refl,
  ext1 x,
  change (if t ≤ 1 / 2 then _ else _) = (𝓖 _).φ x,
  rw if_neg ht,
  refl
end

@[simp]
lemma htpy_jet_sec.comp_1 (𝓕 𝓖 : htpy_jet_sec E F) (h) : 𝓕.comp 𝓖 h 1 = 𝓖 1 :=
begin
  rw htpy_jet_sec.comp_of_not_le _ _ h (by norm_num : ¬ (1 : ℝ) ≤ 1/2),
  norm_num
end

end htpy_jet_sec
