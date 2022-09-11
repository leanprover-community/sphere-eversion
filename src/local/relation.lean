import analysis.calculus.specific_functions
import topology.metric_space.hausdorff_distance

import to_mathlib.topology.misc
import to_mathlib.topology.nhds_set
import to_mathlib.topology.hausdorff_distance
import to_mathlib.linear_algebra.basic

import local.dual_pair
import local.ample
import notations

/-!
# Local partial differential relations and their formal solutions

This file defines `rel_loc E F`, the type of first order partial differential relations
for maps between two real normed spaces `E` and `F`.

To any `R : rel_loc E F` we associate the type `sol R` of maps `f : E → F` of
solutions of `R`, and its formal counterpart `formal_sol R`.

The h-principle question is whether we can deform any formal solution into a solution.
The type of deformations is `htpy_jet_sec E F` (homotopies of 1-jet sections).
Implementation note: the time parameter `t` is any real number, but all the homotopies we will
construct will be constant for `t ≤ 0` and `t ≥ 1`. It looks like this imposes more smoothness
constraints at `t = 0` and `t = 1` (requiring flat functions), but this is needed for smooth
concatenations anyway.

This file also defines the ampleness conditions for these relations. Together with openness,
this will guarantee the h-principle (in some other file).
-/

noncomputable theory

open set function module (dual) real filter
open_locale unit_interval topological_space

variables (E : Type*) [normed_add_comm_group E] [normed_space ℝ E]
variables (F : Type*) [normed_add_comm_group F] [normed_space ℝ F]
variables (P : Type*) [normed_add_comm_group P] [normed_space ℝ P]


@[derive metric_space]
def one_jet := E × F × (E →L[ℝ] F)

/-- A first order relation for maps between real vector spaces. -/
def rel_loc := set (one_jet E F)

instance : has_mem (E × F × (E →L[ℝ] F)) (rel_loc E F) := set.has_mem


variables {E F}

namespace rel_loc

/-- The slice of a local relation `R : rel_loc E F` for a dual pair `p` at a jet `θ` is
the set of `w` in `F` such that updating `θ` using `p` and `w` leads to a jet in `R`. -/
def slice (R : rel_loc E F) (p : dual_pair' E) (θ : E × F × (E →L[ℝ] F)) : set F :=
{w | (θ.1, θ.2.1, p.update θ.2.2 w) ∈ R}

lemma mem_slice (R : rel_loc E F) {p : dual_pair' E} {θ : E × F × (E →L[ℝ] F)} {w : F} :
  w ∈ R.slice p θ ↔ (θ.1, θ.2.1, p.update θ.2.2 w) ∈ R :=
iff.rfl

/-- A relation is ample if all its slices are ample. -/
def is_ample (R : rel_loc E F) : Prop := ∀ (p : dual_pair' E) (θ : E × F × (E →L[ℝ] F)),
ample_set (R.slice p θ)

/- FIXME: the proof below is awful. -/
lemma is_ample.mem_hull {R : rel_loc E F} (h : is_ample R) {θ : E × F × (E →L[ℝ] F)}
  (hθ : θ ∈ R) (v : F) (p) : v ∈ hull (connected_component_in (R.slice p θ) (θ.2.2 p.v)) :=
begin
  rw h p θ (θ.2.2 p.v) _,
  exact mem_univ _,
  dsimp [rel_loc.slice],
  rw p.update_self,
  cases θ,
  cases θ_snd,
  exact hθ
end

lemma slice_update {R : rel_loc E F} {θ : E × F × (E →L[ℝ] F)}
  {p : dual_pair' E} (x : F) :
  R.slice p (θ.1, θ.2.1, (p.update θ.2.2 x)) = R.slice p θ :=
begin
  ext1 w,
  dsimp [slice],
  rw [p.update_update]
end

/-- In order to check ampleness, it suffices to consider slices through elements of the relation. -/
lemma is_ample_iff {R : rel_loc E F} : R.is_ample ↔
  ∀ ⦃θ : one_jet E F⦄ (p : dual_pair' E), θ ∈ R → ample_set (R.slice p θ) :=
begin
  simp_rw [is_ample],
  refine ⟨λ h θ p hθ, h p θ, λ h p θ w hw, _⟩,
  dsimp [slice] at hw,
  have := h p hw,
  rw [slice_update] at this,
  exact this w hw
end


open_locale pointwise

lemma slice_of_ker_eq_ker {R : rel_loc E F} {θ : one_jet E F}
  {p p' : dual_pair' E} (hpp' : p.π = p'.π) :
  R.slice p θ = θ.2.2 (p.v - p'.v) +ᵥ R.slice p' θ :=
begin
  rcases θ with ⟨x, y, φ⟩,
  have key : ∀ w, p'.update φ w = p.update φ (w + φ (p.v - p'.v)),
  { intros w,
    simp only [dual_pair'.update, hpp', map_sub, add_right_inj],
    congr' 2,
    abel },
  ext w,
  simp only [slice, mem_set_of_eq, map_sub, vadd_eq_add, mem_vadd_set_iff_neg_vadd_mem, key],
  have : -(φ p.v - φ p'.v) + w + (φ p.v - φ p'.v) = w,
  abel,
  rw this,
end

lemma ample_slice_of_ample_slice {R : rel_loc E F} {θ : one_jet E F}
  {p p' : dual_pair' E} (hpp' : p.π = p'.π) (h : ample_set (R.slice p θ)) :
  ample_set (R.slice p' θ) :=
begin
  rw slice_of_ker_eq_ker hpp'.symm,
  exact ample_set.vadd h
end

/-- A solution to a local relation `R`. -/
@[ext] structure sol (R : rel_loc E F) :=
(f : E → F)
(f_diff : 𝒞 ∞ f)
(is_sol : ∀ x, (x, f x, D f x) ∈ R)

variables (E)

@[ext] structure jet_sec (F : Type*) [normed_add_comm_group F] [normed_space ℝ F] :=
(f : E → F)
(f_diff : 𝒞 ∞ f)
(φ : E → E →L[ℝ] F)
(φ_diff : 𝒞 ∞ φ)

variables {E}

def jet_sec.is_formal_sol (𝓕 : jet_sec E F) (R : rel_loc E F) : Prop :=
∀ x, (x, 𝓕.f x, 𝓕.φ x) ∈ R

/-- A formal solution to a local relation `R` over a set `U`. -/
@[ext] structure formal_sol (R : rel_loc E F) extends jet_sec E F :=
(is_sol : ∀ x, (x, f x, φ x) ∈ R)

instance (R : rel_loc E F) : has_coe (formal_sol R) (jet_sec E F):=
⟨formal_sol.to_jet_sec⟩

@[simp] lemma formal_sol.to_jet_sec_eq_coe {R : rel_loc E F} (𝓕 : formal_sol R) :
𝓕.to_jet_sec = (𝓕 : jet_sec E F) := rfl

@[simp] lemma formal_sol.coe_is_formal_sol  {R : rel_loc E F} (𝓕 : formal_sol R) :
  (𝓕 : jet_sec E F).is_formal_sol R := 𝓕.is_sol

def jet_sec.is_formal_sol.formal_sol  {𝓕 : jet_sec E F} {R : rel_loc E F}
  (h : 𝓕.is_formal_sol R) : formal_sol R :=
{is_sol := h, ..𝓕}

/-- Inclusion of solutions into formal solutions. -/
def sol.to_formal_sol {R : rel_loc E F}  (𝓕 : sol R) : formal_sol R :=
{ f := 𝓕.f,
  f_diff := 𝓕.f_diff,
  φ := D 𝓕.f,
  φ_diff := (cont_diff_top_iff_fderiv.mp 𝓕.f_diff).2,
  is_sol := 𝓕.is_sol }

end rel_loc

namespace rel_loc.jet_sec

open rel_loc

instance : has_coe_to_fun (jet_sec E F) (λ S, E → F × (E →L[ℝ] F)) :=
⟨λ 𝓕, λ x, (𝓕.f x, 𝓕.φ x)⟩

instance (R : rel_loc E F) (U : set E) : has_coe_to_fun (formal_sol R) (λ S, E → F × (E →L[ℝ] F)) :=
⟨λ 𝓕, λ x, (𝓕.f x, 𝓕.φ x)⟩

@[simp] lemma formal_sol.coe_apply  {R : rel_loc E F} (𝓕 : formal_sol R) (x : E) :
(𝓕 : jet_sec E F) x = 𝓕 x := rfl

lemma jet_sec.eq_iff {𝓕 𝓕' : jet_sec E F} {x : E} :
  𝓕 x = 𝓕' x ↔ 𝓕.f x = 𝓕'.f x ∧ 𝓕.φ x = 𝓕'.φ x :=
begin
  split,
  { intro h,
    exact ⟨congr_arg prod.fst h, congr_arg prod.snd h⟩ },
  { rintros ⟨h, h'⟩,
    ext1,
    exacts [h, h'] }
end

variables  {R : rel_loc E F}

lemma formal_sol.eq_iff {𝓕 𝓕' : formal_sol R} {x : E} :
  𝓕 x = 𝓕' x ↔ 𝓕.f x = 𝓕'.f x ∧ 𝓕.φ x = 𝓕'.φ x :=
jet_sec.eq_iff

/-- The slice associated to a jet section and a dual pair at some point. -/
def slice_at (𝓕 : jet_sec E F) (R : rel_loc E F) (p : dual_pair' E) (x : E) : set F :=
R.slice p (x, 𝓕.f x, 𝓕.φ x)

/-- The slice associated to a formal solution and a dual pair at some point. -/
def _root_.rel_loc.formal_sol.slice_at (𝓕 : formal_sol R) (p : dual_pair' E) (x : E) : set F :=
R.slice p (x, 𝓕.f x, 𝓕.φ x)

/-- A jet section `𝓕` is holonomic if its linear map part at `x`
is the derivative of its function part at `x`. -/
def is_holonomic_at (𝓕 : jet_sec E F) (x : E) : Prop := D 𝓕.f x = 𝓕.φ x

def _root_.rel_loc.formal_sol.is_holonomic_at (𝓕 : formal_sol R) (x : E) : Prop := D 𝓕.f x = 𝓕.φ x

lemma _root_.rel_loc.formal_sol.is_holonomic_at_congr (𝓕 𝓕' : formal_sol R) {s : set E}
  (h : ∀ᶠ x near s, 𝓕 x = 𝓕' x) : ∀ᶠ x near s, 𝓕.is_holonomic_at x ↔ 𝓕'.is_holonomic_at x :=
begin
  apply h.eventually_nhds_set.mono,
  intros x hx,
  have hf : 𝓕.f =ᶠ[𝓝 x] 𝓕'.f,
  { apply hx.mono,
    simp_rw formal_sol.eq_iff,
    tauto },
  unfold rel_loc.formal_sol.is_holonomic_at,
  rw [hf.fderiv_eq, (formal_sol.eq_iff.mp hx.self_of_nhds).2]
end

lemma _root_.rel_loc.sol.is_holonomic {R : rel_loc E F} (𝓕 : sol R) (x : E) :
  𝓕.to_formal_sol.is_holonomic_at x :=
by simp [rel_loc.sol.to_formal_sol, rel_loc.formal_sol.is_holonomic_at]

/-- A formal solution of `R` over `U` that is holonomic at every point of `U`
comes from a genuine solution. -/
def _root_.rel_loc.formal_sol.to_sol (𝓕 : formal_sol R) (h : ∀ x, 𝓕.to_jet_sec.is_holonomic_at x) : sol R :=
{ f := 𝓕.f,
  f_diff := 𝓕.f_diff,
  is_sol := λ x, ((h x).symm ▸ (𝓕.is_sol x)) }

lemma to_sol_to_formal_sol (𝓕 : sol R) :
  𝓕.to_formal_sol.to_sol (λ x, 𝓕.is_holonomic x) = 𝓕 :=
by { ext x, refl }

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
    simp_rw jet_sec.eq_iff,
    tauto },
  unfold rel_loc.jet_sec.is_part_holonomic_at,
  rw [hf.fderiv_eq, (jet_sec.eq_iff.mp hx.self_of_nhds).2]
end

lemma is_part_holonomic_at.sup (𝓕 : jet_sec E F) {E' E'' : submodule ℝ E} {x : E}
  (h' : 𝓕.is_part_holonomic_at E' x) (h'' : 𝓕.is_part_holonomic_at E'' x) :
  𝓕.is_part_holonomic_at (E' ⊔ E'') x :=
λ v : E, linear_map.eq_on_sup h' h''

lemma _root_.rel_loc.jet_sec.is_part_holonomic_at.mono {𝓕 : jet_sec E F}
  {E' E'' : submodule ℝ E} {x : E} (h : 𝓕.is_part_holonomic_at E' x) (h' : E'' ≤ E') :
  𝓕.is_part_holonomic_at E'' x :=
λ v v_in, h v $ set_like.coe_subset_coe.mpr h' v_in

def _root_.rel_loc.formal_sol.is_part_holonomic_at (𝓕 : formal_sol R) (E' : submodule ℝ E) (x : E) :=
∀ v ∈ E', D 𝓕.f x v = 𝓕.φ x v

lemma _root_.rel_loc.formal_sol.is_part_holonomic_at.mono {𝓕 : formal_sol R}
  {E' E'' : submodule ℝ E} {x : E} (h : 𝓕.is_part_holonomic_at E' x) (h' : E'' ≤ E') :
  𝓕.is_part_holonomic_at E'' x :=
λ v v_in, h v $ set_like.coe_subset_coe.mpr h' v_in

lemma _root_.is_part_holonomic_top {𝓕 : jet_sec E F} {x : E} :
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


lemma mem_slice (𝓕 : formal_sol R) (p : dual_pair' E) {x : E} :
  𝓕.φ x p.v ∈ 𝓕.slice_at p x :=
by simpa [rel_loc.formal_sol.slice_at, rel_loc.slice] using  𝓕.is_sol x

/-- A formal solution `𝓕` is short for a dual pair `p` at a point `x` if the derivative of
the function `𝓕.f` at `x` is in the convex hull of the relevant connected component of the
corresponding slice. -/
def is_short_at (𝓕 : jet_sec E F) (R : rel_loc E F) (p : dual_pair' E) (x : E) : Prop :=
D 𝓕.f x p.v ∈ hull (connected_component_in (𝓕.slice_at R p x) $ 𝓕.φ x p.v)

def _root_.rel_loc.formal_sol.is_short_at (𝓕 : formal_sol R)(p : dual_pair' E) (x : E) : Prop :=
D 𝓕.f x p.v ∈ hull (connected_component_in (𝓕.slice_at p x) $ 𝓕.φ x p.v)

lemma _root_.rel_loc.is_ample.is_short_at {R : rel_loc E F} (hR : is_ample R) (𝓕 : formal_sol R) (p : dual_pair' E)
  (x : E) : 𝓕.is_short_at p x :=
hR.mem_hull (𝓕.is_sol x) _ p

end rel_loc.jet_sec

section htpy_jet_sec

open rel_loc

variables (E F)

/-- A homotopy of sections of J¹(E, F). -/
structure htpy_jet_sec :=
(f : ℝ → E → F)
(f_diff : 𝒞 ∞ ↿f)
(φ : ℝ → E → E →L[ℝ] F)
(φ_diff : 𝒞 ∞ ↿φ)

variables  {E F} {R : rel_loc E F}

instance : has_coe_to_fun (htpy_jet_sec E F) (λ S, ℝ → jet_sec E F) :=
⟨λ S t,
 { f := S.f t,
   f_diff := S.f_diff.comp (cont_diff_const.prod cont_diff_id),
   φ := S.φ t,
   φ_diff := S.φ_diff.comp (cont_diff_const.prod cont_diff_id) }⟩

namespace htpy_jet_sec

lemma cont_diff_f (𝓕 : htpy_jet_sec E F) {n : ℕ∞} : 𝒞 n ↿𝓕.f :=
𝓕.f_diff.of_le le_top

lemma cont_diff_φ (𝓕 : htpy_jet_sec E F) {n : ℕ∞} : 𝒞 n ↿𝓕.φ :=
𝓕.φ_diff.of_le le_top

end htpy_jet_sec

/-- The constant homotopy of formal solutions at a given formal solution. It will be used
as junk value for constructions of formal homotopies that need additional assumptions and also
for trivial induction initialization. -/
def rel_loc.jet_sec.const_htpy (𝓕 : jet_sec E F) : htpy_jet_sec E F :=
{ f := λ t, 𝓕.f,
  f_diff := 𝓕.f_diff.snd',
  φ := λ t, 𝓕.φ,
  φ_diff := 𝓕.φ_diff.snd' }

@[simp] lemma rel_loc.jet_sec.const_htpy_apply (𝓕 : jet_sec E F) :
  ∀ t, 𝓕.const_htpy t = 𝓕 :=
λ t, by ext x ; refl

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
/- begin
  have c3 : ∀ {n}, 𝒞 n (λ t : ℝ, 2 * t) :=
  λ n, cont_diff_const.mul cont_diff_id,
  have c4 : ∀ {n}, 𝒞 n ↿(λ t : ℝ, 2 * t - 1) :=
  λ n, (cont_diff_const.mul cont_diff_id).sub cont_diff_const,
  have c5 : ∀ {n}, 𝒞 n (λ t, smooth_step $ 2 * t) :=
  λ n, smooth_transition.cont_diff.comp c3,
  have c6 : ∀ {n}, 𝒞 n ↿(λ t, smooth_step $ 2*t - 1) :=
  λ n, smooth_transition.cont_diff.comp c4,
  have h1 : ∀ {n}, 𝒞 n ↿(λ t, f (smooth_step $ 2*t)) :=
  λ n, hf.comp₂ c5.fst' cont_diff_snd,
  have h2 : ∀ {n}, 𝒞 n ↿(λ t, g (smooth_step $ 2*t - 1)) :=
  λ n, hg.comp₂ c6.fst' cont_diff_snd,
  refine h1.if_le_of_fderiv h2 cont_diff_fst cont_diff_const _,
  rintro ⟨t, x⟩ n ht,
  dsimp only at ht,
  subst ht,
  simp [has_uncurry.uncurry],
  cases n,
  { simp [iterated_fderiv_zero_eq_comp, hfg], },
  rw [iterated_fderiv_of_partial, iterated_fderiv_of_partial],
  { simp [has_uncurry.uncurry, hfg],
    congr' 1,
    refine (iterated_fderiv_comp (hf.comp₂ cont_diff_id cont_diff_const) c5 _).trans _,
    convert continuous_multilinear_map.comp_zero _,
    { ext1 i, refine (iterated_fderiv_comp smooth_transition.cont_diff c3 _).trans _,
      convert continuous_multilinear_map.zero_comp _, simp },
    refine (iterated_fderiv_comp (hg.comp₂ cont_diff_id cont_diff_const) c6 _).trans _,
    convert continuous_multilinear_map.comp_zero _,
    { ext1 i, refine (iterated_fderiv_comp smooth_transition.cont_diff c4 _).trans _,
      convert continuous_multilinear_map.zero_comp _, simp [has_uncurry.uncurry] } },
  { exact λ x, h2.comp₂ cont_diff_const cont_diff_id },
  { exact λ y, h2.comp₂ cont_diff_id cont_diff_const },
  { exact λ x, h1.comp₂ cont_diff_const cont_diff_id },
  { exact λ y, h1.comp₂ cont_diff_id cont_diff_const },
end -/

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

/-- A homotopy of formal solutions is a 1-parameter family of formal solutions. -/
@[ext] structure rel_loc.htpy_formal_sol (R : rel_loc E F) extends htpy_jet_sec E F :=
(is_sol : ∀ t x, (x, f t x, φ t x) ∈ R)

open rel_loc

instance (R : rel_loc E F) : has_coe_to_fun (htpy_formal_sol R) (λ S, ℝ → jet_sec E F) :=
⟨λ S t,
 { f := S.f t,
   f_diff := S.f_diff.comp (cont_diff_const.prod cont_diff_id),
   φ := S.φ t,
   φ_diff := S.φ_diff.comp (cont_diff_const.prod cont_diff_id) }⟩
