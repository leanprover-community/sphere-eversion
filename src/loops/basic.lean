import analysis.normed_space.add_torsor_bases
import analysis.convex.caratheodory
import analysis.calculus.times_cont_diff
import measure_theory.integral.set_integral
import measure_theory.measure.lebesgue
import topology.algebra.floor_ring
import topology.path_connected
import linear_algebra.affine_space.independent
import loops.homotheties
import to_mathlib.topology.misc

/-!
# Basic definitions and properties of loops
-/

open set function finite_dimensional int (hiding range)
open_locale big_operators topological_space topological_space unit_interval
noncomputable theory

def nhds_set {α : Type*} [topological_space α] (s : set α) : filter α :=
Sup (nhds '' s)

variables {E : Type*} [normed_group E] [normed_space ℝ E]
          {F : Type*} [normed_group F] [normed_space ℝ F] [finite_dimensional ℝ F]
          {F' : Type*} [normed_group F'] [normed_space ℝ F'] [finite_dimensional ℝ F']

local notation `d` := finrank ℝ F

local notation `smooth_on` := times_cont_diff_on ℝ ⊤

def smooth_at (f : E → F) (x : E) : Prop := ∃ s ∈ 𝓝 x, smooth_on f s

section surrounding_points

-- def:surrounds_points
structure surrounding_pts (f : F) (p : fin (d + 1) → F) (w : fin (d + 1) → ℝ) : Prop :=
(indep : affine_independent ℝ p)
(w_pos : ∀ i, 0 < w i)
(w_sum : ∑ i, w i = 1)
(avg : ∑ i, (w i) • (p i) = f)


def surrounded (f : F) (s : set F) : Prop :=
∃ p w, surrounding_pts f p w ∧ ∀ i, p i ∈ s

lemma surrounded_iff_mem_interior_convex_hull_aff_basis {f : F} {s : set F} :
  surrounded f s ↔ ∃ (b : set F)
                     (h₀ : b ⊆ s)
                     (h₁ : affine_independent ℝ (coe : b → F))
                     (h₂ : affine_span ℝ b = ⊤),
                     f ∈ interior (convex_hull ℝ b) :=
begin
  split,
  { rintros ⟨p, w, ⟨⟨indep, w_pos, w_sum, rfl⟩, h_mem⟩⟩,
    have h_tot : affine_span ℝ (range p) = ⊤ :=
      indep.affine_span_eq_top_iff_card_eq_finrank_add_one.mpr (fintype.card_fin _),
    refine ⟨range p, range_subset_iff.mpr h_mem, indep.range, h_tot, _⟩,
    rw interior_convex_hull_aff_basis indep h_tot,
    intros i,
    rw [← finset.affine_combination_eq_linear_combination _ _ _ w_sum,
      barycentric_coord_apply_combination_of_mem _ _ (finset.mem_univ i) w_sum],
    exact w_pos i, },
  { rintros ⟨b, h₀, h₁, h₂, h₃⟩,
    haveI : fintype b := (finite_of_fin_dim_affine_independent ℝ h₁).fintype,
    have hb : fintype.card b = d + 1,
    { rw [← h₁.affine_span_eq_top_iff_card_eq_finrank_add_one, subtype.range_coe_subtype,
        set_of_mem_eq, h₂], },
    let p := (coe : _ → F) ∘ (fintype.equiv_fin_of_card_eq hb).symm,
    have hp : b = range p,
    { ext x,
      exact ⟨by { intros h, use fintype.equiv_fin_of_card_eq hb ⟨x, h⟩, simp [p], },
             by { rintros ⟨y, rfl⟩, apply subtype.coe_prop, }⟩, },
    rw hp at h₀ h₂ h₃,
    replace h₁ : affine_independent ℝ p :=
      h₁.comp_embedding (fintype.equiv_fin_of_card_eq hb).symm.to_embedding,
    rw [interior_convex_hull_aff_basis h₁ h₂, mem_set_of_eq] at h₃,
    refine ⟨p, λ i, barycentric_coord h₁ h₂ i f, ⟨h₁, h₃, _, _⟩, λ i, h₀ (mem_range_self i)⟩,
    { exact sum_barycentric_coord_apply_eq_one h₁ h₂ f, },
    { rw [← finset.univ.affine_combination_eq_linear_combination p _
        (sum_barycentric_coord_apply_eq_one h₁ h₂ f),
        affine_combination_barycentric_coord_eq_self], }, },
end

--- lem:int_cvx
lemma surrounded_of_convex_hull {f : F} {s : set F} (hs : is_open s) (hsf : f ∈ convex_hull ℝ s) :
  surrounded f s :=
begin
  rw surrounded_iff_mem_interior_convex_hull_aff_basis,
  obtain ⟨t, hts, hai, hf⟩ := (by simpa only [exists_prop, mem_Union] using convex_hull_eq_union.subst hsf :
    ∃ (t : finset F), (t : set F) ⊆ s ∧ affine_independent ℝ (coe : t → F) ∧ f ∈ convex_hull ℝ (t : set F)),
  have htne : (t : set F).nonempty := (@convex_hull_nonempty_iff ℝ _ _ _ _ _).mp ⟨f, hf⟩,
  obtain ⟨b, hb₁, hb₂, hb₃, hb₄⟩ := exists_subset_affine_independent_span_eq_top_of_open hs hts htne hai,
  have hb₀ : b.finite, { exact finite_of_fin_dim_affine_independent ℝ hb₃, },
  obtain ⟨c, hc⟩ := interior_convex_hull_nonempty_iff_aff_span_eq_top.mpr hb₄,
  obtain ⟨ε, hε, hcs⟩ := homothety_image_subset_of_open c hs hb₂ hb₀,
  have hbε := convex.subset_interior_image_homothety_of_one_lt
    (convex_convex_hull ℝ _) hc (1 + ε) (lt_add_of_pos_right 1 hε),
  rw affine_map.image_convex_hull at hbε,
  let t : units ℝ := units.mk0 (1 + ε) (by linarith),
  refine ⟨affine_map.homothety c (t : ℝ) '' b, hcs, _, _, hbε (convex_hull_mono hb₁ hf)⟩,
  { rwa (affine_equiv.homothety_units_mul_hom c t).affine_independent_set_of_eq_iff, },
  { exact (affine_equiv.homothety_units_mul_hom c t).span_eq_top_iff.mp hb₄, },
end

-- lem:smooth_convex_hull
lemma smooth_surrounding {x : F} {p w} (h : surrounding_pts x p w) :
  ∃ W : F → (fin (d+1) → F) → (fin (d+1) → ℝ),
  ∀ᶠ y in 𝓝 x, ∀ᶠ q in  𝓝 p, smooth_at (uncurry W) (y, q) ∧
                              ∀ i, W y q i ∈ Ioo (0 : ℝ) 1 ∧
                              ∑ i, W y q i • q i = y :=
sorry

end surrounding_points

namespace path

/-- A loop evaluated at `t / t` is equal to its endpoint. Note that `t / t = 0` for `t = 0`. -/
@[simp] lemma extend_div_self {x : F} (γ : path x x) (t : ℝ) : γ.extend (t / t) = x :=
by by_cases h : t = 0; simp [h]

/-- Concatenation of two loops which moves through the first loop on `[0, t₀]` and
through the second one on `[t₀, 1]`. All endpoints are assumed to be the same so that this
function is also well-defined for `t₀ ∈ {0, 1}`.
`strans` stands either for a *s*kewed transitivity, or a transitivity with different *s*peeds. -/
def strans {x : F} (γ γ' : path x x) (t₀ : I) : path x x :=
{ to_fun := λ t, if t ≤ t₀ then γ.extend (t / t₀) else γ'.extend ((t - t₀) / (1 - t₀)),
  continuous_to_fun :=
  begin
    refine continuous.if_le _ _ continuous_id continuous_const (by simp only [extend_div_self,
      unit_interval.mk_zero, zero_le_one, id.def, zero_div, forall_eq, extend_extends, path.source,
      left_mem_Icc, sub_self]),
    -- TODO: the following are provable by `continuity` but it is too slow
    exacts [γ.continuous_extend.comp continuous_subtype_coe.div_const,
      γ'.continuous_extend.comp (continuous_subtype_coe.sub continuous_const).div_const]
  end,
  source' := by simp only [unit_interval.nonneg', unit_interval.coe_zero,
    unit_interval.mk_zero, zero_le_one,
    if_true, zero_div, comp_app, extend_extends, path.source, left_mem_Icc],
  target' := by simp only [unit_interval.le_one'.le_iff_eq.trans eq_comm, extend_div_self,
    unit_interval.coe_one, implies_true_iff, eq_self_iff_true, comp_app, ite_eq_right_iff]
    {contextual := tt}}

@[simp] lemma strans_zero {x : F} (γ γ' : path x x) : γ.strans γ' 0 = γ' :=
by { ext t, simp only [strans, path.coe_mk, if_pos, unit_interval.coe_zero,
  div_one, extend_extends',
  unit_interval.nonneg'.le_iff_eq, sub_zero, div_zero, extend_zero, ite_eq_right_iff,
  show (t : ℝ) = 0 ↔ t = 0, from (@subtype.ext_iff _ _ t 0).symm, path.source, eq_self_iff_true,
  implies_true_iff] {contextual := tt} }

@[simp] lemma strans_one {x : F} (γ γ' : path x x) : γ.strans γ' 1 = γ :=
by { ext t, simp only [strans, unit_interval.le_one', path.coe_mk, if_pos, div_one,
  extend_extends', unit_interval.coe_one] }

@[simp] lemma strans_of_ge {x : F} (γ γ' : path x x) {t₀ t : I} (h : t₀ ≤ t) :
  γ.strans γ' t₀ t = γ'.extend ((t - t₀) / (1 - t₀)) :=
begin
  simp only [path.coe_mk, path.strans, ite_eq_right_iff],
  intro h2, obtain rfl := le_antisymm h h2, simp
end

@[simp] lemma strans_self {x : F} (γ γ' : path x x) (t₀ : I) : γ.strans γ' t₀ t₀ = x :=
by { simp only [strans, path.coe_mk, extend_div_self, if_pos, le_rfl], }

@[simp] lemma refl_strans_refl {x : F} {t₀ : I} : (refl x).strans (refl x) t₀ = refl x :=
by { ext s, simp [strans] }

lemma range_strans_left {x : F} {γ γ' : path x x} {t₀ : I} (h : t₀ ≠ 0) :
  range γ ⊆ range (γ.strans γ' t₀) :=
by { rintro _ ⟨t, rfl⟩, use t * t₀,
  simp [strans, unit_interval.mul_le_right, unit_interval.coe_ne_zero.mpr h] }

lemma range_strans_right {x : F} {γ γ' : path x x} {t₀ : I} (h : t₀ ≠ 1) :
  range γ' ⊆ range (γ.strans γ' t₀) :=
begin
  rintro _ ⟨t, rfl⟩,
  have := mul_nonneg t.2.1 (sub_nonneg.mpr t₀.2.2),
  let t' : I := ⟨t₀ + t * (1 - t₀), add_nonneg t₀.2.1 this, by { rw [add_comm, ← le_sub_iff_add_le],
    refine (mul_le_mul_of_nonneg_right t.2.2 $ sub_nonneg.mpr t₀.2.2).trans_eq (one_mul _) }⟩,
  have h2 : t₀ ≤ t' := le_add_of_nonneg_right this,
  have h3 := sub_ne_zero.mpr (unit_interval.coe_ne_one.mpr h).symm,
  use t',
  simp [h2, unit_interval.coe_ne_one.mpr h, h3],
end

-- this lemma is easier if we reorder/reassociate the arguments
lemma _root_.continuous.path_strans {X : Type*} [uniform_space X] [separated_space X]
  [locally_compact_space X] {f : X → F} {t : X → I} {s : X → I}
  {γ γ' : ∀ x, path (f x) (f x)}
  (hγ : continuous ↿γ)
  (hγ' : continuous ↿γ')
  (hγ0 : ∀ ⦃x s⦄, t x = 0 → γ x s = f x)
  (hγ'1 : ∀ ⦃x s⦄, t x = 1 → γ' x s = f x)
  (ht : continuous t)
  (hs : continuous s) :
  continuous (λ x, strans (γ x) (γ' x) (t x) (s x)) :=
begin
  have hγ0 : ∀ {x₀}, t x₀ = 0 → tendsto_uniformly (λ x, γ x) (λ _, f x₀) (𝓝 x₀),
  { intros x₀ hx₀, convert continuous.tendsto_uniformly (λ x, γ x) hγ _,
    ext t, rw [hγ0 hx₀] },
  have hγ'1 : ∀ {x₀}, t x₀ = 1 → tendsto_uniformly (λ x, γ' x) (λ _, f x₀) (𝓝 x₀),
  { intros x₀ hx₀, convert continuous.tendsto_uniformly (λ x, γ' x) hγ' _,
    ext t, rw [hγ'1 hx₀] },
  refine continuous.if_le _ _ hs ht _,
  { rw [continuous_iff_continuous_at],
    intro x,
    refine (continuous_subtype_coe.comp hs).continuous_at.comp_div_cases (λ x s, (γ x).extend s)
      (continuous_subtype_coe.comp ht).continuous_at _ _,
    { intro h,
      refine continuous_at.extend _ _ continuous_at_snd,
      exact hγ.continuous_at.comp (continuous_at_fst.fst.prod continuous_at_snd) },
    { intro h,
      have ht : t x = 0 := subtype.ext h,
      apply filter.tendsto.extend,
      dsimp only, rw [(proj_Icc_surjective _).map_top, extend_zero],
      refine tendsto_prod_top_iff.mpr (hγ0 ht) } },
  { rw [continuous_iff_continuous_at],
    intro x,
    refine ((continuous_subtype_coe.comp hs).sub (continuous_subtype_coe.comp ht))
      .continuous_at.comp_div_cases (λ x s, (γ' x).extend s)
      (continuous_const.sub $ continuous_subtype_coe.comp ht).continuous_at _ _,
    { intro h,
      refine continuous_at.extend _ _ continuous_at_snd,
      exact hγ'.continuous_at.comp (continuous_at_fst.fst.prod continuous_at_snd) },
    { intro h,
      have ht : t x = 1 := subtype.ext (sub_eq_zero.mp h).symm,
      apply filter.tendsto.extend,
      dsimp only, rw [(proj_Icc_surjective _).map_top, extend_zero],
      refine tendsto_prod_top_iff.mpr (hγ'1 ht) } },
  { rintro x h, rw [h, sub_self, zero_div, extend_div_self, extend_zero] },
end

end path

set_option old_structure_cmd true

variables (E F)

structure loop :=
(to_fun : ℝ → F)
(per' : ∀ t, to_fun (t + 1) = to_fun t)

instance : has_coe_to_fun (loop F) (λ _, ℝ → F) := ⟨λ γ, γ.to_fun⟩

initialize_simps_projections loop (to_fun → apply)

/-- Any function `φ : α → loop F` can be seen as a function `α × ℝ → F`. -/
@[uncurry_simps]
instance has_uncurry_loop {α : Type*} : has_uncurry (α → loop F) (α × ℝ) F := ⟨λ φ p, φ p.1 p.2⟩

variables {E F}

@[simps]
def const_loop (f : F) : loop F :=
⟨λ t, f, by simp⟩

namespace loop

@[ext] protected lemma ext : ∀ {γ₁ γ₂ : loop F}, (γ₁ : ℝ → F) = γ₂ → γ₁ = γ₂
| ⟨x, h1⟩ ⟨.(x), h2⟩ rfl := rfl

/-- Periodicity of loops restated in terms of the function coercion. -/
lemma per (γ : loop F) : ∀ t, γ (t + 1) = γ t :=
loop.per' γ

protected lemma one (γ : loop F) : γ 1 = γ 0 :=
by { convert γ.per 0, rw [zero_add] }

/-- Transforming a loop by applying function `f`. -/
@[simps]
def transform (γ : loop F) (f : F → F') : loop F' :=
⟨λ t, f (γ t), λ t, by rw γ.per⟩

/-- Shifting a loop, or equivalently, adding a constant value to a loop -/
@[simps]
def shift (γ : loop F) (x : F) : loop F := γ.transform (+ x)

/-- The average value of a loop. -/
noncomputable
def average [measurable_space F] [borel_space F] (γ : loop F) : F := ∫ x in Icc 0 1, (γ x)

def support {X : Type*} [topological_space X] [measurable_space F] [borel_space F] (γ : X → loop F) : set X :=
closure {x | γ x ≠ const_loop (γ x).average}

lemma const_of_not_mem_support {X : Type*} [topological_space X] [measurable_space F] [borel_space F] {γ : X → loop F} {x : X}
  (hx : x ∉ support γ) : γ x = const_loop (γ x).average :=
begin
  classical,
  by_contradiction H,
  apply hx,
  apply subset_closure,
  exact H
end

lemma continuous_of_family {α : Type*} [topological_space α] {γ : α → loop F} (h : continuous ↿γ) :
  ∀ a, continuous (γ a) :=
begin
  intro a,
  rw show (γ a : ℝ → F) = ↿γ ∘ (λ t, (a, t)), from rfl,
  exact h.comp (continuous_const.prod_mk continuous_id')
end

lemma continuous_of_family_step {α β : Type*} [topological_space α] [topological_space β]
  {γ : α → β → loop F} (h : continuous ↿γ) : ∀ a, continuous ↿(γ a) :=
begin
  intro a,
  rw show ↿(γ a : β → loop F) = ↿γ ∘ (λ t, (a, t)), from rfl,
  exact h.comp (continuous_const.prod_mk continuous_id')
end

lemma add_nat_eq (γ : loop F) (t : ℝ) : ∀ (n : ℕ), γ (t+n) = γ t
| 0 := (add_zero t).symm ▸ rfl
| (nat.succ n) := by rw [← add_nat_eq n, nat.cast_succ, ← add_assoc, γ.per]

lemma add_int_eq (γ : loop F) (t : ℝ) (n : ℤ) : γ (t+n) = γ t :=
begin
  induction n using int.induction_on with n hn n hn,
  { norm_cast, rw add_zero },
  { rw [← hn, int.cast_add, ← add_assoc, int.cast_one, γ.per] },
  { rw [← hn, int.cast_sub, add_sub, int.cast_one, ← γ.per, sub_add_cancel] }
end

lemma fract_eq (γ : loop F) : ∀ t, γ (fract t) = γ t :=
begin
  intro t,
  unfold fract,
  rw [sub_eq_add_neg, ← int.cast_neg],
  exact γ.add_int_eq _ _
end

lemma comp_fract_eq (γ : loop F) : γ ∘ fract = γ :=
funext γ.fract_eq

lemma range_eq_image (γ : loop F) : range γ = γ '' I :=
begin
  apply eq_of_subset_of_subset,
  { rw range_subset_iff,
    exact λ y, ⟨fract y, unit_interval.fract_mem y, γ.fract_eq _⟩ },
  { rintros y ⟨x, hx, hxy⟩,
    exact ⟨x, hxy⟩ },
end

@[simps]
noncomputable
def of_path {x : F} (γ : path x x) : loop F :=
{ to_fun := λ t, γ.extend (fract t),
  per' :=
  begin
    intros t,
    congr' 1,
    rw fract_eq_fract,
    use 1,
    norm_num
  end }

@[simp]
lemma range_of_path {x : F} (γ : path x x) : range (of_path γ) = range γ :=
begin
  rw loop.range_eq_image,
  unfold_coes,
  simp only [of_path, image_eq_range],
  congr,
  ext t,
  by_cases ht1 : t.val = 1,
  { have : t = ⟨1, right_mem_Icc.mpr zero_le_one⟩ := subtype.ext_val ht1,
    rw this,
    norm_cast,
    simp only [fract, floor_one, path.extend_zero, int.cast_one, sub_self, subtype.coe_mk],
    exact γ.target.symm },
  { change (t : ℝ) ≠ 1 at ht1,
    have : fract ↑t = t.val,
    { rw fract_eq_iff,
      exact ⟨t.2.1, lt_of_le_of_ne t.2.2 ht1, ⟨0, sub_self _⟩⟩ },
    simp only [this, γ.extend_extends t.2],
    congr',
    rw subtype.ext_iff_val }
end

lemma of_path_continuous {x : F} (γ : path x x) : continuous (of_path γ) :=
begin
  simp only [has_coe_to_fun.coe, coe_fn, of_path],
  apply γ.continuous_extend.continuous_on.comp_fract,
  rw [γ.extend_zero, γ.extend_one]
end

-- move
lemma continuous_on.comp_fract'' {α β γ : Type*} [linear_ordered_ring α] [floor_ring α]
  [topological_space α] [order_topology α]
  [topological_add_group α] [topological_space β] [topological_space γ]
  {s : β → α}
  {f : β → α → γ}
  (h : continuous_on (uncurry f) $ (univ : set β).prod (Icc 0 1 : set α))
  (hs : continuous s)
  (hf : ∀ s, f s 0 = f s 1) :
  continuous (λ x : β, f x $ fract (s x)) :=
(h.comp_fract' hf).comp (continuous_id.prod_mk hs)

/-- `loop.of_path` is continuous, general version. -/
lemma _root_.continuous.of_path {ι : Type*} [topological_space ι] (x : ι → F) (t : ι → ℝ)
  (γ : ∀ (i : ι), path (x i) (x i)) (hγ : continuous ↿γ) (ht : continuous t) :
  continuous (λ i, of_path (γ i) (t i)) :=
begin
  change continuous (λ i : ι, (λ s, (γ s).extend) i (fract (t i))),
  refine continuous_on.comp_fract'' _ ht _,
  { exact (hγ.comp (continuous_id.prod_map continuous_proj_Icc)).continuous_on },
  { simp only [unit_interval.mk_zero, zero_le_one, path.target, path.extend_extends,
      implies_true_iff, eq_self_iff_true, path.source, right_mem_Icc, left_mem_Icc,
      unit_interval.mk_one] }
end

/-- `loop.of_path` is continuous, where the endpoints of `γ` are fixed. TODO: remove -/
lemma of_path_continuous_family {ι : Type*} [topological_space ι] {x : F} (γ : ι → path x x)
  (h : continuous ↿γ) : continuous ↿(λ s, of_path $ γ s) :=
continuous.of_path _ _ (λ i : ι × ℝ, γ i.1) (h.comp $ continuous_fst.prod_map continuous_id)
  continuous_snd

def round_trip {x y : F} (γ : path x y) : loop F :=
of_path (γ.trans γ.symm)

lemma round_trip_range {x y : F} {γ : path x y} : range (round_trip γ) = range γ :=
by simp [round_trip, range_of_path, path.trans_range, path.symm_range]

lemma round_trip_based_at {x y : F} {γ : path x y} : round_trip γ 0 = x :=
begin
  unfold_coes,
  rw [round_trip, of_path],
  simp [fract_zero]
end

lemma round_trip_continuous {x y : F} (γ : path x y) : continuous (round_trip γ) :=
of_path_continuous _

noncomputable
def round_trip_family {x y : F} (γ : path x y) : ℝ → loop F :=
have key : ∀ {t}, x = γ.extend (min 0 t) := λ t, (γ.extend_of_le_zero $ min_le_left _ _).symm,
λ t, round_trip ((γ.truncate 0 t).cast key rfl)

lemma round_trip_family_continuous {x y : F} {γ : path x y} : continuous ↿(round_trip_family γ) :=
of_path_continuous_family _
  (path.trans_continuous_family _ (γ.truncate_const_continuous_family 0) _ $
    path.symm_continuous_family _ $ γ.truncate_const_continuous_family 0)

lemma round_trip_family_based_at {x y : F} {γ : path x y} : ∀ t, (round_trip_family γ) t 0 = x :=
λ t, round_trip_based_at

lemma round_trip_family_zero {x y : F} {γ : path x y} : (round_trip_family γ) 0 = of_path (path.refl x) :=
begin
  simp only [round_trip_family, round_trip, path.truncate_zero_zero, of_path],
  ext z,
  congr,
  ext t,
  simp [path.refl_symm]
end

lemma round_trip_family_one {x y : F} {γ : path x y} : (round_trip_family γ) 1 = round_trip γ :=
begin
  simp only [round_trip_family, round_trip, path.truncate_zero_one, of_path],
  refl
end

end loop
