import topology.path_connected

import to_mathlib.topology.misc

open set function int topological_space
open_locale big_operators topological_space topological_space unit_interval
noncomputable theory

variables {X X' Y Z : Type*} [topological_space X]
variables [topological_space X'] [topological_space Y] [topological_space Z]



namespace path

/-- A loop evaluated at `t / t` is equal to its endpoint. Note that `t / t = 0` for `t = 0`. -/
@[simp] lemma extend_div_self {x : X} (γ : path x x) (t : ℝ) :
  γ.extend (t / t) = x :=
by by_cases h : t = 0; simp [h]

/-- Concatenation of two loops which moves through the first loop on `[0, t₀]` and
through the second one on `[t₀, 1]`. All endpoints are assumed to be the same so that this
function is also well-defined for `t₀ ∈ {0, 1}`.
`strans` stands either for a *s*kewed transitivity, or a transitivity with different *s*peeds. -/
def strans {x : X} (γ γ' : path x x) (t₀ : I) : path x x :=
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

/-- Reformulate `strans` without using `extend`. This is useful to not have to prove that the
  arguments to `γ` lie in `I` after this. -/
lemma strans_def {x : X} (γ γ' : path x x) {t₀ t : I} :
  γ.strans γ' t₀ t =
  if h : t ≤ t₀ then γ ⟨t / t₀, unit_interval.div_mem t.2.1 t₀.2.1 h⟩ else
  γ' ⟨(t - t₀) / (1 - t₀), unit_interval.div_mem (sub_nonneg.mpr $ le_of_not_le h)
    (sub_nonneg.mpr t₀.2.2) (sub_le_sub_right t.2.2 t₀)⟩ :=
by split_ifs; simp [strans, h, ← extend_extends]

@[simp] lemma strans_zero {x : X} (γ γ' : path x x) : γ.strans γ' 0 = γ' :=
by { ext t, simp only [strans, path.coe_mk, if_pos, unit_interval.coe_zero,
  div_one, extend_extends',
  unit_interval.nonneg'.le_iff_eq, sub_zero, div_zero, extend_zero, ite_eq_right_iff,
  show (t : ℝ) = 0 ↔ t = 0, from (@subtype.ext_iff _ _ t 0).symm, path.source, eq_self_iff_true,
  implies_true_iff] {contextual := tt} }

@[simp] lemma strans_one {x : X} (γ γ' : path x x) : γ.strans γ' 1 = γ :=
by { ext t, simp only [strans, unit_interval.le_one', path.coe_mk, if_pos, div_one,
  extend_extends', unit_interval.coe_one] }

@[simp] lemma strans_of_ge {x : X} (γ γ' : path x x) {t₀ t : I} (h : t₀ ≤ t) :
  γ.strans γ' t₀ t = γ'.extend ((t - t₀) / (1 - t₀)) :=
begin
  simp only [path.coe_mk, path.strans, ite_eq_right_iff],
  intro h2, obtain rfl := le_antisymm h h2, simp
end

@[simp] lemma strans_self {x : X} (γ γ' : path x x) (t₀ : I) : γ.strans γ' t₀ t₀ = x :=
by { simp only [strans, path.coe_mk, extend_div_self, if_pos, le_rfl], }

@[simp] lemma refl_strans_refl {x : X} {t₀ : I} : (refl x).strans (refl x) t₀ = refl x :=
by { ext s, simp [strans] }

lemma subset_range_strans_left {x : X} {γ γ' : path x x} {t₀ : I} (h : t₀ ≠ 0) :
  range γ ⊆ range (γ.strans γ' t₀) :=
by { rintro _ ⟨t, rfl⟩, use t * t₀,
  simp [strans, unit_interval.mul_le_right, unit_interval.coe_ne_zero.mpr h] }

lemma subset_range_strans_right {x : X} {γ γ' : path x x} {t₀ : I} (h : t₀ ≠ 1) :
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

lemma range_strans_subset {x : X} {γ γ' : path x x} {t₀ : I} :
  range (γ.strans γ' t₀) ⊆ range γ ∪ range γ' :=
begin
  rintro _ ⟨t, rfl⟩,
  by_cases h : t ≤ t₀,
  { rw [strans_def, dif_pos h], exact or.inl (mem_range_self _) },
  { rw [strans_def, dif_neg h], exact or.inr (mem_range_self _) }
end

-- this lemma is easier if we reorder/reassociate the arguments
lemma _root_.continuous.path_strans {X Y : Type*} [uniform_space X] [separated_space X]
  [locally_compact_space X] [uniform_space Y] {f : X → Y} {t : X → I} {s : X → I}
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
      refine continuous_at.path_extend _ _ continuous_at_snd,
      exact hγ.continuous_at.comp (continuous_at_fst.fst.prod continuous_at_snd) },
    { intro h,
      have ht : t x = 0 := subtype.ext h,
      apply filter.tendsto.path_extend,
      dsimp only, rw [(proj_Icc_surjective _).filter_map_top, extend_zero],
      refine tendsto_prod_top_iff.mpr (hγ0 ht) } },
  { rw [continuous_iff_continuous_at],
    intro x,
    refine ((continuous_subtype_coe.comp hs).sub (continuous_subtype_coe.comp ht))
      .continuous_at.comp_div_cases (λ x s, (γ' x).extend s)
      (continuous_const.sub $ continuous_subtype_coe.comp ht).continuous_at _ _,
    { intro h,
      refine continuous_at.path_extend _ _ continuous_at_snd,
      exact hγ'.continuous_at.comp (continuous_at_fst.fst.prod continuous_at_snd) },
    { intro h,
      have ht : t x = 1 := subtype.ext (sub_eq_zero.mp h).symm,
      apply filter.tendsto.path_extend,
      dsimp only, rw [(proj_Icc_surjective _).filter_map_top, extend_zero],
      refine tendsto_prod_top_iff.mpr (hγ'1 ht) } },
  { rintro x h, rw [h, sub_self, zero_div, extend_div_self, extend_zero] },
end

end path
