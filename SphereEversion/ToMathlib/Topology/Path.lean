import Mathlib.Topology.PathConnected
import SphereEversion.ToMathlib.Topology.Misc

open Set Function Int TopologicalSpace

open scoped BigOperators Topology unitInterval

noncomputable section

variable {X X' Y Z : Type _} [TopologicalSpace X]

variable [TopologicalSpace X'] [TopologicalSpace Y] [TopologicalSpace Z]

namespace Path

variable {x : X} {γ γ' : Path x x} {t₀ t : I}

/-- A loop evaluated at `t / t` is equal to its endpoint. Note that `t / t = 0` for `t = 0`. -/
@[simp]
theorem extend_div_self (γ : Path x x) (t : ℝ) : γ.extend (t / t) = x := by
  by_cases h : t = 0 <;> simp [h]

/-- Concatenation of two loops which moves through the first loop on `[0, t₀]` and
through the second one on `[t₀, 1]`. All endpoints are assumed to be the same so that this
function is also well-defined for `t₀ ∈ {0, 1}`.
`strans` stands either for a *s*kewed transitivity, or a transitivity with different *s*peeds. -/
def strans (γ γ' : Path x x) (t₀ : I) : Path x x
    where
  toFun t := if t ≤ t₀ then γ.extend (t / t₀) else γ'.extend ((t - t₀) / (1 - t₀))
  continuous_toFun :=
    by
    refine'
      Continuous.if_le _ _ continuous_id continuous_const
        (by
          simp only [extend_div_self, Icc.mk_zero, zero_le_one, id.def, zero_div, forall_eq,
            extend_extends, Path.source, left_mem_Icc, sub_self])
    -- TODO: the following are provable by `continuity` but it is too slow
    exacts [γ.continuous_extend.comp (continuous_subtype_coe.div_const _),
      γ'.continuous_extend.comp ((continuous_subtype_coe.sub continuous_const).div_const _)]
  source' := by
    simp only [unitInterval.nonneg', Icc.coe_zero, Icc.mk_zero, zero_le_one, if_true, zero_div,
      comp_app, extend_extends, Path.source, left_mem_Icc]
  target' := by
    simp (config := { contextual := true }) only [unit_interval.le_one'.le_iff_eq.trans eq_comm,
      extend_div_self, Icc.coe_one, imp_true_iff, eq_self_iff_true, comp_app, ite_eq_right_iff]

/-- Reformulate `strans` without using `extend`. This is useful to not have to prove that the
  arguments to `γ` lie in `I` after this. -/
theorem strans_def (γ γ' : Path x x) :
    γ.strans γ' t₀ t =
      if h : t ≤ t₀ then γ ⟨t / t₀, unitInterval.div_mem t.2.1 t₀.2.1 h⟩
      else
        γ'
          ⟨(t - t₀) / (1 - t₀),
            unitInterval.div_mem (sub_nonneg.mpr <| le_of_not_le h) (sub_nonneg.mpr t₀.2.2)
              (sub_le_sub_right t.2.2 t₀)⟩ :=
  by split_ifs <;> simp [strans, h, ← extend_extends]

@[simp]
theorem strans_of_ge (h : t₀ ≤ t) : γ.strans γ' t₀ t = γ'.extend ((t - t₀) / (1 - t₀)) :=
  by
  simp only [Path.coe_mk_mk, Path.strans, ite_eq_right_iff]
  intro h2; obtain rfl := le_antisymm h h2; simp

theorem UnitInterval.zero_le (x : I) : 0 ≤ x :=
  x.Prop.1

@[simp]
theorem strans_zero (γ γ' : Path x x) : γ.strans γ' 0 = γ' := by ext t;
  simp (config := { contextual := true }) only [strans_of_ge (unit_interval.zero_le t),
    Icc.coe_zero, div_one, extend_extends', unit_interval.nonneg'.le_iff_eq, sub_zero, div_zero,
    extend_zero, ite_eq_right_iff, show (t : ℝ) = 0 ↔ t = 0 from (@Subtype.ext_iff _ _ t 0).symm,
    Path.source, eq_self_iff_true, imp_true_iff]

@[simp]
theorem strans_one {x : X} (γ γ' : Path x x) : γ.strans γ' 1 = γ := by ext t;
  simp only [strans, unitInterval.le_one', Path.coe_mk_mk, if_pos, div_one, extend_extends',
    Icc.coe_one]

@[simp]
theorem strans_self {x : X} (γ γ' : Path x x) (t₀ : I) : γ.strans γ' t₀ t₀ = x := by
  simp only [strans, Path.coe_mk_mk, extend_div_self, if_pos, le_rfl]

@[simp]
theorem refl_strans_refl {x : X} {t₀ : I} : (refl x).strans (refl x) t₀ = refl x := by ext s;
  simp [strans]

theorem subset_range_strans_left {x : X} {γ γ' : Path x x} {t₀ : I} (h : t₀ ≠ 0) :
    range γ ⊆ range (γ.strans γ' t₀) := by
  rintro _ ⟨t, rfl⟩; use t * t₀
  simp [strans, unitInterval.mul_le_right, unit_interval.coe_ne_zero.mpr h]

theorem subset_range_strans_right {x : X} {γ γ' : Path x x} {t₀ : I} (h : t₀ ≠ 1) :
    range γ' ⊆ range (γ.strans γ' t₀) := by
  rintro _ ⟨t, rfl⟩
  have := mul_nonneg t.2.1 (sub_nonneg.mpr t₀.2.2)
  let t' : I :=
    ⟨t₀ + t * (1 - t₀), add_nonneg t₀.2.1 this,
      by
      rw [add_comm, ← le_sub_iff_add_le]
      refine' (mul_le_mul_of_nonneg_right t.2.2 <| sub_nonneg.mpr t₀.2.2).trans_eq (one_mul _)⟩
  have h2 : t₀ ≤ t' := le_add_of_nonneg_right this
  have h3 := sub_ne_zero.mpr (unit_interval.coe_ne_one.mpr h).symm
  use t'
  simp [h2, unit_interval.coe_ne_one.mpr h, h3]

theorem range_strans_subset {x : X} {γ γ' : Path x x} {t₀ : I} :
    range (γ.strans γ' t₀) ⊆ range γ ∪ range γ' :=
  by
  rintro _ ⟨t, rfl⟩
  by_cases h : t ≤ t₀
  · rw [strans_def, dif_pos h]; exact Or.inl (mem_range_self _)
  · rw [strans_def, dif_neg h]; exact Or.inr (mem_range_self _)

theorem Continuous.path_strans {X Y : Type _} [UniformSpace X] [SeparatedSpace X]
    [LocallyCompactSpace X] [UniformSpace Y] {f : X → Y} {t : X → I} {s : X → I}
    {γ γ' : ∀ x, Path (f x) (f x)} (hγ : Continuous ↿γ) (hγ' : Continuous ↿γ')
    (hγ0 : ∀ ⦃x s⦄, t x = 0 → γ x s = f x) (hγ'1 : ∀ ⦃x s⦄, t x = 1 → γ' x s = f x)
    (ht : Continuous t) (hs : Continuous s) : Continuous fun x => strans (γ x) (γ' x) (t x) (s x) :=
  by
  have hγ0 : ∀ {x₀}, t x₀ = 0 → TendstoUniformly (fun x => γ x) (fun _ => f x₀) (𝓝 x₀) :=
    by
    intro x₀ hx₀; convert Continuous.tendstoUniformly (fun x => γ x) hγ _
    ext t; rw [hγ0 hx₀]
  have hγ'1 : ∀ {x₀}, t x₀ = 1 → TendstoUniformly (fun x => γ' x) (fun _ => f x₀) (𝓝 x₀) :=
    by
    intro x₀ hx₀; convert Continuous.tendstoUniformly (fun x => γ' x) hγ' _
    ext t; rw [hγ'1 hx₀]
  refine' Continuous.if_le _ _ hs ht _
  · rw [continuous_iff_continuousAt]
    intro x
    refine'
      (continuous_subtype_coe.comp hs).ContinuousAt.comp_div_cases (fun x s => (γ x).extend s)
        (continuous_subtype_coe.comp ht).ContinuousAt _ _
    · intro h
      refine' ContinuousAt.path_extend _ _ continuousAt_snd
      exact hγ.continuous_at.comp (continuous_at_fst.fst.prod continuousAt_snd)
    · intro h
      have ht : t x = 0 := Subtype.ext h
      apply Filter.Tendsto.path_extend
      dsimp only; rw [(proj_Icc_surjective _).filter_map_top, extend_zero]
      refine' tendsto_prod_top_iff.mpr (hγ0 ht)
  · rw [continuous_iff_continuousAt]
    intro x
    refine'
      ((continuous_subtype_coe.comp hs).sub
              (continuous_subtype_coe.comp ht)).ContinuousAt.comp_div_cases
        (fun x s => (γ' x).extend s)
        (continuous_const.sub <| continuous_subtype_coe.comp ht).ContinuousAt _ _
    · intro h
      refine' ContinuousAt.path_extend _ _ continuousAt_snd
      exact hγ'.continuous_at.comp (continuous_at_fst.fst.prod continuousAt_snd)
    · intro h
      have ht : t x = 1 := Subtype.ext (sub_eq_zero.mp h).symm
      apply Filter.Tendsto.path_extend
      dsimp only; rw [(proj_Icc_surjective _).filter_map_top, extend_zero]
      refine' tendsto_prod_top_iff.mpr (hγ'1 ht)
  · rintro x h; rw [h, sub_self, zero_div, extend_div_self, extend_zero]

end Path

