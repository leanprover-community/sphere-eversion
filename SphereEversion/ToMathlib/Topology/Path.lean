import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Topology.Connected.PathConnected

open Set Function

open scoped Topology unitInterval

noncomputable section

variable {X X' Y Z : Type*} [TopologicalSpace X]
  [TopologicalSpace X'] [TopologicalSpace Y] [TopologicalSpace Z]

namespace Path

variable {x : X} {γ γ' : Path x x}

/-- A loop evaluated at `t / t` is equal to its endpoint. Note that `t / t = 0` for `t = 0`. -/
@[simp]
theorem extend_div_self (γ : Path x x) (t : ℝ) : γ.extend (t / t) = x := by
  by_cases h : t = 0 <;> simp [h]

/-- Concatenation of two loops which moves through the first loop on `[0, t₀]` and
through the second one on `[t₀, 1]`. All endpoints are assumed to be the same so that this
function is also well-defined for `t₀ ∈ {0, 1}`.
`strans` stands either for a *s*kewed transitivity, or a transitivity with different *s*peeds. -/
def strans (γ γ' : Path x x) (t₀ : I) : Path x x where
  toFun t := if t ≤ t₀ then γ.extend (t / t₀) else γ'.extend ((t - t₀) / (1 - t₀))
  continuous_toFun := by
    refine Continuous.if_le ?_ ?_ continuous_id continuous_const ?_
    · continuity
    · continuity
    · simp only [extend_div_self, Icc.mk_zero, zero_le_one, zero_div, forall_eq,
        extend_apply, Path.source, left_mem_Icc, sub_self]
  source' := by simp
  target' := by
    simp +contextual only [unitInterval.le_one'.ge_iff_eq.trans eq_comm,
      extend_div_self, Icc.coe_one, imp_true_iff, ite_eq_right_iff]

/-- Reformulate `strans` without using `extend`. This is useful to not have to prove that the
  arguments to `γ` lie in `I` after this. -/
theorem strans_def {x : X} {t₀ t : I} (γ γ' : Path x x) :
    γ.strans γ' t₀ t =
      if h : t ≤ t₀ then γ ⟨t / t₀, unitInterval.div_mem t.2.1 t₀.2.1 h⟩
      else γ' ⟨(t - t₀) / (1 - t₀),
        unitInterval.div_mem (sub_nonneg.mpr <| le_of_not_ge h) (sub_nonneg.mpr t₀.2.2)
          (sub_le_sub_right t.2.2 t₀)⟩ := by
  split_ifs with h <;> simp [strans, h, ← extend_apply]

@[simp]
theorem strans_of_ge {t t₀ : I} (h : t₀ ≤ t) :
    γ.strans γ' t₀ t = γ'.extend ((t - t₀) / (1 - t₀)) := by
  simp only [Path.coe_mk_mk, Path.strans, ite_eq_right_iff]
  intro h2; obtain rfl := le_antisymm h h2; simp

@[simp]
theorem strans_zero (γ γ' : Path x x) : γ.strans γ' 0 = γ' := by
  ext t
  simp +contextual only [strans_of_ge unitInterval.nonneg', Icc.coe_zero, div_one,
    extend_extends', sub_zero]

@[simp]
theorem strans_one {x : X} (γ γ' : Path x x) : γ.strans γ' 1 = γ := by
  ext t
  simp only [strans, unitInterval.le_one', Path.coe_mk_mk, if_pos, div_one, extend_extends',
    Icc.coe_one]

theorem strans_self {x : X} (γ γ' : Path x x) (t₀ : I) : γ.strans γ' t₀ t₀ = x := by
  simp only [strans, Path.coe_mk_mk, extend_div_self, if_pos, le_rfl]

@[simp]
theorem refl_strans_refl {x : X} {t₀ : I} : (refl x).strans (refl x) t₀ = refl x := by
  ext s
  simp [strans]

theorem subset_range_strans_left {x : X} {γ γ' : Path x x} {t₀ : I} (h : t₀ ≠ 0) :
    range γ ⊆ range (γ.strans γ' t₀) := by
  rintro _ ⟨t, rfl⟩
  use t * t₀
  simp [strans, unitInterval.mul_le_right, unitInterval.coe_ne_zero.mpr h]

theorem subset_range_strans_right {x : X} {γ γ' : Path x x} {t₀ : I} (h : t₀ ≠ 1) :
    range γ' ⊆ range (γ.strans γ' t₀) := by
  rintro _ ⟨t, rfl⟩
  have := mul_nonneg t.2.1 (sub_nonneg.mpr t₀.2.2)
  let t' : I := ⟨t₀ + t * (1 - t₀), add_nonneg t₀.2.1 this, by
      rw [add_comm, ← le_sub_iff_add_le]
      exact (mul_le_mul_of_nonneg_right t.2.2 <| sub_nonneg.mpr t₀.2.2).trans_eq (one_mul _)⟩
  have h2 : t₀ ≤ t' := le_add_of_nonneg_right this
  have h3 := sub_ne_zero.mpr (unitInterval.coe_ne_one.mpr h).symm
  use t'
  simp [h2, h3, t']

theorem range_strans_subset {x : X} {γ γ' : Path x x} {t₀ : I} :
    range (γ.strans γ' t₀) ⊆ range γ ∪ range γ' := by
  rintro _ ⟨t, rfl⟩
  by_cases h : t ≤ t₀
  · rw [strans_def, dif_pos h]; exact Or.inl (mem_range_self _)
  · rw [strans_def, dif_neg h]; exact Or.inr (mem_range_self _)

theorem Continuous.path_strans {X Y : Type*} [UniformSpace X]
    [LocallyCompactSpace X] [UniformSpace Y] {f : X → Y} {t : X → I} {s : X → I}
    {γ γ' : ∀ x, Path (f x) (f x)} (hγ : Continuous ↿γ) (hγ' : Continuous ↿γ')
    (hγ0 : ∀ ⦃x s⦄, t x = 0 → γ x s = f x) (hγ'1 : ∀ ⦃x s⦄, t x = 1 → γ' x s = f x)
    (ht : Continuous t) (hs : Continuous s) :
    Continuous fun x ↦ strans (γ x) (γ' x) (t x) (s x) := by
  have hγ0 : ∀ {x₀}, t x₀ = 0 →
      TendstoUniformly (fun x ↦ γ x) (fun _ ↦ f x₀) (𝓝 x₀) := fun h₀ ↦ by
    convert Continuous.tendstoUniformly (fun x ↦ γ x) hγ _; rw [hγ0 h₀]
  have hγ'1 : ∀ {x₀}, t x₀ = 1 →
      TendstoUniformly (fun x ↦ γ' x) (fun _ ↦ f x₀) (𝓝 x₀) := fun h₀ ↦ by
    convert Continuous.tendstoUniformly (fun x ↦ γ' x) hγ' _; rw [hγ'1 h₀]
  refine Continuous.if_le ?_ ?_ hs ht ?_
  · rw [continuous_iff_continuousAt]
    intro x
    refine (continuous_subtype_val.comp hs).continuousAt.comp_div_cases (fun x s ↦ (γ x).extend s)
      (continuous_subtype_val.comp ht).continuousAt ?_ ?_
    · intro _
      refine ContinuousAt.pathExtend _ ?_ continuousAt_snd
      exact hγ.continuousAt.comp (continuousAt_fst.fst.prodMk continuousAt_snd)
    · intro h
      have ht : t x = 0 := Subtype.ext h
      apply Filter.Tendsto.pathExtend
      rw [(projIcc_surjective _).filter_map_top, extend_zero]
      exact tendsto_prod_top_iff.mpr (hγ0 ht)
  · rw [continuous_iff_continuousAt]
    intro x
    refine (continuous_subtype_val.comp hs).sub (continuous_subtype_val.comp ht)
      |>.continuousAt.comp_div_cases (fun x s ↦ (γ' x).extend s)
      (continuous_const.sub <| continuous_subtype_val.comp ht).continuousAt ?_ ?_
    · intro _
      refine ContinuousAt.pathExtend _ ?_ continuousAt_snd
      exact hγ'.continuousAt.comp (continuousAt_fst.fst.prodMk continuousAt_snd)
    · intro h
      have ht : t x = 1 := Subtype.ext (sub_eq_zero.mp h).symm
      apply Filter.Tendsto.pathExtend
      rw [(projIcc_surjective _).filter_map_top, extend_zero]
      exact tendsto_prod_top_iff.mpr (hγ'1 ht)
  · rintro x h; rw [h, sub_self, zero_div, extend_div_self, extend_zero]

end Path
