import Mathlib.Analysis.Calculus.AddTorsor.AffineMap

/-!

# Lemmas about interaction of `ball` and `homothety`

TODO Generalise these lemmas appropriately.

-/


open Set Function Metric AffineMap

variable {F : Type*} [NormedAddCommGroup F]

-- Unused
-- @[simp]
-- theorem range_affine_equiv_ball {p c : F} {s r : ℝ} (hr : 0 < r) :
--     (range fun x : ball p s ↦ c +ᵥ homothety p r (x : F)) = ball (c + p) (r * s) := by
--   ext
--   simp only [homothety_apply, dist_eq_norm, vsub_eq_sub, vadd_eq_add, mem_range, SetCoe.exists,
--     mem_ball, Subtype.coe_mk, exists_prop]
--   refine ⟨?_, fun h ↦ ⟨p + r⁻¹ • (x - (c + p)), ?_, ?_⟩⟩
--   · rintro ⟨y, h, rfl⟩
--     simpa [norm_smul, abs_eq_self.mpr hr.le] using (mul_lt_mul_left hr).mpr h
--   · simpa [norm_smul, abs_eq_self.mpr hr.le] using (inv_mul_lt_iff hr).mpr h
--   · simp [← smul_assoc, hr.ne.symm.is_unit.mul_inv_cancel]; abel

@[simp]
theorem norm_coe_ball_lt (r : ℝ) (x : ball (0 : F) r) : ‖(x : F)‖ < r := by
  obtain ⟨x, hx⟩ := x
  simpa using hx

variable [NormedSpace ℝ F]

theorem mapsTo_homothety_ball (c : F) {r : ℝ} (hr : 0 < r) :
    MapsTo (fun y ↦ homothety c r⁻¹ y -ᵥ c) (ball c r) (ball 0 1) := fun y hy ↦ by
  replace hy : r⁻¹ * ‖y - c‖ < 1 := by
    rw [← mul_lt_mul_iff_right₀ hr, ← mul_assoc, mul_inv_cancel₀ hr.ne.symm, mul_one, one_mul]
    simpa [dist_eq_norm] using hy
  simp only [homothety_apply, vsub_eq_sub, vadd_eq_add, add_sub_cancel_right, mem_ball_zero_iff,
    norm_smul, Real.norm_eq_abs, abs_eq_self.2 (inv_pos.mpr hr).le, hy]

theorem contDiff_homothety {n : ℕ∞} (c : F) (r : ℝ) : ContDiff ℝ n (homothety c r) :=
  (⟨homothety c r, homothety_continuous c r⟩ : F →ᴬ[ℝ] F).contDiff
