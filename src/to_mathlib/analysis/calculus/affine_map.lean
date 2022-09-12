import analysis.calculus.affine_map

/-!

# Lemmas about interaction of `ball` and `homothety`

TODO Generalise these lemmas appropriately.

-/

open set function metric affine_map

variables {F : Type*} [normed_add_comm_group F] [normed_space ℝ F]

-- Unused
@[simp] lemma range_affine_equiv_ball {p c : F} {s r : ℝ} (hr : 0 < r) :
  range (λ (x : ball p s), c +ᵥ homothety p r (x : F)) = ball (c + p) (r * s) :=
begin
  ext,
  simp only [homothety_apply, dist_eq_norm, vsub_eq_sub, vadd_eq_add, mem_range,
    set_coe.exists, mem_ball, subtype.coe_mk, exists_prop],
  refine ⟨_, λ h, ⟨p + r⁻¹ • (x - (c + p)), _, _⟩⟩,
  { rintros ⟨y, h, rfl⟩,
    simpa [norm_smul, abs_eq_self.mpr hr.le] using (mul_lt_mul_left hr).mpr h, },
  { simpa [norm_smul, abs_eq_self.mpr hr.le] using (inv_mul_lt_iff hr).mpr h, },
  { simp [← smul_assoc, hr.ne.symm.is_unit.mul_inv_cancel], abel, },
end

@[simp] lemma norm_coe_ball_lt (r : ℝ) (x : ball (0 : F) r) : ∥(x : F)∥ < r :=
by { cases x with x hx, simpa using hx, }

lemma maps_to_homothety_ball (c : F) {r : ℝ} (hr : 0 < r) :
  maps_to (λ y, homothety c r⁻¹ y -ᵥ c) (ball c r) (ball 0 1) :=
begin
  intros y hy,
  replace hy : r⁻¹ * ∥y - c∥ < 1,
  { rw [← mul_lt_mul_left hr, ← mul_assoc, mul_inv_cancel hr.ne.symm, mul_one, one_mul],
    simpa [dist_eq_norm] using hy, },
  simp only [homothety_apply, vsub_eq_sub, vadd_eq_add, add_sub_cancel, mem_ball_zero_iff,
    norm_smul, real.norm_eq_abs, abs_eq_self.2 (inv_pos.mpr hr).le, hy],
end

lemma cont_diff_homothety {n : ℕ∞} (c : F) (r : ℝ) : cont_diff ℝ n (homothety c r) :=
(⟨homothety c r, homothety_continuous c r⟩ : F →A[ℝ] F).cont_diff
