import analysis.inner_product_space.calculus
import analysis.calculus.affine_map

variables {F : Type*} [normed_add_comm_group F] [normed_space ℝ F]

open set function metric affine_map

-- TODO Generalise + move
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

-- TODO Generalise + move
lemma cont_diff_homothety {n : ℕ∞} (c : F) (r : ℝ) : cont_diff ℝ n (homothety c r) :=
(⟨homothety c r, homothety_continuous c r⟩ : F →A[ℝ] F).cont_diff

-- TODO Generalise + move
@[simp] lemma norm_coe_ball_lt (r : ℝ) (x : ball (0 : F) r) : ∥(x : F)∥ < r :=
by { cases x with x hx, simpa using hx, }

open_locale classical

/- TODO Drop the below. It is superceded by `diffeomorph_to_nhd`.

/-- Provided `0 < r`, this is a diffeomorphism from `E` onto the open ball of radius `r` in `E`
centred at a point `c` and sending `0` to `c`.

The values for `r ≤ 0` are junk.

TODO: split this up. We should really prove that an affine equiv is a diffeomorphism, that
`homeomorph_unit_ball` is a smooth open embedding, and that composition of a smooth open embedding
with a diffeomorphism is a smooth open embedding. -/
def open_smooth_embedding_to_ball (c : E) (r : ℝ) :
  open_smooth_embedding 𝓘(ℝ, E) E 𝓘(ℝ, E) E :=
if hr : 0 < r then
{ to_fun := λ x, c +ᵥ homothety (0 : E) r (homeomorph_unit_ball x),
  inv_fun := (λ y, if hy : y ∈ ball (0 : E) 1 then homeomorph_unit_ball.symm ⟨y, hy⟩ else 0) ∘
    (λ y, (homothety c r⁻¹ y) -ᵥ c),
  left_inv' := λ x,
  begin
    simp [homothety_apply, norm_smul, abs_eq_self.mpr hr.le, ← mul_assoc, ← smul_assoc,
      hr.ne.symm.is_unit.inv_mul_cancel],
  end,
  right_inv' :=
  begin
    rintros y ⟨x, rfl⟩,
    simp [homothety_apply, norm_smul, abs_eq_self.mpr hr.le, ← mul_assoc, ← smul_assoc,
      hr.ne.symm.is_unit.inv_mul_cancel],
  end,
  open_map :=
  begin
    change is_open_map ((λ x, c + homothety (0 : E) r x) ∘ (coe : ball (0 : E) 1 → E) ∘ _),
    refine is_open_map.comp _ (is_open_ball.is_open_map_subtype_coe.comp
      homeomorph_unit_ball.is_open_map),
    exact (is_open_map_add_left c).comp (homothety_is_open_map 0 r hr.ne.symm),
  end,
  smooth_to := (cont_diff_const.add $ (cont_diff_homothety 0 r).comp
    cont_diff_homeomorph_unit_ball).cont_mdiff,
  smooth_inv := cont_diff_on.cont_mdiff_on
  begin
    change cont_diff_on ℝ ⊤ _ (range ((λ (x : ball (0 : E) 1), c +ᵥ homothety (0 : E) r (x : E)) ∘ _)),
    have : range (homeomorph_unit_ball : E → ball (0 : E) 1) = univ := range_eq_univ _,
    rw [range_comp, this, image_univ, range_affine_equiv_ball hr, add_zero],
    simp_rw [mul_one],
    refine cont_diff_on.comp (cont_diff_on_homeomorph_unit_ball_symm (λ y hy, dif_pos hy))
      (cont_diff.cont_diff_on _) (λ y hy, _),
    { simp only [homothety_apply, vsub_eq_sub, vadd_eq_add, add_sub_cancel],
      exact cont_diff_const.smul (cont_diff_id.sub cont_diff_const), },
    { rw [mem_ball, dist_eq_norm, ← mul_one r] at hy,
      simpa [homothety_apply, norm_smul, abs_eq_self.mpr hr.le] using (inv_mul_lt_iff hr).mpr hy, },
  end }
else  open_smooth_embedding.id 𝓘(ℝ, E) E

@[simp] lemma open_smooth_embedding_to_ball_apply_zero (c : E) {r : ℝ} (h : 0 < r) :
  open_smooth_embedding_to_ball c r 0 = c :=
by simp [open_smooth_embedding_to_ball, h]

@[simp] lemma range_open_smooth_embedding_to_ball (c : E) {r : ℝ} (h : 0 < r) :
  range (open_smooth_embedding_to_ball c r) = ball c r :=
begin
  simp only [open_smooth_embedding_to_ball, h, not_le, dif_neg, open_smooth_embedding.coe_mk],
  change range ((λ (x : ball (0 : E) 1), c +ᵥ homothety (0 : E) r (x : E)) ∘ _) = _,
  have : range (homeomorph_unit_ball : E → ball (0 : E) 1) = univ := range_eq_univ _,
  rw [range_comp, this, image_univ, range_affine_equiv_ball h, add_zero, mul_one],
end
-/

/-- This will be a homothety applied to `homeomorph_unit_ball` *except* that since we do not
assume an `inner_product_space` structure on `F` but merely a `normed_space` structure, we will
need to equip (a type alias for) `F` with an `inner_product_space`, and then use the equivalence
of norms in finite dimensions to obtain what we need. Note that
`range_diffeomorph_to_nhd_subset_ball` only asks for a subset condition. -/
def diffeomorph_to_nhd (c : F) (r : ℝ) :
  local_homeomorph F F :=
sorry

@[simp] lemma diffeomorph_to_nhd_source (c : F) (r : ℝ) :
  (diffeomorph_to_nhd c r).source = univ :=
sorry

@[simp] lemma diffeomorph_to_nhd_apply_zero (c : F) {r : ℝ} (h : 0 < r) :
  diffeomorph_to_nhd c r 0 = c :=
sorry

@[simp] lemma range_diffeomorph_to_nhd_subset_ball (c : F) {r : ℝ} (h : 0 < r) :
  range (diffeomorph_to_nhd c r) ⊆ ball c r :=
sorry

@[simp] lemma cont_diff_diffeomorph_to_nhd (c : F) (r : ℝ) {n : ℕ∞} :
  cont_diff ℝ n $ diffeomorph_to_nhd c r :=
sorry

@[simp] lemma cont_diff_diffeomorph_to_nhd_inv (c : F) (r : ℝ) {n : ℕ∞} :
  cont_diff_on ℝ n (diffeomorph_to_nhd c r).symm (diffeomorph_to_nhd c r).target :=
sorry
