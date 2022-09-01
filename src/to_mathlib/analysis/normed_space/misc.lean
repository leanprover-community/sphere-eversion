import analysis.inner_product_space.calculus
import analysis.calculus.affine_map

variables {F : Type*} [normed_add_comm_group F] [normed_space ℝ F]

open set function metric affine_map
open_locale classical
noncomputable theory

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

lemma local_equiv.range_eq_target_of_source_eq_univ {α β : Type*}
  (e : local_equiv α β) (h : e.source = univ) :
  range e = e.target :=
by { rw [← image_univ, ← h], exact e.image_source_eq_target, }

namespace inner_product_space

variables {E : Type*} [inner_product_space ℝ E]

/-- Provided `0 < r`, this is a diffeomorphism from `E` onto the open ball of radius `r` in `E`
centred at a point `c` and sending `0` to `c`.

The values for `r ≤ 0` are junk.

TODO Refactor this: clearly it should really be built along the following lines:
```
variables (c : F) {r : ℝ} (hr : 0 < r)
include hr

def ball_homeomorph_ball : ball (0 : F) 1 ≃ₜ ball c r :=
{ to_fun := λ x, ⟨c +ᵥ homothety (0 : F) r (x : F), by admit⟩,
  inv_fun := λ y, ⟨(homothety c r⁻¹ y) -ᵥ c, by admit⟩,
  left_inv := by admit,
  right_inv := by admit,
  continuous_to_fun := by admit,
  continuous_inv_fun := by admit, }

-- Not quite the right type but nearly there:
#check (homeomorph_unit_ball.trans (ball_homeomorph_ball c hr)).to_local_homeomorph
```
 -/
def diffeomorph_to_nhd (c : E) (r : ℝ) :
  local_homeomorph E E :=
if hr : 0 < r then
{ to_fun := λ x, c +ᵥ homothety (0 : E) r (homeomorph_unit_ball x),
  inv_fun := (λ y, if hy : y ∈ ball (0 : E) 1 then homeomorph_unit_ball.symm ⟨y, hy⟩ else 0) ∘
    (λ y, (homothety c r⁻¹ y) -ᵥ c),
  source := univ,
  target := ball c r,
  open_source := is_open_univ,
  open_target := is_open_ball,
  map_source' := λ x _,
  begin
    have hx : ∥(homeomorph_unit_ball x : E)∥ < 1,
    { rw ← dist_zero_right, exact (homeomorph_unit_ball x).property, },
    rw [← mul_lt_mul_left hr, mul_one] at hx,
    simp only [homothety_apply, vsub_eq_sub, sub_zero, vadd_eq_add, add_zero, mem_ball,
      dist_self_add_left, norm_smul, real.norm_eq_abs, abs_eq_self.2 hr.le, hx],
  end,
  map_target' := λ x h, mem_univ _,
  left_inv' := λ x, by simp [homothety_apply, norm_smul, abs_eq_self.mpr hr.le, ← mul_assoc,
    ← smul_assoc, hr.ne.symm.is_unit.inv_mul_cancel],
  right_inv' := λ y hy,
  begin
    replace hy : r⁻¹ * ∥y - c∥ < 1,
    { rw [← mul_lt_mul_left hr, ← mul_assoc, mul_inv_cancel hr.ne.symm, mul_one, one_mul],
      simpa [dist_eq_norm] using hy, },
    simp [homothety_apply, norm_smul, abs_eq_self.2 hr.le, ← smul_assoc, mul_inv_cancel hr.ne.symm,
      hy],
  end,
  continuous_to_fun := continuous_iff_continuous_on_univ.mp $ continuous_const.add $
    (homothety_continuous 0 r).comp $ continuous_induced_dom.comp homeomorph_unit_ball.continuous,
  continuous_inv_fun :=
  begin
    refine continuous_on.comp _ (continuous.continuous_on _) (maps_to_homothety_ball c hr),
    { rw continuous_on_iff_continuous_restrict,
      convert homeomorph_unit_ball.symm.continuous, ext, simp, },
    { simp only [homothety_apply, vsub_eq_sub, vadd_eq_add, add_sub_cancel],
      exact continuous_const.smul (continuous_id.sub continuous_const), },
  end }
else local_homeomorph.refl E

@[simp] lemma diffeomorph_to_nhd_source (c : E) (r : ℝ) :
  (diffeomorph_to_nhd c r).source = univ :=
begin
  by_cases hr : 0 < r,
  { rw [diffeomorph_to_nhd, dif_pos hr], },
  { rw [diffeomorph_to_nhd, dif_neg hr, local_homeomorph.refl_local_equiv,
      local_equiv.refl_source], },
end

@[simp] lemma diffeomorph_to_nhd_apply_zero (c : E) {r : ℝ} (hr : 0 < r) :
  diffeomorph_to_nhd c r 0 = c :=
by simp only [diffeomorph_to_nhd, dif_pos hr, vadd_eq_add, local_homeomorph.mk_coe,
    local_equiv.coe_mk, coe_homeomorph_unit_ball_apply_zero, homothety_apply_same, add_zero]

@[simp] lemma range_diffeomorph_to_nhd_eq_ball (c : E) {r : ℝ} (hr : 0 < r) :
  range (diffeomorph_to_nhd c r) = ball c r :=
by erw [local_equiv.range_eq_target_of_source_eq_univ _ (diffeomorph_to_nhd_source c r),
    diffeomorph_to_nhd, dif_pos hr]

@[simp] lemma cont_diff_diffeomorph_to_nhd (c : E) (r : ℝ) {n : ℕ∞} :
  cont_diff ℝ n $ diffeomorph_to_nhd c r :=
begin
  by_cases hr : 0 < r,
  { rw [diffeomorph_to_nhd, dif_pos hr],
    exact cont_diff_const.add ((cont_diff_homothety 0 r).comp cont_diff_homeomorph_unit_ball), },
  { rw [diffeomorph_to_nhd, dif_neg hr],
    exact cont_diff_id, },
end

@[simp] lemma cont_diff_diffeomorph_to_nhd_inv (c : E) (r : ℝ) {n : ℕ∞} :
  cont_diff_on ℝ n (diffeomorph_to_nhd c r).symm (diffeomorph_to_nhd c r).target :=
begin
  by_cases hr : 0 < r,
  { rw [diffeomorph_to_nhd, dif_pos hr],
    have aux : ball c r ⊆ (λ (x : E), (λ (y : E), homothety c r⁻¹ y -ᵥ c) x) ⁻¹' (ball 0 1) :=
      maps_to_homothety_ball c hr,
    refine cont_diff_on.comp _ (cont_diff.cont_diff_on _) aux,
    { exact cont_diff_on_homeomorph_unit_ball_symm (λ y hy, dif_pos hy), },
    { simp only [homothety_apply, vsub_eq_sub, vadd_eq_add, add_sub_cancel],
      exact cont_diff_const.smul (cont_diff_id.sub cont_diff_const), }, },
  { rw [diffeomorph_to_nhd, dif_neg hr],
    exact cont_diff_on_id, },
end

end inner_product_space

variables (F) [finite_dimensional ℝ F]

/-- A type alias which we will endow with an `inner_product_space` structure whose underlying
`module ℝ` structure coincides with the one that `F` already carries. -/
def l2 := F

instance : inner_product_space ℝ (l2 F) := sorry

def self_equiv_l2 : F ≃L[ℝ] l2 F :=
linear_equiv.to_continuous_linear_equiv
{ to_fun    := id,
  inv_fun   := id,
  map_add'  := sorry,
  map_smul' := sorry,
  left_inv  := λ x, rfl,
  right_inv := λ x, rfl, }

@[simp] lemma self_equiv_l2_image_univ :
  self_equiv_l2 F '' univ = univ :=
begin
  rw image_univ,
  exact (self_equiv_l2 F : F ≃ l2 F).range_eq_univ,
end

variables {F}

/-- A variant of `inner_product_space.diffeomorph_to_nhd` which provides a function satisfying the
weaker condition `range_diffeomorph_to_nhd_subset_ball` but which applies to any `normed_space`.

In fact one could demand this stronger property but it would be more work and we don't need it. -/
def diffeomorph_to_nhd (c : F) (r : ℝ) :
  local_homeomorph F F :=
if hr : 0 < r then
begin
  let B := (self_equiv_l2 F) '' (ball c r),
  let f := (self_equiv_l2 F).to_homeomorph,
  have hB : is_open B := f.is_open_map _ is_open_ball,
  have hc : self_equiv_l2 F c ∈ B := mem_image_of_mem f (mem_ball_self hr),
  let ε := classical.some (metric.is_open_iff.mp hB _ hc),
  exact (f.trans_local_homeomorph (inner_product_space.diffeomorph_to_nhd
    (self_equiv_l2 F c) ε)).trans_homeomorph f.symm,
end
else local_homeomorph.refl F

@[simp] lemma diffeomorph_to_nhd_source (c : F) (r : ℝ) :
  (diffeomorph_to_nhd c r).source = univ :=
begin
  by_cases hr : 0 < r,
  { simp [diffeomorph_to_nhd, dif_pos hr], },
  { rw [diffeomorph_to_nhd, dif_neg hr, local_homeomorph.refl_local_equiv,
      local_equiv.refl_source], },
end

@[simp] lemma diffeomorph_to_nhd_apply_zero (c : F) {r : ℝ} (hr : 0 < r) :
  diffeomorph_to_nhd c r 0 = c :=
begin
  rw [diffeomorph_to_nhd, dif_pos hr],
  let B := (self_equiv_l2 F) '' (ball c r),
  let f := (self_equiv_l2 F).to_homeomorph,
  have hB : is_open B := f.is_open_map _ is_open_ball,
  have hc : self_equiv_l2 F c ∈ B := mem_image_of_mem f (mem_ball_self hr),
  let ε := classical.some (metric.is_open_iff.mp hB _ hc),
  have hε : 0 < ε := classical.some (classical.some_spec (metric.is_open_iff.mp hB _ hc)),
  change (f.trans_local_homeomorph (inner_product_space.diffeomorph_to_nhd
    (self_equiv_l2 F c) ε)).trans_homeomorph f.symm 0 = c,
  simp [hε],
end

@[simp] lemma range_diffeomorph_to_nhd_subset_ball (c : F) {r : ℝ} (hr : 0 < r) :
  range (diffeomorph_to_nhd c r) ⊆ ball c r :=
begin
  rw [diffeomorph_to_nhd, dif_pos hr, ← image_univ],
  let B := (self_equiv_l2 F) '' (ball c r),
  let f := (self_equiv_l2 F).to_homeomorph,
  have hB : is_open B := f.is_open_map _ is_open_ball,
  have hc : self_equiv_l2 F c ∈ B := mem_image_of_mem f (mem_ball_self hr),
  let ε := classical.some (metric.is_open_iff.mp hB _ hc),
  have hε : 0 < ε := classical.some (classical.some_spec (metric.is_open_iff.mp hB _ hc)),
  have hε' : ball (self_equiv_l2 F c) ε ⊆ B :=
    classical.some_spec (classical.some_spec (metric.is_open_iff.mp hB _ hc)),
  change f.symm ∘ (inner_product_space.diffeomorph_to_nhd (self_equiv_l2 F c) ε ∘ f) '' univ ⊆ _,
  rw [image_comp f.symm _, image_comp _ f],
  erw [self_equiv_l2_image_univ, image_univ,
    inner_product_space.range_diffeomorph_to_nhd_eq_ball _ hε],
  suffices : ball c r = f.symm '' (f '' ball c r), { rw this, exact monotone_image hε', },
  rw ← image_comp,
  simp,
end

@[simp] lemma cont_diff_diffeomorph_to_nhd (c : F) (r : ℝ) {n : ℕ∞} :
  cont_diff ℝ n $ diffeomorph_to_nhd c r :=
begin
  by_cases hr : 0 < r,
  { rw [diffeomorph_to_nhd, dif_pos hr],
    exact (self_equiv_l2 F).symm.cont_diff.comp
      ((inner_product_space.cont_diff_diffeomorph_to_nhd _ _).comp (self_equiv_l2 F).cont_diff), },
  { rw [diffeomorph_to_nhd, dif_neg hr],
    exact cont_diff_id, },
end

@[simp] lemma cont_diff_diffeomorph_to_nhd_inv (c : F) (r : ℝ) {n : ℕ∞} :
  cont_diff_on ℝ n (diffeomorph_to_nhd c r).symm (diffeomorph_to_nhd c r).target :=
begin
by_cases hr : 0 < r,
  { rw [diffeomorph_to_nhd, dif_pos hr],

    sorry, },
  { rw [diffeomorph_to_nhd, dif_neg hr],
    exact cont_diff_on_id, },
end
