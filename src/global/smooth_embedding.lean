import topology.metric_space.hausdorff_distance
import topology.uniform_space.compact_separated
import geometry.manifold.cont_mdiff
import analysis.inner_product_space.calculus
import analysis.calculus.affine_map
import global.indexing
import to_mathlib.topology.paracompact
import to_mathlib.topology.local_homeomorph
import to_mathlib.geometry.manifold.charted_space

noncomputable theory

open set equiv
open_locale manifold topological_space

/-- A variant of `is_compact.exists_forall_le` for real-valued functions that does not require the
assumption `s.nonempty`.

TODO Move -/
lemma is_compact.exists_forall_le' {β : Type*} [topological_space β]
  {s : set β} (hs : is_compact s)
  {f : β → ℝ} (hf : continuous_on f s) {a : ℝ} (hf' : ∀ b ∈ s, a < f b) :
  ∃ a', a < a' ∧ ∀ b ∈ s, a' ≤ f b :=
begin
  rcases s.eq_empty_or_nonempty with rfl | hs',
  { exact ⟨a + 1, by simp only [lt_add_iff_pos_right, zero_lt_one], λ b hb, by simpa using hb⟩, },
  { obtain ⟨x, hx, hx'⟩ := hs.exists_forall_le hs' hf,
    exact ⟨f x, hf' x hx, hx'⟩, },
end

section general
variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
  {H : Type*} [topological_space H]
  (I : model_with_corners 𝕜 E H)
  (M : Type*) [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
  {E' : Type*} [normed_add_comm_group E'] [normed_space 𝕜 E']
  {H' : Type*} [topological_space H']
  (I' : model_with_corners 𝕜 E' H')
  (M' : Type*) [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M']

structure open_smooth_embedding  :=
(to_fun : M → M')
(inv_fun : M' → M)
(left_inv'   : ∀{x}, inv_fun (to_fun x) = x)
(right_inv'  : ∀{x}, x ∈ range to_fun → to_fun (inv_fun x) = x)
(open_map : is_open_map to_fun)
(smooth_to : smooth I I' to_fun)
(smooth_inv : smooth_on I' I inv_fun (range to_fun))

instance : has_coe_to_fun (open_smooth_embedding I M I' M') (λ _, M → M') :=
⟨open_smooth_embedding.to_fun⟩

namespace open_smooth_embedding

variables {I I' M M'} (f : open_smooth_embedding I M I' M')

@[simp] lemma coe_mk (f g h₁ h₂ h₃ h₄ h₅) :
  ⇑(⟨f, g, h₁, h₂, h₃, h₄, h₅⟩ : open_smooth_embedding I M I' M') = f :=
rfl

@[simp] lemma left_inv (x : M) : f.inv_fun (f x) = x := by apply f.left_inv'

@[simp] lemma inv_fun_comp_coe : f.inv_fun ∘ f = id := funext f.left_inv

@[simp] lemma right_inv {y : M'} (hy : y ∈ range f) : f (f.inv_fun y) = y := f.right_inv' hy

lemma coe_comp_inv_fun_eventually_eq (x : M) : f ∘ f.inv_fun =ᶠ[𝓝 (f x)] id :=
filter.eventually_of_mem (f.open_map.range_mem_nhds x) $ λ y hy, f.right_inv' hy

protected lemma continuous : continuous f := f.smooth_to.continuous

lemma is_open_range : is_open (range f) :=
f.open_map.is_open_range

lemma smooth_at_inv {y : M'} (hy : y ∈ range f) : smooth_at I' I f.inv_fun y :=
(f.smooth_inv y hy).cont_mdiff_at $ f.is_open_range.mem_nhds hy

/- Note that we are slightly abusing the fact that `tangent_space I x` and
`tangent_space I (f.inv_fun (f x))` are both definitionally `E` below. -/
def fderiv (x : M) : tangent_space I x ≃L[𝕜] tangent_space I' (f x) :=
have h₁ : mdifferentiable_at I' I f.inv_fun (f x) := ((f.smooth_inv (f x) (mem_range_self x)
  ).mdifferentiable_within_at le_top).mdifferentiable_at (f.open_map.range_mem_nhds x),
have h₂ : mdifferentiable_at I I' f x := f.smooth_to.cont_mdiff.mdifferentiable le_top _,
continuous_linear_equiv.equiv_of_inverse
  (mfderiv I I' f x)
  (mfderiv I' I f.inv_fun (f x))
begin
  intros v,
  rw [← continuous_linear_map.comp_apply, ← mfderiv_comp x h₁ h₂, f.inv_fun_comp_coe, mfderiv_id,
    continuous_linear_map.coe_id', id.def],
end
begin
  intros v,
  have hx : x = f.inv_fun (f x), { rw f.left_inv, },
  have hx' : f (f.inv_fun (f x)) = f x, { rw f.left_inv, },
  rw hx at h₂,
  rw [hx, hx', ← continuous_linear_map.comp_apply, ← mfderiv_comp (f x) h₂ h₁, ((has_mfderiv_at_id
    I' (f x)).congr_of_eventually_eq (f.coe_comp_inv_fun_eventually_eq x)).mfderiv,
    continuous_linear_map.coe_id', id.def],
end

@[simp] lemma fderiv_coe (x : M) :
  (f.fderiv x : tangent_space I x →L[𝕜] tangent_space I' (f x)) = mfderiv I I' f x :=
by { ext, refl }

@[simp] lemma fderiv_symm_coe (x : M) :
  ((f.fderiv x).symm : tangent_space I' (f x) →L[𝕜] tangent_space I x) =
  mfderiv I' I f.inv_fun (f x) :=
by { ext, refl }

lemma fderiv_symm_coe' {x : M'} (hx : x ∈ range f) :
  ((f.fderiv (f.inv_fun x)).symm : tangent_space I' (f (f.inv_fun x)) →L[𝕜]
    tangent_space I (f.inv_fun x)) =
  (mfderiv I' I f.inv_fun x : tangent_space I' x →L[𝕜] tangent_space I (f.inv_fun x)) :=
by rw [fderiv_symm_coe, f.right_inv hx]

variables (I M)

/-- The identity map is a smooth open embedding. -/
@[simps] def id : open_smooth_embedding I M I M :=
{ to_fun := id,
  inv_fun := id,
  left_inv' := λ x, rfl,
  right_inv' := λ x hx, rfl,
  open_map := is_open_map.id,
  smooth_to := smooth_id,
  smooth_inv := smooth_on_id }

end open_smooth_embedding

end general

section without_boundary

open metric (hiding mem_nhds_iff) function

universe u

variables
  {E : Type*} [inner_product_space ℝ E]
  (M : Type u) [topological_space M] [charted_space E M] [smooth_manifold_with_corners 𝓘(ℝ, E) M]
  [t2_space M] [locally_compact_space M] [sigma_compact_space M]

/- Clearly should be generalised. Maybe what we really want is a theory of local diffeomorphisms. -/
def open_smooth_embedding_of_subset_chart_target {x : M}
  {f : open_smooth_embedding 𝓘(ℝ, E) E 𝓘(ℝ, E) E} (hf : range f ⊆ (chart_at E x).target) :
  open_smooth_embedding 𝓘(ℝ, E) E 𝓘(ℝ, E) M :=
{ to_fun := (chart_at E x).symm ∘ f,
  inv_fun := f.inv_fun ∘ (chart_at E x),
  left_inv' := λ y, by simp [hf (mem_range_self y)],
  right_inv' := by { rintros - ⟨y, rfl⟩, simp [hf (mem_range_self y)], },
  open_map := λ u hu,
  begin
    rw image_comp,
    apply local_homeomorph.image_open_of_open _ (f.open_map _ hu),
    rw ← image_univ at hf,
    exact (monotone_image (subset_univ u)).trans hf,
  end,
  smooth_to := cont_mdiff_on_chart_symm.comp_cont_mdiff f.smooth_to (range_subset_iff.mp hf),
  smooth_inv :=
  begin
    have hf' : range ((chart_at E x).symm ∘ f) ⊆ (chart_at E x) ⁻¹' range f,
    { rw [range_comp, ← image_subset_iff],
      exact (local_equiv.image_symm_image_of_subset_target _ hf).subset },
    refine f.smooth_inv.comp _ hf',
    have hf'' : range ((chart_at E x).symm ∘ f) ⊆ (chart_at E x).source,
    { rw [range_comp, ← local_equiv.symm_image_target_eq_source],
      exact (monotone_image hf).trans subset.rfl, },
    exact cont_mdiff_on_chart.mono hf'',
  end }

@[simp] lemma coe_open_smooth_embedding_of_subset_chart_target {x : M}
  {f : open_smooth_embedding 𝓘(ℝ, E) E 𝓘(ℝ, E) E} (hf : range f ⊆ (chart_at E x).target) :
  (open_smooth_embedding_of_subset_chart_target M hf : E → M) = (chart_at E x).symm ∘ f :=
rfl

open affine_map

-- TODO Generalise + move
@[simp] lemma range_affine_equiv_ball {p c : E} {s r : ℝ} (hr : 0 < r) :
  range (λ (x : ball p s), c +ᵥ homothety p r (x : E)) = ball (c + p) (r * s) :=
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
lemma cont_diff_homothety {n : ℕ∞} (c : E) (r : ℝ) : cont_diff ℝ n (homothety c r) :=
(⟨homothety c r, homothety_continuous c r⟩ : E →A[ℝ] E).cont_diff

-- TODO Generalise + move
@[simp] lemma norm_coe_ball_lt (r : ℝ) (x : ball (0 : E) r) : ∥(x : E)∥ < r :=
by { cases x with x hx, simpa using hx, }

open_locale classical

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

variables (E) {M}

lemma nice_atlas'
  {ι : Type*} {s : ι → set M} (s_op : ∀ j, is_open $ s j) (cov : (⋃ j, s j) = univ)
  (U : set E) (hU₁ : (0 : E) ∈ U) (hU₂ : is_open U) :
  ∃ (ι' : Type u) (t : set ι') (φ : t → open_smooth_embedding 𝓘(ℝ, E) E 𝓘(ℝ, E) M),
  t.countable ∧
  (∀ i, ∃ j, range (φ i) ⊆ s j) ∧
  locally_finite (λ i, range (φ i)) ∧
  (⋃ i, φ i '' U) = univ :=
begin
  let W : M → ℝ → set M := λ x r,
    (chart_at E x).symm ∘ open_smooth_embedding_to_ball (chart_at E x x) r '' U,
  let B : M → ℝ → set M := charted_space.ball E,
  let p : M → ℝ → Prop :=
    λ x r, 0 < r ∧ ball (chart_at E x x) r ⊆ (chart_at E x).target ∧ ∃ j, B x r ⊆ s j,
  have hW₀ : ∀ x r, p x r → x ∈ W x r := λ x r h, ⟨0, hU₁, by simp [h.1]⟩,
  have hW₁ : ∀ x r, p x r → is_open (W x r),
  { rintros x r ⟨h₁, h₂, -, -⟩,
    simp only [W],
    have aux :
      open_smooth_embedding_to_ball (chart_at E x x) r '' U ⊆ (chart_at E x).target :=
      subset.trans ((image_subset_range _ _).trans (by simp [h₁])) h₂,
    rw [image_comp, local_homeomorph.is_open_symm_image_iff_of_subset_target _ aux],
    exact open_smooth_embedding.open_map _ _ hU₂, },
  have hB : ∀ x, (𝓝 x).has_basis (p x) (B x) :=
    λ x, charted_space.nhds_has_basis_balls_of_open_cov E x s_op cov,
  have hp : ∀ i r, p i r → 0 < r := λ i r h, h.1,
  obtain ⟨t, ht₁, ht₂, ht₃, ht₄⟩ :=
    exists_countable_locally_finite_cover surjective_id hp hW₀ hW₁ hB,
  refine ⟨M × ℝ, t, λ z, _, ht₁, λ z, _, _, _⟩,
  { have h : range (open_smooth_embedding_to_ball (chart_at E z.1.1 z.1.1) z.1.2) ⊆
      (chart_at E z.1.1).target,
    { have aux : 0 < z.val.snd := hp _ _ (ht₂ _ z.2),
      simpa only [range_open_smooth_embedding_to_ball, aux] using (ht₂ _ z.2).2.1, },
    exact open_smooth_embedding_of_subset_chart_target M h, },
  { have aux : 0 < (z : M × ℝ).snd := hp _ _ (ht₂ _ z.2),
    simp only [subtype.val_eq_coe, coe_open_smooth_embedding_of_subset_chart_target],
    simp only [range_comp, range_open_smooth_embedding_to_ball, aux],
    exact (ht₂ z.1 z.2).2.2, },
  { convert ht₄,
    ext1 z,
    have aux : 0 < (z : M × ℝ).snd := hp _ _ (ht₂ _ z.2),
    simp only [subtype.val_eq_coe, coe_open_smooth_embedding_of_subset_chart_target],
    simpa only [range_comp, range_open_smooth_embedding_to_ball, aux], },
  { simpa only [Union_coe_set] using ht₃, },
end

variables [nonempty M]

lemma nice_atlas {ι : Type*} {s : ι → set M} (s_op : ∀ j, is_open $ s j) (cov : (⋃ j, s j) = univ) :
  ∃ n, ∃ φ : index_type n → open_smooth_embedding 𝓘(ℝ, E) E 𝓘(ℝ, E) M,
  (∀ i, ∃ j, range (φ i) ⊆ s j) ∧
  locally_finite (λ i, range (φ i)) ∧
  (⋃ i, φ i '' ball 0 1) = univ :=
begin
  obtain ⟨ι', t, φ, h₁, h₂, h₃, h₄⟩ := nice_atlas' E s_op cov (ball 0 1) (by simp) is_open_ball,
  have htne : t.nonempty,
  { by_contra contra,
    simp only [not_nonempty_iff_eq_empty.mp contra, Union_false, Union_coe_set, Union_empty,
      @eq_comm _ _ univ, univ_eq_empty_iff] at h₄,
    exact not_is_empty_of_nonempty M h₄, },
  obtain ⟨n, ⟨fn⟩⟩ := (set.countable_iff_exists_nonempty_index_type_equiv htne).mp h₁,
  refine ⟨n, φ ∘ fn, λ i, h₂ (fn i), h₃.comp_injective fn.injective, _⟩,
  rwa fn.surjective.Union_comp (λ i, φ i '' ball 0 1),
end

end without_boundary

namespace open_smooth_embedding

section updating

variables {𝕜 EX EM EY EN X M Y N : Type*} [nontrivially_normed_field 𝕜]
  [normed_add_comm_group EX] [normed_space 𝕜 EX]
  [normed_add_comm_group EM] [normed_space 𝕜 EM]
  [normed_add_comm_group EY] [normed_space 𝕜 EY]
  [normed_add_comm_group EN] [normed_space 𝕜 EN]
  [topological_space X] [charted_space EX X] [smooth_manifold_with_corners 𝓘(𝕜, EX) X]
  [topological_space M] [charted_space EM M] [smooth_manifold_with_corners 𝓘(𝕜, EM) M] [t2_space M]
  [metric_space Y]      [charted_space EY Y] [smooth_manifold_with_corners 𝓘(𝕜, EY) Y] [proper_space Y]
  [metric_space N]      [charted_space EN N] [smooth_manifold_with_corners 𝓘(𝕜, EN) N]
  (φ : open_smooth_embedding 𝓘(𝕜, EX) X 𝓘(𝕜, EM) M)
  (ψ : open_smooth_embedding 𝓘(𝕜, EY) Y 𝓘(𝕜, EN) N)
  (f : M → N) (g : X → Y)
  [decidable_pred (∈ range φ)]

/-- This is definition `def:update` in the blueprint. -/
def update (m : M) : N := if m ∈ range φ then ψ (g (φ.inv_fun m)) else f m

@[simp] lemma update_of_nmem_range {m : M} (hm : m ∉ range φ) :
  update φ ψ f g m = f m :=
by simp [update, hm]

@[simp] lemma update_of_mem_range {m : M} (hm : m ∈ range φ) :
  update φ ψ f g m = ψ (g (φ.inv_fun m)) :=
by simp [update, hm]

@[simp] lemma update_apply_embedding (x : X) :
  update φ ψ f g (φ x) = ψ (g x) :=
by simp [update]

/-- This is lemma `lem:updating` in the blueprint. -/
lemma nice_update_of_eq_outside_compact
  {K : set X} (hK : is_compact K)
  (hf : smooth 𝓘(𝕜, EM) 𝓘(𝕜, EN) f) (hf' : f '' range φ ⊆ range ψ)
  (hg : smooth 𝓘(𝕜, EX) 𝓘(𝕜, EY) g) (hg' : ∀ x, x ∉ K → f (φ x) = ψ (g x)) :
  smooth 𝓘(𝕜, EM) 𝓘(𝕜, EN) (update φ ψ f g) ∧
  (∀ (ε : M → ℝ) (hε : ∀ m, 0 < ε m) (hε' : continuous ε), ∃ (η > (0 : ℝ)),
    (∀ x, dist (g x) (ψ.inv_fun (f (φ x))) < η) → ∀ m, dist (update φ ψ f g m) (f m) < ε m) :=
begin
  have hK' : ∀ m ∉ φ '' K, update φ ψ f g m = f m := λ m hm, by
  { by_cases hm' : m ∈ range φ,
    { obtain ⟨x, rfl⟩ := hm',
      replace hm : x ∉ K, { contrapose! hm, exact mem_image_of_mem φ hm, },
      simp [hg' x hm], },
    { simp [hm'], }, },
  refine ⟨cont_mdiff_of_locally_cont_mdiff_on (λ m, _), λ ε hε hε', _⟩,
  { let U := range φ,
    let V := (φ '' K)ᶜ,
    have h₂ : is_open V := is_open_compl_iff.mpr (hK.image φ.continuous).is_closed,
    have h₃ : V ∪ U = univ,
    { rw [← compl_subset_iff_union, compl_compl], exact image_subset_range φ K, },
    have h₄ : ∀ m ∈ U, update φ ψ f g m = (ψ ∘ g ∘ φ.inv_fun) m := λ m hm, by simp [hm],
    by_cases hm : m ∈ U,
    { exact ⟨U, φ.is_open_range, hm, (cont_mdiff_on_congr h₄).mpr $
        ψ.smooth_to.comp_cont_mdiff_on $ hg.comp_cont_mdiff_on φ.smooth_inv⟩, },
    { refine ⟨V, h₂, _, (cont_mdiff_on_congr hK').mpr hf.cont_mdiff_on⟩,
      simpa [hm] using set.ext_iff.mp h₃ m, }, },
  { let K₁ := metric.cthickening 1 ((ψ.inv_fun ∘ f ∘ φ) '' K),
    have hK₁ : is_compact K₁,
    { refine metric.is_compact_of_is_closed_bounded metric.is_closed_cthickening
        (metric.bounded.cthickening $ is_compact.bounded $ hK.image _),
      replace hf' : ∀ x, f (φ x) ∈ range ψ := λ x, hf' ⟨φ x, mem_range_self x, rfl⟩,
      exact ψ.smooth_inv.continuous_on.comp_continuous
        (hf.continuous.comp φ.continuous) hf', },
    have h₁ : uniform_continuous_on ψ K₁ :=
      hK₁.uniform_continuous_on_of_continuous ψ.continuous.continuous_on,
    have hεφ : ∀ x ∈ K, 0 < (ε ∘ φ) x := λ x hx, hε _,
    obtain ⟨ε₀, hε₀, hε₀'⟩ :=
      hK.exists_forall_le' (hε'.comp φ.continuous).continuous_on hεφ,
    obtain ⟨τ, hτ : 0 < τ, hτ'⟩ := metric.uniform_continuous_on_iff.mp h₁ ε₀ hε₀,
    refine ⟨min τ 1, by simp [hτ], λ hη m, _⟩,
    by_cases hm : m ∈ φ '' K, swap, { simp [hK', hm, hε m], },
    obtain ⟨x, hx, rfl⟩ := hm,
    refine lt_of_lt_of_le _ (hε₀' x hx),
    simp only [update_apply_embedding],
    have h₁ : g x ∈ K₁ :=
      metric.mem_cthickening_of_dist_le _ _ _ _ ⟨x, hx, rfl⟩ (lt_min_iff.mp (hη x)).2.le,
    have h₂ : f (φ x) ∈ range ψ := hf' ⟨φ x, mem_range_self x, rfl⟩,
    rw ← ψ.right_inv h₂,
    exact hτ' _ h₁ _ (metric.self_subset_cthickening _ ⟨x, hx, rfl⟩) (lt_min_iff.mp (hη x)).1, },
end

end updating

end open_smooth_embedding
