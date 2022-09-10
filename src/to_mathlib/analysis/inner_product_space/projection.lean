import analysis.inner_product_space.projection

noncomputable theory

open_locale real_inner_product_space topological_space
open submodule function set filter

section general_stuff
-- Things in this section go to other files

lemma eq_zero_of_mem_disjoint {R : Type*} [comm_ring R] {M : Type*} [add_comm_group M] [module R M]
  {F G : submodule R M} (h : F ⊓ G = ⊥) {x : M} (hx : x ∈ F) (hx' : x ∈ G) : x = 0 :=
begin
  have := submodule.mem_inf.mpr ⟨hx, hx'⟩,
  rw h at this,
  simpa
end

@[simp] lemma forall_mem_span_singleton {R : Type*} [comm_ring R] {M : Type*} [add_comm_group M] [module R M]
  (P : M → Prop) (u : M) : (∀ x ∈ span R ({u} : set M), P x) ↔ ∀ t : R, P (t•u) :=
by simp [mem_span_singleton]

open_locale pointwise

@[simp] lemma field.exists_unit {𝕜 : Type*} [field 𝕜] (P : 𝕜 → Prop) :
  (∃ u : 𝕜ˣ, P u) ↔ ∃ u ≠ 0, P u :=
begin
  split,
  { rintros ⟨u, hu⟩,
    exact ⟨u, u.ne_zero, hu⟩ },
  { rintros ⟨u, u_ne, hu⟩,
    exact ⟨units.mk0 u u_ne, hu⟩ }
end

lemma span_singleton_eq_span_singleton_of_ne {𝕜 : Type*} [field 𝕜]{M : Type*} [add_comm_group M] [module 𝕜 M]
{u v : M} (hu : u ≠ 0) (hu' : u ∈ span 𝕜 ({v} : set M)) :
span 𝕜 ({u} : set M) = span 𝕜 ({v} : set M) :=
begin
  rcases mem_span_singleton.mp hu' with ⟨a, rfl⟩,
  by_cases hv : v = 0,
  { subst hv,
    simp },
  have : a ≠ 0,
  { rintro rfl,
    exact hu (zero_smul 𝕜 v) },
  symmetry,
  erw [submodule.span_singleton_eq_span_singleton, field.exists_unit (λ z : 𝕜, z • v = a • v)],
  use [a, this, rfl]
end

end general_stuff

variables {E : Type*} [inner_product_space ℝ E] [complete_space E]

lemma linear_isometry_equiv.apply_ne_zero
  {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
  {F : Type*} [normed_add_comm_group F] [normed_space ℝ F] [complete_space F]
  (φ : E ≃ₗᵢ⋆[ℝ] F) {x : E} (hx : x ≠ 0) : φ x ≠ 0 :=
begin
  intro H,
  apply hx,
  rw [← φ.symm_apply_apply x, H, φ.symm.map_zero]
end

-- ignore the next line which is fixing a pretty-printer bug
local notation (name := line_printing_only) `Δ` v:55 := submodule.span ℝ {v}
local notation `Δ` v:55 := submodule.span ℝ ({v} : set E)
-- ignore the next line which is fixing a pretty-printer bug
local notation (name := module_span_printing_only) `{.` x `}ᗮ` := (submodule.span ℝ {x})ᗮ
local notation `{.` x `}ᗮ` := (submodule.span ℝ ({x} : set E))ᗮ
local notation `pr[`x`]ᗮ` := orthogonal_projection (submodule.span ℝ {x})ᗮ

lemma orthogonal_projection_orthogonal {U : submodule ℝ E} {x : E}
  [complete_space (U : set E)] :
  (orthogonal_projection Uᗮ x : E) = x - orthogonal_projection U x :=
by rw [eq_sub_iff_add_eq, add_comm, ← eq_sum_orthogonal_projection_self_orthogonal_complement]

lemma orthogonal_line_inf {u v : E} : {.u}ᗮ ⊓ {.v}ᗮ = {.pr[v]ᗮ u}ᗮ ⊓ {.v}ᗮ :=
begin
  rw [inf_orthogonal, inf_orthogonal],
  refine congr_arg _ (le_antisymm (sup_le _ le_sup_right) (sup_le _ le_sup_right));
  rw [span_singleton_le_iff_mem],
  { nth_rewrite 0 eq_sum_orthogonal_projection_self_orthogonal_complement (Δ v) u,
    exact add_mem (mem_sup_right $ coe_mem _) (mem_sup_left $ mem_span_singleton_self _) },
  { rw [orthogonal_projection_orthogonal],
    refine sub_mem (mem_sup_left $ mem_span_singleton_self _) (mem_sup_right $ coe_mem _) }
end

lemma orthogonal_line_inf_sup_line (u v : E) : {.u}ᗮ ⊓ {.v}ᗮ  ⊔ Δ (pr[v]ᗮ u) = {.v}ᗮ :=
begin
  rw [orthogonal_line_inf, sup_comm, sup_orthogonal_inf_of_complete_space],
  rw span_singleton_le_iff_mem,
  exact coe_mem _
end

lemma orthogonal_projection_eq_zero_of_mem {F : submodule ℝ E} [complete_space F]
  {x : E} (h : x ∈ Fᗮ) : orthogonal_projection F x = 0 :=
begin
  refine subtype.coe_injective (eq_orthogonal_projection_of_mem_of_inner_eq_zero F.zero_mem _),
  simp only [coe_zero, sub_zero],
  exact (mem_orthogonal' F x).mp h,
end

lemma inner_projection_self_eq_zero_iff {F : submodule ℝ E} [complete_space F] {x : E} :
 ⟪x, orthogonal_projection F x⟫ = 0 ↔ x ∈ Fᗮ :=
begin
  obtain ⟨y, hy, z, hz, rfl⟩ := F.exists_sum_mem_mem_orthogonal x,
  rw [inner_add_left, map_add, coe_add, inner_add_right, inner_add_right],
  suffices : y = 0 ↔ y + z ∈ Fᗮ,
  { simpa [orthogonal_projection_eq_zero_of_mem hz, orthogonal_projection_eq_self_iff.mpr hy,
           inner_eq_zero_sym.mp (hz y hy)] },
  rw add_mem_cancel_right hz,
  split,
  { rintro rfl,
    exact Fᗮ.zero_mem },
  { exact eq_zero_of_mem_disjoint (inf_orthogonal_eq_bot F) hy },
end

variables {x₀ x : E}

@[simp] lemma mem_orthogonal_span_singleton_iff {x₀ x : E} :
  x ∈ {.x₀}ᗮ ↔ ⟪x₀, x⟫ = 0 :=
begin
  simp only [mem_orthogonal, forall_mem_span_singleton, inner_smul_left,
             is_R_or_C.conj_to_real, mul_eq_zero],
  split,
  { intros h,
    simpa using h 1 },
  { intros h t,
    exact or.inr h }
end

@[simp] lemma orthogonal_projection_orthogonal_singleton {x y : E} :
  pr[x]ᗮ y = ⟨y - (⟪x, y⟫/⟪x, x⟫) • x, begin
    rcases eq_or_ne x 0 with rfl|hx,
    { simp },
    simp [mem_orthogonal_span_singleton_iff],
    rw [inner_sub_right, inner_smul_right],
    have : ⟪x, x⟫ ≠ 0, -- TODO: extract as lemma or find it in mathlib
    { intro H,
      apply hx,
      rwa ← inner_self_eq_zero },
    field_simp [this]
  end⟩ :=
begin
  apply subtype.ext,
  have := eq_sum_orthogonal_projection_self_orthogonal_complement (span ℝ ({x} : set E)) y,
  simp [eq_sub_of_add_eq' this.symm, orthogonal_projection_singleton, real_inner_self_eq_norm_sq]
end

@[simp] lemma coe_orthogonal_projection_orthogonal_singleton {x y : E} :
  (pr[x]ᗮ y : E) = y - (⟪x, y⟫/⟪x, x⟫) • x :=
begin
  rw orthogonal_projection_orthogonal_singleton,
  refl
end

lemma orthogonal_projection_orthogonal_line_iso {x₀ x : E} (h : ⟪x₀, x⟫ ≠ 0) :
{.x₀}ᗮ ≃L[ℝ] {.x}ᗮ :=
{ inv_fun := λ y, ⟨y - (⟪x₀, y⟫/⟪x₀, x⟫) • x, begin
    rw [mem_orthogonal_span_singleton_iff, inner_sub_right, inner_smul_right],
    field_simp [h]
  end⟩,
  left_inv := begin
    rintros ⟨y, hy⟩,
    ext,
    dsimp,
    sorry
  end,
  right_inv := begin
    rintros ⟨y, hy⟩,
    ext,
    dsimp,
    sorry
  end,
  continuous_to_fun := (pr[x]ᗮ.comp (subtypeL {.x₀}ᗮ)).continuous,
  continuous_inv_fun := sorry,
  ..pr[x]ᗮ.comp (subtypeL {.x₀}ᗮ) }

lemma surjective_orthogonal_projection_comp_subtypeL {x₀ x : E} (h : ⟪x₀, x⟫ ≠ 0) :
  surjective (pr[x]ᗮ.comp (subtypeL {.x₀}ᗮ)) :=
begin
  -- The following proof is super weird, Lean has a lot of trouble unfolding definitions.
  convert (orthogonal_projection_orthogonal_line_iso h).surjective,
  ext e,
  delta orthogonal_projection_orthogonal_line_iso,
  refl,
end


lemma orthogonal_projection_comp_coe (K : submodule ℝ E) [complete_space K] :
  orthogonal_projection K ∘ (coe : K → E) = id :=
begin
  ext1 x,
  exact orthogonal_projection_mem_subspace_eq_self x
end

variable (E)

-- Is this really missing??
lemma normed_space.continuous_at_iff {E F : Type*}
  [seminormed_add_comm_group E] [seminormed_add_comm_group F] (f : E → F) (x : E) :
  continuous_at f x ↔ ∀ ε > 0, ∃ δ > 0, ∀ y, ∥y - x∥ < δ → ∥f y - f x∥ < ε :=
by simp_rw [metric.continuous_at_iff, dist_eq_norm]

lemma normed_space.continuous_at_iff' {E F : Type*}
  [seminormed_add_comm_group E] [seminormed_add_comm_group F] (f : E → F) (x : E) :
  continuous_at f x ↔ ∀ ε > 0, ∃ δ > 0, ∀ y, ∥y - x∥ ≤ δ → ∥f y - f x∥ ≤ ε :=
begin
  rw normed_space.continuous_at_iff,
  split ; intros h ε ε_pos,
  { rcases h ε ε_pos with ⟨η, η_pos, hη⟩,
    use [η/2, half_pos η_pos],
    intros h hy,
    apply le_of_lt,
    apply hη,
    linarith },
  { rcases h (ε/2) (half_pos ε_pos) with ⟨δ, δ_pos, hδ⟩,
    use [δ, δ_pos],
    intros y hy,
    linarith [hδ y (by linarith)] },
end

-- Is this really missing??
lemma normed_space.continuous_iff {E F : Type*}
  [seminormed_add_comm_group E] [seminormed_add_comm_group F] (f : E → F) :
  continuous f ↔ ∀ x, ∀ ε > 0, ∃ δ > 0, ∀ y, ∥y - x∥ < δ → ∥f y - f x∥ < ε :=
by simp_rw [metric.continuous_iff, dist_eq_norm]

lemma normed_space.continuous_iff' {E F : Type*}
  [seminormed_add_comm_group E] [seminormed_add_comm_group F] (f : E → F) :
  continuous f ↔ ∀ x, ∀ ε > 0, ∃ δ > 0, ∀ y, ∥y - x∥ ≤ δ → ∥f y - f x∥ ≤ ε :=
by simp_rw [continuous_iff_continuous_at, normed_space.continuous_at_iff']

lemma continuous_linear_map.op_norm_le_iff {𝕜 : Type*} {𝕜₂ : Type*} {E : Type*} {F : Type*}
  [seminormed_add_comm_group E] [seminormed_add_comm_group F] [nontrivially_normed_field 𝕜]
  [nontrivially_normed_field 𝕜₂] [normed_space 𝕜 E] [normed_space 𝕜₂ F]
  {σ₁₂ : 𝕜 →+* 𝕜₂} [ring_hom_isometric σ₁₂] {M : ℝ} (hM : 0 ≤ M) (f : E →SL[σ₁₂] F) :
  ∥f∥ ≤ M ↔ ∀ x, ∥f x∥ ≤ M * ∥x∥:=
⟨f.le_of_op_norm_le, f.op_norm_le_bound hM⟩

variable {E}

@[continuity]
lemma continuous_at_orthogonal_projection_orthogonal {x₀ : E} (hx₀ : x₀ ≠ 0) :
  continuous_at (λ x : E, {.x}ᗮ.subtypeL.comp pr[x]ᗮ) x₀ :=
begin
  rw normed_space.continuous_at_iff',
  intros ε ε_pos,
  suffices : ∃ δ > 0, ∀ y, ∥y - x₀∥ ≤ δ → ∀ x, ∥(⟪x₀, x⟫ / ⟪x₀, x₀⟫) • x₀ - (⟪y, x⟫ / ⟪y, y⟫) • y∥ ≤ ε * ∥x∥,
  sorry,/-
  simpa only [continuous_linear_map.op_norm_le_iff (le_of_lt ε_pos), orthogonal_projection_orthogonal_singleton,
  continuous_linear_map.coe_sub', continuous_linear_map.coe_comp', coe_subtypeL', submodule.coe_subtype, pi.sub_apply,
  comp_app, coe_mk, sub_sub_sub_cancel_left], -/

  let N : E → E := λ x, ⟪x, x⟫⁻¹ • x,
  have hNx₀ : 0 < ∥N x₀∥,
  {
    sorry },
  have cont : continuous_at N x₀,
  {
    sorry },
  have lim : tendsto (λ y, ∥N x₀ - N y∥ * ∥y∥) (𝓝 x₀) (𝓝 0),
  {
    sorry },
  have key : ∀ x y, (⟪x₀, x⟫ / ⟪x₀, x₀⟫) • x₀ - (⟪y, x⟫ / ⟪y, y⟫) • y =
    ⟪N x₀, x⟫ • (x₀ - y) + ⟪N x₀ - N y, x⟫ • y,
  sorry { intros x y,
    dsimp only [N],
    simp only [inner_smul_left, inner_sub_left, is_R_or_C.conj_to_real, smul_sub, sub_smul],
    field_simp },
  simp only [key],
  simp_rw [metric.tendsto_nhds_nhds, real.dist_0_eq_abs, dist_eq_norm] at lim,
  rcases lim (ε/2) (half_pos ε_pos) with ⟨η, η_pos, hη⟩,
  refine ⟨min (ε/(2*∥N x₀∥)) (η/2), _, _⟩,
  sorry, --{ apply lt_min, positivity, exact half_pos η_pos },
  intros y hy x,
  have hy₁ := hy.trans (min_le_left _ _), have hy₂ := hy.trans (min_le_right _ _), clear hy,
  specialize hη (by linarith : ∥y - x₀∥ < η),
  rw abs_of_nonneg at hη,
  calc ∥⟪N x₀, x⟫ • (x₀ - y) + ⟪N x₀ - N y, x⟫ • y∥ ≤
     ∥⟪N x₀, x⟫ • (x₀ - y)∥ + ∥⟪N x₀ - N y, x⟫ • y∥ : norm_add_le _ _
  ... ≤ ∥N x₀∥*∥x∥ * ∥x₀ - y∥ + ∥N x₀ - N y∥ * ∥x∥ * ∥y∥ : add_le_add _ _
  ... ≤ (ε/2) * ∥x∥ + (ε/2) * ∥x∥ : add_le_add _ _
  ... = ε * ∥x∥ : by linarith,
  {
    sorry },
  {
    sorry },
  {
    sorry },
  {
    sorry },
  {
    sorry },
end
