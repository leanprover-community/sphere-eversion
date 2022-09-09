import analysis.inner_product_space.projection

open_locale real_inner_product_space
open submodule

section general_stuff
-- Things in this section go to other files

lemma eq_zero_of_mem_disjoint {R : Type*} [comm_ring R] {M : Type*} [add_comm_group M] [module R M]
  {F G : submodule R M} (h : F ⊓ G = ⊥) {x : M} (hx : x ∈ F) (hx' : x ∈ G) : x = 0 :=
begin
  have := submodule.mem_inf.mpr ⟨hx, hx'⟩,
  rw h at this,
  simpa
end

/- lemma foo {𝕜 : Type*} [field 𝕜]{M : Type*} [add_comm_group M] [module 𝕜 M]
{u : M} (hu : u ≠ 0) {a : 𝕜} (hu' : u ∈ span 𝕜 ({v} : set M)) :
 -/

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
