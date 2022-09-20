import to_mathlib.partition
import to_mathlib.geometry.manifold.misc_manifold

noncomputable theory

open_locale topological_space manifold big_operators
open set function

lemma locally_finite_prod {α β γ : Type*} [topological_space α] [topological_space γ]
  (f : β → set α) (h : locally_finite f) :
  locally_finite (λ b, (f b) ×ˢ (univ : set γ)) :=
begin
  rintros ⟨a, c⟩,
  obtain ⟨t, ht₁, ht₂⟩ := h a,
  refine ⟨t ×ˢ univ, mem_nhds_prod_iff.mpr ⟨t, ht₁, univ, filter.univ_mem, subset.rfl⟩, _⟩,
  simp only [prod_inter_prod, univ_inter],
  refine ht₂.subset (λ b hb, _),
  simp only [mem_set_of_eq] at hb,
  obtain ⟨⟨a', c'⟩, h'⟩ := hb,
  simp only [prod_mk_mem_set_prod_eq, mem_univ, and_true] at h',
  exact ⟨a', h'⟩,
end

-- See: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Typeclass.20resolution.20under.20binders/near/281296989
instance real.normed_space.to_module (F : Type*) [normed_add_comm_group F] [normed_space ℝ F] : module ℝ F :=
by apply_instance

variables {E₁ E₂ F : Type*}
variables [normed_add_comm_group E₁] [normed_space ℝ E₁] [finite_dimensional ℝ E₁]
variables [normed_add_comm_group E₂] [normed_space ℝ E₂] [finite_dimensional ℝ E₂]
variables [normed_add_comm_group F] [normed_space ℝ F]

variables {H₁ M₁ H₂ M₂ : Type*}
variables [topological_space H₁] (I₁ : model_with_corners ℝ E₁ H₁)
variables [topological_space M₁] [charted_space H₁ M₁] [smooth_manifold_with_corners I₁ M₁]
variables [sigma_compact_space M₁] [t2_space M₁]
variables [topological_space H₂] (I₂ : model_with_corners ℝ E₂ H₂)
variables [topological_space M₂] [charted_space H₂ M₂] [smooth_manifold_with_corners I₂ M₂]

local notation `𝓒` := cont_mdiff (I₁.prod I₂) 𝓘(ℝ, F)
local notation `𝓒_on` := cont_mdiff_on (I₁.prod I₂) 𝓘(ℝ, F)

namespace smooth_partition_of_unity

variables {ι : Type*} (ρ : smooth_partition_of_unity ι I₁ M₁) {I₁} (I₂ M₂)

/-- If `ρ` is a smooth partition of unity for smooth manifold `M₁` and `M₂` is another smooth
manifold (with model `I₂`) then `ρ.prod M₂ I₂` is the smooth partition of unity for `M₁ × M₂`
obtained by precomposing each component of `ρ` with the projection map `M₁ × M₂ → M₁`. -/
def prod : smooth_partition_of_unity ι (I₁.prod I₂) (M₁ × M₂) :=
{ to_fun := λ i, (ρ i).comp ⟨prod.fst, cont_mdiff_fst⟩,
  locally_finite' :=
  begin
    convert locally_finite_prod _ ρ.locally_finite,
    ext i ⟨x, y⟩,
    simp only [mem_support, cont_mdiff_map.comp_apply, cont_mdiff_map.coe_fn_mk,
      prod_mk_mem_set_prod_eq, mem_univ, and_true],
  end,
  nonneg' := λ i z, by simp only [cont_mdiff_map.comp_apply, cont_mdiff_map.coe_fn_mk, ρ.nonneg i],
  sum_le_one' := λ z, by simp only [ρ.sum_le_one, cont_mdiff_map.comp_apply],
  sum_eq_one' := λ z h, by simp only [ρ.sum_eq_one, cont_mdiff_map.comp_apply, mem_univ], }

@[simp] lemma tsupport_prod (i : ι) :
  tsupport (ρ.prod M₂ I₂ i) = tsupport (ρ i) ×ˢ (univ : set M₂) :=
begin
  change closure (support (λ (xy : M₁ × M₂), (ρ i) xy.1)) = closure (support (ρ i)) ×ˢ univ,
  rw [← show closure univ = (univ : set M₂), from is_closed_univ.closure_eq, ← closure_prod_eq],
  congr,
  ext,
  simp,
end

end smooth_partition_of_unity

lemma exists_cont_mdiff_of_convex₂
  {P : M₁ → (M₂ → F) → Prop} (hP : ∀ x, convex ℝ {f | P x f}) {n : ℕ∞}
  (hP' : ∀ x : M₁, ∃ (U ∈ 𝓝 x) (f : M₁ → M₂ → F),
    𝓒_on n (uncurry f) (U ×ˢ (univ : set M₂)) ∧ ∀ y ∈ U, P y (f y)) :
  ∃ f : M₁ → M₂ → F, 𝓒 n (uncurry f) ∧ ∀ x, P x (f x) :=
begin
  replace hP' : ∀ x : M₁, ∃ U ∈ 𝓝 x, (is_open U) ∧ ∃ f : M₁ → M₂ → F,
    𝓒_on n (uncurry f) (U ×ˢ (univ : set M₂)) ∧ ∀ y ∈ U, P y (f y),
  { intros x,
    rcases ((nhds_basis_opens x).exists_iff _).mp (hP' x) with ⟨U, ⟨x_in, U_op⟩, f, hf, hfP⟩,
    exact ⟨U, U_op.mem_nhds x_in, U_op, f, hf, hfP⟩,
    rintros s t hst ⟨f, hf, hf'⟩,
    exact ⟨f, hf.mono (prod_mono hst subset.rfl), λ x hx, hf' x (hst hx)⟩, },
  choose U hU U_op φ hφ using hP',
  rcases smooth_bump_covering.exists_is_subordinate I₁ is_closed_univ (λ x h, hU x) with ⟨ι, b, hb⟩,
  let ρ := b.to_smooth_partition_of_unity,
  have subf : ∀ i, support (ρ i) ⊆ U (b.c i) := λ i,
    subset_closure.trans (smooth_bump_covering.is_subordinate.to_smooth_partition_of_unity hb i),
  refine ⟨λ x, ∑ᶠ i, (ρ i x) • φ (b.c i) x, _, λ x₀, _⟩,
  { have h₁ : uncurry (λ (x : M₁), ∑ᶠ (i : ι), ρ i x • φ (b.c i) x) =
              λ (xy : M₁ × M₂), ∑ᶠ (i : ι), (ρ.prod M₂ I₂ i xy) • uncurry (φ (b.c i)) xy,
    { ext ⟨x, y⟩,
      simp only [uncurry_apply_pair],
      change _ = ∑ᶠ i, ρ i x • φ (b.c i) x y,
      erw [← ρ.to_partition_of_unity.sum_finsupport_smul,
        ← ρ.to_partition_of_unity.sum_finsupport_smul],
      simp only [finset.sum_apply, pi.smul_apply], },
    rw h₁,
    rintros ⟨x, y⟩,
    refine (ρ.prod M₂ I₂).cont_diff_at_sum (λ i hxy, _),
    have hx : x ∈ U (b.c i),
    { suffices : x ∈ tsupport (ρ i),
      { exact smooth_bump_covering.is_subordinate.to_smooth_partition_of_unity hb i this, },
      rw [ρ.tsupport_prod M₂ I₂ i] at hxy,
      simpa using hxy, },
    refine ((hφ $ b.c i).1 ⟨x, y⟩ _).cont_mdiff_at _,
    { simpa only [prod_mk_mem_set_prod_eq, mem_univ, and_true], },
    { exact mem_nhds_prod_iff.mpr
      ⟨_, (U_op $ b.c i).mem_nhds hx, _, filter.univ_mem, subset.rfl⟩, }, },
  { erw ← ρ.to_partition_of_unity.sum_finsupport_smul,
    refine (hP x₀).sum_mem (λ i hi, (ρ.nonneg i x₀ : _))
      ρ.to_partition_of_unity.sum_finsupport (λ i hi, _),
    rw [partition_of_unity.mem_finsupport] at hi,
    exact (hφ $ b.c i).2 _ (subf _ hi), },
end

lemma exists_cont_diff_of_convex₂
  {P : E₁ → (E₂ → F) → Prop} (hP : ∀ x, convex ℝ {f | P x f}) {n : ℕ∞}
  (hP' : ∀ x : E₁, ∃ (U ∈ 𝓝 x) (f : E₁ → E₂ → F),
    cont_diff_on ℝ n (uncurry f) (U ×ˢ (univ : set E₂)) ∧ ∀ y ∈ U, P y (f y)) :
  ∃ f : E₁ → E₂ → F, cont_diff ℝ n (uncurry f) ∧ ∀ x, P x (f x) :=
begin
  simp_rw [← cont_mdiff_on_iff_cont_diff_on, model_with_corners_self_prod] at hP',
  simp_rw [← cont_mdiff_iff_cont_diff, model_with_corners_self_prod],
  rw [← charted_space_self_prod] at hP' ⊢, -- Why does `simp_rw` not succeed here?
  exact exists_cont_mdiff_of_convex₂ 𝓘(ℝ, E₁) 𝓘(ℝ, E₂) hP hP',
end
