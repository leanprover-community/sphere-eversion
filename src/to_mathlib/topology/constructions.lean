import topology.constructions

noncomputable theory
open_locale topological_space classical
open set function

variables {α β γ δ ι : Type*} [topological_space α] [topological_space β] [topological_space γ]
  [topological_space δ]
  {x : α}

lemma continuous_at.fst {f : α → β × γ} (hf : continuous_at f x) :
  continuous_at (λ a : α, (f a).1) x :=
continuous_at_fst.comp hf

lemma continuous_at.snd {f : α → β × γ} (hf : continuous_at f x) :
  continuous_at (λ a : α, (f a).2) x :=
continuous_at_snd.comp hf

lemma is_open_slice_of_is_open_over {Ω : set (α × β)} {x₀ : α}
  (hΩ_op : ∃ U ∈ 𝓝 x₀, is_open (Ω ∩ prod.fst ⁻¹' U)) : is_open (prod.mk x₀ ⁻¹' Ω) :=
begin
  rcases hΩ_op with ⟨U, hU, hU_op⟩, convert hU_op.preimage (continuous.prod.mk x₀) using 1,
  simp_rw [preimage_inter, preimage_preimage, preimage_const, mem_of_mem_nhds hU, if_pos,
    inter_univ]
end

-- lemma continuous_uncurry_uncurry_base {f : α → ι} [has_uncurry ι β γ] :
--   continuous ↿(λ a, ↿(f a)) ↔ continuous ↿f :=
-- begin
--   sorry
-- end
-- instance has_uncurry_induction [has_uncurry β γ δ] : has_uncurry (α → β) (α × γ) δ :=
-- ⟨λ f p, ↿(f p.1) p.2⟩


lemma continuous_uncurry_uncurry1 {f : α → β → ι} [has_uncurry (β → ι) (β × γ) δ]
  [has_uncurry (α × β → ι) ((α × β) × γ) δ] :
  continuous ↿(λ p : α × β, f p.1 p.2) ↔ continuous ↿f :=
begin
  sorry
end

lemma continuous_uncurry_uncurry {f : α → β → ι} [has_uncurry ι γ δ] :
  continuous ↿(λ p : α × β, f p.1 p.2) ↔ continuous ↿f :=
begin
  sorry
end
