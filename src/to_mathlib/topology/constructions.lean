import topology.constructions
import topology.homeomorph

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

lemma continuous.fst {f : α → β × γ} (hf : continuous f) :
  continuous (λ a : α, (f a).1) :=
continuous_fst.comp hf

lemma continuous.snd {f : α → β × γ} (hf : continuous f) :
  continuous (λ a : α, (f a).2) :=
continuous_snd.comp hf

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

/- TODO: reformulate these lemmas so that they are true -/
-- lemma continuous_uncurry_uncurry1 {f : α → β → ι} [has_uncurry (β → ι) (β × γ) δ]
--   [has_uncurry (α × β → ι) ((α × β) × γ) δ] :
--   continuous ↿(λ p : α × β, f p.1 p.2) ↔ continuous ↿f :=
-- begin
--   sorry
-- end

-- lemma continuous_uncurry_uncurry {f : α → β → ι} [has_uncurry ι γ δ] :
--   continuous ↿(λ p : α × β, f p.1 p.2) ↔ continuous ↿f :=
-- begin
--   sorry
-- end

lemma inducing.continuous_at_iff {f : α → β} {g : β → γ} (hg : inducing g) {x : α} :
  continuous_at f x ↔ continuous_at (g ∘ f) x :=
by simp_rw [continuous_at, inducing.tendsto_nhds_iff hg]

lemma homeomorph.comp_continuous_at_iff (h : α ≃ₜ β) (f : γ → α) (x : γ) :
  continuous_at (h ∘ f) x ↔ continuous_at f x :=
h.inducing.continuous_at_iff.symm

lemma inducing.continuous_at_iff' {f : α → β} {g : β → γ} (hf : inducing f) {x : α}
  (h : range f ∈ 𝓝 (f x)) :
  continuous_at (g ∘ f) x ↔ continuous_at g (f x) :=
by { simp_rw [continuous_at, filter.tendsto, ← hf.map_nhds_of_mem _ h, filter.map_map],  }

lemma homeomorph.comp_continuous_at_iff' (h : α ≃ₜ β) (f : β → γ) (x : α) :
  continuous_at (f ∘ h) x ↔ continuous_at f (h x) :=
h.inducing.continuous_at_iff' (by simp)

lemma continuous₃_iff (f : α → β → γ → δ) :
  continuous (λ p : (α × β) × γ, f p.1.1 p.1.2 p.2) ↔ continuous ↿f :=
by { convert (homeomorph.prod_assoc α β γ).comp_continuous_iff', refl }

lemma continuous_at₃_iff (f : α → β → γ → δ) {x : α} {y : β} {z : γ} :
  continuous_at (λ p : (α × β) × γ, f p.1.1 p.1.2 p.2) ((x, y), z) ↔ continuous_at ↿f (x, y, z) :=
(homeomorph.prod_assoc α β γ).comp_continuous_at_iff' ↿f ((x, y), z)
