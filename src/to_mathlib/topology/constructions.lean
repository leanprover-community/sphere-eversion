import topology.constructions

noncomputable theory
open_locale topological_space classical
open set

variables {α β γ : Type*} [topological_space α] [topological_space β] [topological_space γ]
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
