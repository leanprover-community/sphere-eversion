import topology.path_connected
import topology.uniform_space.compact_separated

noncomputable theory

open set function filter
open_locale unit_interval topological_space uniformity filter classical

section -- to ???

-- needs classical
variables {α β γ δ ι : Type*} [topological_space α] [topological_space β] {x : α}

lemma is_open_slice_of_is_open_over {Ω : set (α × β)} {x₀ : α}
  (hΩ_op : ∃ U ∈ 𝓝 x₀, is_open (Ω ∩ prod.fst ⁻¹' U)) : is_open (prod.mk x₀ ⁻¹' Ω) :=
begin
  rcases hΩ_op with ⟨U, hU, hU_op⟩, convert hU_op.preimage (continuous.prod.mk x₀) using 1,
  simp_rw [preimage_inter, preimage_preimage, preimage_const, mem_of_mem_nhds hU, if_pos,
    inter_univ]
end


end

section -- logic.function

-- move
-- @[simp] lemma base_apply {α β : Type*} (f : α → β) (x : α) : ↿f x = f x := rfl
-- @[simp] lemma induction_apply {α β γ δ : Type*} {h : has_uncurry β γ δ} (f : α → β) (x : α)
--   (c : γ) : ↿f (x, c) = ↿(f x) c :=
-- rfl

-- @[simp] lemma uncurry_loop_apply {F : Type*} [normed_group F] [normed_space ℝ F]
--   [finite_dimensional ℝ F] {α : Type*} (f : α → loop F) (x : α) (t : ℝ) :
--   ↿f (x, t) = f x t :=
-- rfl

-- @[simp] lemma uncurry_path_apply {X α : Type*} [topological_space X] {x y : α → X}
--   (f : Π a, path (x a) (y a)) (a : α) (t : I) : ↿f (a, t) = f a t :=
-- rfl
mk_simp_attribute uncurry_simps "unfolds all occurrences of the uncurry operation `↿`."
attribute [uncurry_simps] function.has_uncurry_base function.has_uncurry_induction
  path.has_uncurry_path

end



section -- to unit_interval

namespace unit_interval

open int
lemma fract_mem (x : ℝ) : fract x ∈ I := ⟨fract_nonneg _, (fract_lt_one _).le⟩

end unit_interval

end

section

section
variables {α : Type*} [uniform_space α]
-- to uniform_space/basic

-- `uniformity_eq_symm` should probably be reformulated in the library
lemma symm_eq_uniformity : map (@prod.swap α α) (𝓤 α) = 𝓤 α :=
uniformity_eq_symm.symm

lemma nhds_eq_comap_uniformity_rev {y : α} : 𝓝 y = (𝓤 α).comap (λ x, (x, y)) :=
by { rw [uniformity_eq_symm, map_swap_eq_comap_swap, comap_comap], exact nhds_eq_comap_uniformity }


end

-- to logic/basic
/-- We intentionally restrict the type of `α` here so that this is a safer to use in simp. -/
lemma imp_forall_iff {α : Type*} {p : Prop} {q : α → Prop} : (p → ∀ x, q x) ↔ (∀ x, p → q x) :=
forall_swap

-- to filter/basic
lemma filter.mem_prod_top {α β : Type*} {f : filter α} {s : set (α × β)} :
  s ∈ f ×ᶠ (⊤ : filter β) ↔ {a | ∀ b, (a, b) ∈ s} ∈ f :=
begin
  rw [← @exists_mem_subset_iff _ f],
  simp only [mem_prod_iff, exists_prop, exists_eq_left, mem_top, prod_univ, mem_preimage,
    prod.forall, subset_def, mem_set_of_eq, imp_forall_iff]
end

-- to uniform_convergence
lemma tendsto_prod_top_iff {α β ι : Type*} [uniform_space β] {F : ι → α → β} {c : β}
  {p : filter ι} : tendsto ↿F (p ×ᶠ ⊤) (𝓝 c) ↔ tendsto_uniformly F (λ _, c) p :=
let j : β → β × β := prod.mk c in
calc tendsto ↿F (p ×ᶠ ⊤) (𝓝 c)
    ↔ map ↿F (p ×ᶠ ⊤) ≤ (𝓝 c) : iff.rfl
... ↔ map ↿F (p ×ᶠ ⊤) ≤ comap j (𝓤 β) : by rw nhds_eq_comap_uniformity
... ↔ map j (map ↿F (p ×ᶠ ⊤)) ≤ 𝓤 β : map_le_iff_le_comap.symm
... ↔ map (j ∘ ↿F) (p ×ᶠ ⊤) ≤ 𝓤 β : by rw map_map
... ↔ ∀ V ∈ 𝓤 β, {x | (c, ↿F x) ∈ V} ∈ (p ×ᶠ ⊤ : filter $ ι × α) : iff.rfl
... ↔ ∀ V ∈ 𝓤 β, {i | ∀ a, (c, F i a) ∈ V} ∈ p : by simpa [filter.mem_prod_top]

-- can this be shorter?
lemma uniform_continuous_on.tendsto_uniformly {α β γ : Type*}
  [uniform_space α] [uniform_space β] [uniform_space γ] {x : α} {U : set α} (hU : U ∈ 𝓝 x)
  {f : α → β → γ} (h : uniform_continuous_on ↿f (U.prod univ)) :
  tendsto_uniformly f (f x) (𝓝 x) :=
begin
  intros V hV,
  rw [uniform_continuous_on, uniformity_prod_eq_prod] at h,
  specialize h hV,
  rw [mem_map, mem_inf_iff] at h,
  rcases h with ⟨s, hs, t, ht, hst⟩,
  rw [mem_map, mem_prod_iff] at hs, rcases hs with ⟨u, hu, v, hv, huvs⟩,
  rw [mem_principal] at ht,
  rw [← image_subset_iff] at huvs,
  have hU' := mem_nhds_uniformity_iff_right.mp hU,
  rw [nhds_eq_comap_uniformity, eventually_comap],
  apply eventually_of_mem (inter_mem hu hU'),
  rintro ⟨x', y'⟩ ⟨hxyu, hxyU⟩ y hxy b,
  cases hxy,
  show ((x, b), (y, b)) ∈ (λ p : _ × _, (↿f p.1, ↿f p.2)) ⁻¹' V,
  rw [hst],
  refine ⟨huvs ⟨((x, y), (b, b)), _, rfl⟩, ht _⟩,
  exact ⟨hxyu, refl_mem_uniformity hv⟩,
  refine ⟨⟨mem_of_mem_nhds hU, mem_univ b⟩, ⟨hxyU rfl, mem_univ b⟩⟩
end

lemma uniform_continuous₂.tendsto_uniformly {α β γ : Type*}
  [uniform_space α] [uniform_space β] [uniform_space γ]
  {f : α → β → γ} (h : uniform_continuous₂ f) {x : α} : tendsto_uniformly f (f x) (𝓝 x) :=
uniform_continuous_on.tendsto_uniformly univ_mem $
  by rwa [univ_prod_univ, uniform_continuous_on_univ]

local attribute [instance] uniform_space.separation_setoid

lemma is_separated.eq_of_uniform_continuous {α β : Type*} [uniform_space α] [uniform_space β]
  {f : α → β} {x y : α} {s : set β} (hs : is_separated s) (hxs : f x ∈ s) (hys : f y ∈ s)
  (H : uniform_continuous f) (h : x ≈ y) : f x = f y :=
(is_separated_def _).mp hs _ _ hxs hys $ λ _ h', h _ (H h')

lemma is_separated.prod {α β : Type*} [uniform_space α] [uniform_space β] {s : set α} {t : set β}
  (hs : is_separated s) (ht : is_separated t) : is_separated (s.prod t) :=
(is_separated_def _).mpr $ assume x y hx hy H, prod.ext
  (hs.eq_of_uniform_continuous hx.1 hy.1 uniform_continuous_fst H)
  (ht.eq_of_uniform_continuous hx.2 hy.2 uniform_continuous_snd H)

lemma is_separated.mono {α : Type*} [uniform_space α] {s t : set α}
  (hs : is_separated s) (hts : t ⊆ s) : is_separated t :=
λ x y hx hy, hs x y (hts hx) (hts hy)

lemma continuous_on.tendsto_uniformly {α β γ : Type*}
  [uniform_space α] [uniform_space β] [uniform_space γ] [locally_compact_space α] [compact_space β]
  [separated_space β]
  {f : α → β → γ} {x : α} {U : set α} (hxU : U ∈ 𝓝 x) (hU : is_separated U)
  (h : continuous_on ↿f (U.prod univ)) :
  tendsto_uniformly f (f x) (𝓝 x) :=
begin
  rcases locally_compact_space.local_compact_nhds _ _ hxU with ⟨K, hxK, hKU, hK⟩,
  have : uniform_continuous_on ↿f (K.prod univ),
  { refine is_compact.uniform_continuous_on_of_continuous' (hK.prod compact_univ) _
      (h.mono $ prod_mono hKU subset.rfl),
    exact (hU.mono hKU).prod (is_separated_of_separated_space _) },
  exact this.tendsto_uniformly hxK
end

lemma continuous.tendsto_uniformly {α β γ : Type*}
  [uniform_space α] [separated_space α] [locally_compact_space α] [uniform_space β]
  [compact_space β] [separated_space β] [uniform_space γ]
  (f : α → β → γ) (h : continuous ↿f) (x : α) : tendsto_uniformly f (f x) (𝓝 x) :=
h.continuous_on.tendsto_uniformly univ_mem $ is_separated_of_separated_space _

end
