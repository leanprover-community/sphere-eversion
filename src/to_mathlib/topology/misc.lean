import topology.path_connected
import topology.urysohns_lemma
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
lemma zero_mem : (0 : ℝ) ∈ I := ⟨le_rfl, zero_le_one⟩
lemma one_mem : (1 : ℝ) ∈ I := ⟨zero_le_one, le_rfl⟩

end unit_interval

end

section

section
variables {α : Type*} [uniform_space α]
-- to uniform_space/basic

-- `uniformity_eq_symm` should probably be reformulated in the library
-- UNUSED
lemma symm_eq_uniformity : map (@prod.swap α α) (𝓤 α) = 𝓤 α :=
uniformity_eq_symm.symm

-- UNUSED
lemma nhds_eq_comap_uniformity_rev {y : α} : 𝓝 y = (𝓤 α).comap (λ x, (x, y)) :=
by { rw [uniformity_eq_symm, map_swap_eq_comap_swap, comap_comap], exact nhds_eq_comap_uniformity }

end

end


section

variables {α β : Type*} [topological_space α] [topological_space β]

-- basic
lemma continuous.congr {f g : α → β} (h : continuous f) (h' : ∀ x, f x = g x) : continuous g :=
by { convert h, ext, rw h' }

-- TODO: rename `finset.closure_Union` to `finset.closure_bUnion`

-- constructions
lemma continuous.subtype_coe {p : β → Prop} {f : α → subtype p} (hf : continuous f) :
  continuous (λ x, (f x : β)) :=
continuous_subtype_coe.comp hf

end

section -- to separation

variables {α : Type*} [topological_space α]

lemma exists_open_superset_and_is_compact_closure [locally_compact_space α] [t2_space α]
  {K : set α} (hK : is_compact K) : ∃ V, is_open V ∧ K ⊆ V ∧ is_compact (closure V) :=
begin
  rcases exists_compact_superset hK with ⟨K', hK', hKK'⟩,
  refine ⟨interior K', is_open_interior, hKK',
    compact_closure_of_subset_compact hK' interior_subset⟩,
end

lemma exists_compact_between [locally_compact_space α] [regular_space α]
  {K U : set α} (hK : is_compact K) (hU : is_open U) (hKU : K ⊆ U) :
  ∃ K', is_compact K' ∧ K ⊆ interior K' ∧ closure K' ⊆ U :=
begin
  choose C hxC hCU hC using λ x : K, nhds_is_closed (hU.mem_nhds $ hKU x.2),
  choose L hL hxL using λ x : K, exists_compact_mem_nhds (x : α),
  have : K ⊆ ⋃ x, interior (L x) ∩ interior (C x), from
  λ x hx, mem_Union.mpr ⟨⟨x, hx⟩,
    ⟨mem_interior_iff_mem_nhds.mpr (hxL _), mem_interior_iff_mem_nhds.mpr (hxC _)⟩⟩,
  rcases hK.elim_finite_subcover _ _ this with ⟨t, ht⟩,
  { refine ⟨⋃ x ∈ t, L x ∩ C x, t.compact_bUnion (λ x _, (hL x).inter_right (hC x)), λ x hx, _, _⟩,
    { obtain ⟨y, hyt, hy : x ∈ interior (L y) ∩ interior (C y)⟩ := mem_bUnion_iff.mp (ht hx),
      rw [← interior_inter] at hy,
      refine interior_mono (subset_bUnion_of_mem hyt) hy },
    { simp_rw [t.closure_Union, Union_subset_iff, ((hL _).is_closed.inter (hC _)).closure_eq],
      rintro x -, exact (inter_subset_right _ _).trans (hCU _) } },
  { exact λ _, is_open_interior.inter is_open_interior }
end

lemma exists_open_between_and_is_compact_closure [locally_compact_space α] [regular_space α]
  {K U : set α} (hK : is_compact K) (hU : is_open U) (hKU : K ⊆ U) :
  ∃ V, is_open V ∧ K ⊆ V ∧ closure V ⊆ U ∧ is_compact (closure V) :=
begin
  rcases exists_compact_between hK hU hKU with ⟨V, hV, hKV, hVU⟩,
  refine ⟨interior V, is_open_interior, hKV, (closure_mono interior_subset).trans hVU,
    compact_closure_of_subset_compact hV interior_subset⟩,
end

end