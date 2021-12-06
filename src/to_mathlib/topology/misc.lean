import topology.path_connected
import topology.urysohns_lemma
import topology.uniform_space.compact_separated
import linear_algebra.affine_space.independent
import analysis.normed_space.finite_dimension
<<<<<<< HEAD
import topology.algebra.floor_ring
||||||| merged common ancestors
=======
import topology.paracompact
import topology.shrinking_lemma
>>>>>>> some work on lem 1.15

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

namespace filter

variables {α β : Type*} {f : filter α} {g : filter β}

lemma eventually_eventually_of_eventually_prod {p : α → β → Prop}
  (h : ∀ᶠ (z : α × β) in f ×ᶠ g, p z.1 z.2) : ∀ᶠ x in f, ∀ᶠ y in g, p x y :=
begin
  rw [filter.eventually_prod_iff] at h, rcases h with ⟨pa, hpa, pb, hpb, h⟩,
  filter_upwards [hpa], intros a ha,
  filter_upwards [hpb], intros b hb, exact h ha hb
end


end filter

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
lemma div_mem {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x ≤ y) : x / y ∈ I :=
⟨div_nonneg hx hy, div_le_one_of_le hxy hy⟩

lemma mul_mem' {x y : ℝ} (hx : x ∈ I) (hy : y ∈ I) : x * y ∈ I :=
⟨mul_nonneg hx.1 hy.1, (mul_le_mul hx.2 hy.2 hy.1 zero_le_one).trans_eq $ one_mul 1⟩


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

variables {α β γ : Type*} [topological_space α] [topological_space β]

-- basic
lemma continuous.congr {f g : α → β} (h : continuous f) (h' : ∀ x, f x = g x) : continuous g :=
by { convert h, ext, rw h' }

-- false
-- lemma locally_finite_image [topological_space γ] {f : β → set α} {g : α → γ}
--   (hf : locally_finite f) (hg : open_embedding g) : locally_finite (λ i, g '' (f i)) :=
-- begin
--   intro y,
--   by_cases hy : y ∈ range g,
--   { rcases hy with ⟨x, rfl⟩,
--     obtain ⟨t, ht, hft⟩ := hf x,
--     refine ⟨g '' t, hg.is_open_map.image_mem_nhds ht, _⟩,
--     simp_rw [image_inter hg.to_embedding.inj, nonempty_image_iff, hft] },
--   { }
-- end

-- TODO: rename `finset.closure_Union` to `finset.closure_bUnion`

-- constructions
lemma continuous.subtype_coe {p : β → Prop} {f : α → subtype p} (hf : continuous f) :
  continuous (λ x, (f x : β)) :=
continuous_subtype_coe.comp hf

end

section -- to subset_properties

variables {α β γ : Type*} [topological_space α] [topological_space β] [topological_space γ]

lemma is_compact.eventually_forall_of_forall_eventually {x₀ : α} {K : set β} (hK : is_compact K)
  {P : α → β → Prop} (hP : ∀ y ∈ K, ∀ᶠ (z : α × β) in 𝓝 (x₀, y), P z.1 z.2):
  ∀ᶠ x in 𝓝 x₀, ∀ y ∈ K, P x y :=
begin
  refine hK.induction_on _ _ _ _,
  { exact eventually_of_forall (λ x y, false.elim) },
  { intros s t hst ht, refine ht.mono (λ x h y hys, h y $ hst hys) },
  { intros s t hs ht, filter_upwards [hs, ht], rintro x h1 h2 y (hys|hyt),
    exacts [h1 y hys, h2 y hyt] },
  { intros y hyK,
    specialize hP y hyK,
    rw [nhds_prod_eq, eventually_prod_iff] at hP,
    rcases hP with ⟨p, hp, q, hq, hpq⟩,
    exact ⟨{y | q y}, mem_nhds_within_of_mem_nhds hq, eventually_of_mem hp @hpq⟩ }
end

lemma is_compact.eventually_forall_mem {x₀ : α} {K : set β} (hK : is_compact K)
  {f : α → β → γ} (hf : continuous ↿f) {U : set γ} (hU : ∀ y ∈ K, U ∈ 𝓝 (f x₀ y)) :
  ∀ᶠ x in 𝓝 x₀, ∀ y ∈ K, f x y ∈ U :=
hK.eventually_forall_of_forall_eventually $ λ y hy, hf.continuous_at.eventually $
  show U ∈ 𝓝 (↿f (x₀, y)), from hU y hy

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

/-
needs
import linear_algebra.affine_space.independent
import analysis.normed_space.finite_dimension
-/
lemma is_open_set_of_affine_independent (𝕜 E : Type*) {ι : Type*} [nondiscrete_normed_field 𝕜]
  [normed_group E] [normed_space 𝕜 E] [complete_space 𝕜] [fintype ι] :
  is_open {p : ι → E | affine_independent 𝕜 p} :=
begin
  classical,
  cases is_empty_or_nonempty ι, { resetI, exact is_open_discrete _ },
  obtain ⟨i₀⟩ := h,
  simp_rw [affine_independent_iff_linear_independent_vsub 𝕜 _ i₀],
  let ι' := {x // x ≠ i₀},
  haveI : fintype ι' := subtype.fintype _,
  convert_to
    is_open ((λ (p : ι → E) (i : ι'), p i -ᵥ p i₀) ⁻¹' {p : ι' → E | linear_independent 𝕜 p}),
  refine is_open.preimage _ is_open_set_of_linear_independent,
  refine continuous_pi (λ i', continuous.vsub (continuous_apply i') $ continuous_apply i₀),
end

end

-- move
lemma continuous_on.comp_fract'' {α β γ : Type*} [linear_ordered_ring α] [floor_ring α]
  [topological_space α] [order_topology α]
  [topological_add_group α] [topological_space β] [topological_space γ]
  {s : β → α}
  {f : β → α → γ}
  (h : continuous_on (uncurry f) $ (univ : set β).prod (Icc 0 1 : set α))
  (hs : continuous s)
  (hf : ∀ s, f s 0 = f s 1) :
  continuous (λ x : β, f x $ int.fract (s x)) :=
(h.comp_fract' hf).comp (continuous_id.prod_mk hs)

-- TODO: replace mathlib's `connected_component_in`, which is never used, by the following.

/-- Given a set `F` in a topological space `α` and a point `x : α`, the connected
component of `x` in `F` is the connected component of `x` in the subtype `F` seen as
a set in `α`. This definition does not make sense if `x` is not in `F` so we return the
empty set in this case. -/
def connected_comp_in {α : Type*} [topological_space α] (F : set α) (x : α) : set α :=
if h : x ∈ F then coe '' (connected_component (⟨x, h⟩ : F)) else ∅

namespace topological_space -- to topology.bases
lemma cover_nat_nhds_within {α} [topological_space α] [second_countable_topology α] {f : α → set α}
  {s : set α} (hf : ∀ x ∈ s, f x ∈ 𝓝[s] x) (hs : s.nonempty) :
  ∃ x : ℕ → α, range x ⊆ s ∧ s ⊆ ⋃ n, f (x n) :=
begin
  obtain ⟨t, hts, ht, hsf⟩ := topological_space.countable_cover_nhds_within hf,
  have hnt : t.nonempty,
  { by_contra,
    rw [not_nonempty_iff_eq_empty] at h,
    rw [h, bUnion_empty, subset_empty_iff] at hsf,
    exact hs.ne_empty hsf },
  obtain ⟨x, rfl⟩ := ht.exists_surjective hnt,
  rw [bUnion_range] at hsf,
  exact ⟨x, hts, hsf⟩
end

/-- A version of `topological_space.cover_nat_nhds_within` where `f` is only defined on `s`. -/
lemma cover_nat_nhds_within' {α} [topological_space α] [second_countable_topology α] {s : set α}
  {f : ∀ x ∈ s, set α} (hf : ∀ x (hx : x ∈ s), f x hx ∈ 𝓝[s] x) (hs : s.nonempty) :
  ∃ (x : ℕ → α) (hx : range x ⊆ s), s ⊆ ⋃ n, f (x n) (range_subset_iff.mp hx n) :=
begin
  let g := λ x, if hx : x ∈ s then f x hx else ∅,
  have hg : ∀ x ∈ s, g x ∈ 𝓝[s] x, { intros x hx, simp_rw [g, dif_pos hx], exact hf x hx },
  obtain ⟨x, hx, h⟩ := topological_space.cover_nat_nhds_within hg hs,
  simp_rw [g, dif_pos (range_subset_iff.mp hx _)] at h,
  refine ⟨x, hx, h⟩,
end

end topological_space

namespace set
namespace subtype
open _root_.subtype
variables {α : Type*}

lemma image_coe_eq_iff_eq_univ {s : set α} {t : set s} : (coe : s → α) '' t = s ↔ t = univ :=
by { convert coe_injective.image_injective.eq_iff, rw coe_image_univ }

@[simp] lemma preimage_coe_eq_univ {s t : set α} : (coe : s → α) ⁻¹' t = univ ↔ s ⊆ t :=
by rw [← inter_eq_right_iff_subset, ← image_preimage_coe, image_coe_eq_iff_eq_univ]

end subtype
end set
open set

section paracompact_space

/-- When `s : set X` is open and paracompact, we can find a precise refinement on `s`. Note that
 in this case we only get the locally finiteness condition on `s`, which is weaker than the local
 finiteness condition on all of `X` (the collection might not be locally finite on the boundary of
 `s`). -/
theorem precise_refinement_set' {ι X : Type*} [topological_space X] {s : set X}
  [paracompact_space s] (hs : is_open s)
  (u : ι → set X) (uo : ∀ i, is_open (u i)) (us : s ⊆ ⋃ i, u i) :
  ∃ (v : ι → set X), (∀ i, is_open (v i)) ∧ (s ⊆ ⋃ i, v i) ∧
  locally_finite (λ i, (coe : s → X) ⁻¹' v i) ∧ (∀ i, v i ⊆ s) ∧ (∀ i, v i ⊆ u i) :=
begin
  obtain ⟨v, vo, vs, vl, vu⟩ := precise_refinement (λ i, (coe : s → X) ⁻¹' u i)
    (λ i, (uo i).preimage continuous_subtype_coe)
    (by rwa [← preimage_Union, subtype.preimage_coe_eq_univ]),
  refine ⟨λ i, coe '' v i, λ i, hs.is_open_map_subtype_coe _ (vo i),
    by rw [← image_Union, vs, subtype.coe_image_univ],
    by simp_rw [preimage_image_eq _ subtype.coe_injective, vl],
    λ i, subtype.coe_image_subset _ _,
    by { intro i, rw [image_subset_iff], exact vu i }⟩,
end

lemma point_finite_of_locally_finite_coe_preimage {ι X : Type*} [topological_space X] {s : set X}
  {f : ι → set X} (hf : locally_finite (λ i, (coe : s → X) ⁻¹' f i)) (hfs : ∀ i, f i ⊆ s) {x : X} :
  finite {i | x ∈ f i} :=
begin
  by_cases hx : x ∈ s,
  { exact hf.point_finite ⟨x, hx⟩ },
  { have : ∀ i, x ∉ f i := λ i hxf, hx (hfs i hxf),
    simp only [this, set_of_false, finite_empty] }
end


end paracompact_space

section shrinking_lemma

variables {ι X : Type*} [topological_space X]
variables {u : ι → set X} {s : set X} [normal_space s]
/-
-- the last condition is false and should be replaced by something like `closure (v i) ∩ s ⊆ u i`
lemma exists_Union_eq_closure_subset_of_is_open (hs : is_open s) (uo : ∀ i, is_open (u i))
  (uf : ∀ x, finite {i | x ∈ u i}) (uU : s ⊆ ⋃ i, u i) :
  ∃ v : ι → set X, s ⊆ Union v ∧ (∀ i, is_open (v i)) ∧ ∀ i, closure (v i) ⊆ u i :=
begin
  obtain ⟨v, vU, vo, hv⟩ := exists_Union_eq_closure_subset
    (λ i, (uo i).preimage (continuous_subtype_coe : continuous (coe : s → X)))
    (λ x, uf x)
    (by simp_rw [← preimage_Union, subtype.preimage_coe_eq_univ, uU]),
  refine ⟨λ i, coe '' (v i), by simp_rw [← image_Union, vU, subtype.coe_image_univ],
    λ i, hs.is_open_map_subtype_coe _ (vo i), _⟩,
  simp_rw [hs.open_embedding_subtype_coe.to_embedding.closure_eq_preimage_closure_image] at hv,
  refine λ i, (preimage_subset_preimage_iff _).mp (hv i),
  sorry,
end

-- the last condition is false and should be replaced by something like `closure (v i) ∩ s ⊆ u i`
lemma exists_Union_eq_closure_subset_of_is_open (hs : is_open s) (uo : ∀ i, is_open (u i))
  (uf : ∀ x, finite {i | x ∈ u i}) (uU : s ⊆ ⋃ i, u i) :
  ∃ v : ι → set X, s ⊆ Union v ∧ (∀ i, is_closed (v i)) ∧ ∀ i, v i ⊆ u i :=
begin
  obtain ⟨v, vU, vo, hv⟩ := exists_Union_eq_closure_subset
    (λ i, (uo i).preimage (continuous_subtype_coe : continuous (coe : s → X)))
    (λ x, uf x)
    (by simp_rw [← preimage_Union, subtype.preimage_coe_eq_univ, uU]),
  refine ⟨λ i, coe '' (v i), by simp_rw [← image_Union, vU, subtype.coe_image_univ],
    λ i, hs.is_open_map_subtype_coe _ (vo i), _⟩,
  simp_rw [hs.open_embedding_subtype_coe.to_embedding.closure_eq_preimage_closure_image] at hv,
  refine λ i, (preimage_subset_preimage_iff _).mp (hv i),
  sorry,
end-/

end shrinking_lemma
