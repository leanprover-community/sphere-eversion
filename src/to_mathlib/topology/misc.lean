import topology.path_connected
import topology.urysohns_lemma
import topology.uniform_space.compact_separated
import linear_algebra.affine_space.independent
import analysis.normed_space.finite_dimension
import topology.algebra.floor_ring
import topology.shrinking_lemma
import topology.metric_space.emetric_paracompact
import to_mathlib.misc

noncomputable theory

open set function filter
open_locale unit_interval topological_space uniformity filter classical

section
 -- to connected

variables {α : Type*} [topological_space α] [connected_space α]
lemma is_connected_univ : is_connected (univ : set α) :=
⟨univ_nonempty, is_preconnected_univ⟩

end

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

open encodable option
variables {α β γ : Type*} [topological_space α] [topological_space β]
-- can we restate this nicely?

/-- Given a locally finite sequence of sets indexed by an encodable type, we can naturally reindex
  this sequence to get a sequence indexed by `ℕ` (by adding some `∅` values).
  This new sequence is still locally finite. -/
lemma decode₂_locally_finite {ι} [encodable ι] [topological_space α] {s : ι → set α}
  (hs : locally_finite s) : locally_finite (λ i, (s <$> decode₂ ι i).get_or_else ∅) :=
begin
  intro x,
  obtain ⟨U, hxU, hU⟩ := hs x,
  refine ⟨U, hxU, _⟩,
  have : encode ⁻¹' {i : ℕ | ((s <$> decode₂ ι i).get_or_else ∅ ∩ U).nonempty} =
     {i : ι | (s i ∩ U).nonempty},
  { simp_rw [preimage_set_of_eq, decode₂_encode, map_some, get_or_else_some] },
  rw [← this] at hU,
  refine finite_of_finite_preimage hU _,
  intros n hn,
  rw [← decode₂_ne_none_iff],
  intro h,
  simp_rw [mem_set_of_eq, h, map_none, get_or_else_none, empty_inter] at hn,
  exact (not_nonempty_empty hn).elim
end

open topological_space

variables {X : Type*} [emetric_space X] [locally_compact_space X] [second_countable_topology X]

lemma exists_locally_finite_subcover_of_locally {C : set X} (hC : is_closed C) {P : set X → Prop}
  (hP : antitone P) (h0 : P ∅) (hX : ∀ x ∈ C, ∃ V ∈ 𝓝 (x : X), P V) :
∃ (K : ℕ → set X) (W : ℕ → set X), (∀ n, is_compact (K n)) ∧ (∀ n, is_open (W n)) ∧
  (∀ n, P (W n)) ∧ (∀ n, K n ⊆ W n) ∧ locally_finite W ∧ C ⊆ ⋃ n, K n :=
begin
  choose V' hV' hPV' using set_coe.forall'.mp hX,
  choose V hV hVV' hcV using λ x : C, locally_compact_space.local_compact_nhds ↑x (V' x) (hV' x),
  simp_rw [← mem_interior_iff_mem_nhds] at hV,
  have : C ⊆ (⋃ x : C, interior (V x)) :=
  λ x hx, by { rw [mem_Union], exact ⟨⟨x, hx⟩, hV _⟩ },
  obtain ⟨s, hs, hsW₂⟩ := is_open_Union_countable (λ x, interior (V x)) (λ x, is_open_interior),
  rw [← hsW₂, bUnion_eq_Union] at this, clear hsW₂,
  obtain ⟨W, hW, hUW, hlW, hWV⟩ :=
    precise_refinement_set hC (λ x : s, interior (V x)) (λ x, is_open_interior) this,
  obtain ⟨K, hCK, hK, hKW⟩ :=
    exists_subset_Union_closed_subset hC (λ x : s, hW x) (λ x _, hlW.point_finite x) hUW,
  haveI : encodable s := hs.to_encodable,
  let K' : ℕ → set X := λ n, (K <$> (decode₂ s n)).get_or_else ∅,
  let W' : ℕ → set X := λ n, (W <$> (decode₂ s n)).get_or_else ∅,
  refine ⟨K', W', _, _, _, _, _, _⟩,
  { intro n, cases h : decode₂ s n with i,
    { simp_rw [K', h, map_none, get_or_else_none, is_compact_empty] },
    { simp_rw [K', h, map_some, get_or_else_some],
      exact compact_of_is_closed_subset (hcV i) (hK i)
        ((hKW i).trans $ (hWV i).trans interior_subset) }},
  { intro n, cases h : decode₂ s n,
    { simp_rw [W', h, map_none, get_or_else_none, is_open_empty] },
    { simp_rw [W', h, map_some, get_or_else_some, hW] }},
  { intro n, cases h : decode₂ s n with i,
    { simp_rw [W', h, map_none, get_or_else_none, h0] },
    { simp_rw [W', h, map_some, get_or_else_some], refine hP _ (hPV' i),
      refine (hWV i).trans (interior_subset.trans $ hVV' i) }},
  { intro n, cases h : decode₂ s n,
    { simp_rw [K', W', h, map_none] },
    { simp_rw [K', W', h, map_some, get_or_else_some, hKW] }},
  { exact decode₂_locally_finite hlW },
  { intros x hx, obtain ⟨i, hi⟩ := mem_Union.mp (hCK hx),
    refine mem_Union.mpr ⟨encode i, _⟩,
    simp_rw [K', decode₂_encode, map_some, get_or_else_some, hi] }
end

end

section -- to subset_properties

variables {α β γ : Type*} [topological_space α] [topological_space β] [topological_space γ]

lemma is_compact.eventually_forall_mem {x₀ : α} {K : set β} (hK : is_compact K)
  {f : α → β → γ} (hf : continuous ↿f) {U : set γ} (hU : ∀ y ∈ K, U ∈ 𝓝 (f x₀ y)) :
  ∀ᶠ x in 𝓝 x₀, ∀ y ∈ K, f x y ∈ U :=
hK.eventually_forall_of_forall_eventually $ λ y hy, hf.continuous_at.eventually $
  show U ∈ 𝓝 (↿f (x₀, y)), from hU y hy

end

section -- to separation

variables {α : Type*} [topological_space α]

/-
needs
import linear_algebra.affine_space.independent
import analysis.normed_space.finite_dimension
-/
lemma is_open_set_affine_independent (𝕜 E : Type*) {ι : Type*} [nondiscrete_normed_field 𝕜]
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

-- a version of `precise_refinement_set` for open `s`.
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

-- this lemma is currently formulated a little weirdly, since we have a collection of open sets
-- as the input and a collection of closed/compact sets as output.
-- Perhaps we can formulate it so that the input is a collection of compact sets whose interiors
-- cover s.
lemma exists_subset_Union_interior_of_is_open (hs : is_open s) (uo : ∀ i, is_open (u i))
  (uc : ∀ i, is_compact (closure (u i)))
  (us : ∀ i, closure (u i) ⊆ s)
  (uf : ∀ x ∈ s, finite {i | x ∈ u i}) (uU : s ⊆ ⋃ i, u i) :
  ∃ v : ι → set X, s ⊆ (⋃ i, interior (v i)) ∧ (∀ i, is_compact (v i)) ∧ ∀ i, v i ⊆ u i :=
begin
  obtain ⟨v, vU, vo, hv⟩ := exists_Union_eq_closure_subset
    (λ i, (uo i).preimage (continuous_subtype_coe : continuous (coe : s → X)))
    (λ x, uf x x.prop)
    (by simp_rw [← preimage_Union, subtype.preimage_coe_eq_univ, uU]),
  have : ∀ i, is_compact (closure ((coe : _ → X) '' (v i))),
  { intro i, refine compact_of_is_closed_subset (uc i) is_closed_closure _,
    apply closure_mono, rw image_subset_iff, refine subset_closure.trans (hv i) },
  refine ⟨λ i, closure (coe '' (v i)), _, this, _⟩,
  { refine subset.trans _ (Union_mono $
      λ i, interior_maximal subset_closure (hs.is_open_map_subtype_coe _ (vo i))),
    simp_rw [← image_Union, vU, subtype.coe_image_univ] },
  { intro i,
    have : coe '' v i ⊆ u i,
    { rintro _ ⟨x, hx, rfl⟩, exact hv i (subset_closure hx) },
    intros x hx,
    have hxs : x ∈ s := us i (closure_mono this hx),
    have : (⟨x, hxs⟩ : s) ∈ closure (v i),
    { rw embedding_subtype_coe.closure_eq_preimage_closure_image (v i), exact hx },
    exact hv i this }
end

end shrinking_lemma
