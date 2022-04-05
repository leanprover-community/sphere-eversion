import topology.path_connected
import topology.urysohns_lemma
import topology.uniform_space.compact_separated
import linear_algebra.affine_space.independent
import analysis.normed_space.finite_dimension
import topology.algebra.floor_ring
import topology.shrinking_lemma
import topology.metric_space.emetric_paracompact
import analysis.convex.topology
import to_mathlib.misc

noncomputable theory

open set function filter topological_space
open_locale unit_interval topological_space uniformity filter classical

section
 -- to connected

variables {α : Type*} [topological_space α] [connected_space α]
lemma is_connected_univ : is_connected (univ : set α) :=
⟨univ_nonempty, is_preconnected_univ⟩

end

section
-- to metric space
variables {E F : Type*} [metric_space E] [metric_space F]
@[simp] lemma dist_prod_same_left {x : E} {y₁ y₂ : F} : dist (x, y₁) (x, y₂) = dist y₁ y₂ :=
by simp [prod.dist_eq, dist_nonneg]

end

section
-- to normed.group.basic


section
variables {E : Type*} [semi_normed_group E]
@[simp] theorem dist_self_add_right (g h : E) : dist g (g + h) = ∥h∥ :=
by rw [← dist_zero_left, ← dist_add_left g 0 h, add_zero]

@[simp] theorem dist_self_add_left (g h : E) : dist (g + h) g = ∥h∥ :=
by rw [dist_comm, dist_self_add_right]
end

end

section fract

open int
/- properties of the (dis)continuity of `int.fract` on `ℝ`. -/

lemma fract_eventually_eq {x : ℝ}
  (h : fract x ≠ 0) : fract =ᶠ[𝓝 x] (λ x', x' - floor x) :=
sorry

lemma is_open.preimage_fract' {s : set ℝ} (hs : is_open s)
  (h2s : 0 ∈ s → s ∈ 𝓝[<] (1 : ℝ)) : is_open (fract ⁻¹' s) :=
sorry

lemma is_open.preimage_fract {s : set ℝ} (hs : is_open s)
  (h2s : (0 : ℝ) ∈ s → (1 : ℝ) ∈ s) : is_open (fract ⁻¹' s) :=
hs.preimage_fract' $ λ h, nhds_within_le_nhds $ hs.mem_nhds (h2s h)

-- is `sᶜ ∉ 𝓝[<] (1 : ℝ)` equivalent to something like `cluster_pt (𝓝[Iio (1 : ℝ) ∩ s] (1 : ℝ)` ?
lemma is_closed.preimage_fract {s : set ℝ} (hs : is_closed s)
  (h2s : sᶜ ∉ 𝓝[<] (1 : ℝ) → (0 : ℝ) ∈ s) : is_closed (fract ⁻¹' s) :=
is_open_compl_iff.mp $ hs.is_open_compl.preimage_fract' $ λ h, by_contra $ λ h', h $ h2s h'

lemma fract_preimage_mem_nhds' {s : set ℝ} {x : ℝ} (h1 : fract x ≠ 0 → s ∈ 𝓝 (fract x))
  (h2 : fract x = 0 → s ∈ 𝓝[<] (1 : ℝ))
  (h3 : fract x = 0 → s ∈ 𝓝[>] (0 : ℝ)) : fract ⁻¹' s ∈ 𝓝 x :=
sorry

lemma fract_preimage_mem_nhds {s : set ℝ} {x : ℝ} (h1 : s ∈ 𝓝 (fract x))
  (h2 : fract x = 0 → s ∈ 𝓝 (1 : ℝ)) : fract ⁻¹' s ∈ 𝓝 x :=
fract_preimage_mem_nhds' (λ _, h1) (λ hx, nhds_within_le_nhds (h2 hx))
  (λ hx, by { rw [hx] at h1, exact nhds_within_le_nhds h1 })

-- lemma comp_fract_preimage_mem_nhds {α β : Type*} [topological_space α] [topological_space β]
--   {f : α → ℝ → β} {g : α → ℝ} {s : set β} {x : α} (hf : continuous_at ↿f (x, fract (g x)))
--   (hg : continuous_at g x) (hs : s ∈ 𝓝 (f x (fract (g x))))
--   (h : fract (g x) = 0 → g '' ((λ x, f x (fract (g x))) ⁻¹' s) ∈ 𝓝[<] (1 : ℝ)) /- or something -/ :
--     (λ x, f x (fract (g x))) ⁻¹' s ∈ 𝓝 x :=
-- sorry

end fract

section
-- to normed_space
variables {E F : Type*} [normed_group E] [normed_group F]
variables [normed_space ℝ E] [normed_space ℝ F]
lemma dist_smul_add_one_sub_smul_le {r : ℝ} {x y : E} (h : r ∈ unit_interval) :
  dist (r • x + (1 - r) • y) x ≤ dist y x :=
by sorry

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

section -- to constructions

variables {X Y Z : Type*} [topological_space X] [topological_space Y] [topological_space Z]

lemma continuous.fst' {f : X → Z} (hf : continuous f) : continuous (λ x : X × Y, f x.fst) :=
hf.comp continuous_fst

lemma continuous.snd' {f : Y → Z} (hf : continuous f) : continuous (λ x : X × Y, f x.snd) :=
hf.comp continuous_snd

lemma continuous_at.fst' {f : X → Z} {x : X} {y : Y} (hf : continuous_at f x) :
  continuous_at (λ x : X × Y, f x.fst) (x, y) :=
continuous_at.comp hf continuous_at_fst

lemma continuous_at.fst'' {f : X → Z} {x : X × Y} (hf : continuous_at f x.fst) :
  continuous_at (λ x : X × Y, f x.fst) x :=
hf.comp continuous_at_fst

lemma continuous_at.snd' {f : Y → Z} {x : X} {y : Y} (hf : continuous_at f y) :
  continuous_at (λ x : X × Y, f x.snd) (x, y) :=
continuous_at.comp hf continuous_at_snd

lemma continuous_at.snd'' {f : Y → Z} {x : X × Y} (hf : continuous_at f x.snd) :
  continuous_at (λ x : X × Y, f x.snd) x :=
hf.comp continuous_at_snd

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


section
variables {α β : Type*} [linear_order α] {a b x c : α} (h : a ≤ b)

-- @[simp] lemma proj_Icc_eq_min : proj_Icc x = min 1 x ↔ 0 ≤ x :=
-- by simp_rw [proj_I_def, max_eq_right_iff, le_min_iff, zero_le_one, true_and]

-- lemma min_proj_I (h2 : a ≤ c) : min c (proj_Icc x) = proj_I (min c x) :=
-- by { cases le_total c x with h3 h3; simp [h2, h3, proj_I_le_iff, proj_I_eq_min.mpr],
--      simp [proj_I_eq_min.mpr, h2.trans h3, min_left_comm c, h3] }
end

variables {α β : Type*} [linear_ordered_semiring α] {x c : α}

def proj_I : α → α := λ x, proj_Icc (0 : α) 1 zero_le_one x

lemma proj_I_def : proj_I x = max 0 (min 1 x) := rfl

lemma proj_Icc_eq_proj_I : (proj_Icc (0 : α) 1 zero_le_one x : α) = proj_I x := rfl

lemma proj_I_of_le_zero (hx : x ≤ 0) : proj_I x = 0 :=
congr_arg coe $ proj_Icc_of_le_left _ hx

@[simp] lemma proj_I_zero : proj_I (0 : α) = 0 :=
congr_arg coe $ proj_Icc_left _

lemma proj_I_of_one_le (hx : 1 ≤ x) : proj_I x = 1 :=
congr_arg coe $ proj_Icc_of_right_le _ hx

@[simp] lemma proj_I_one : proj_I (1 : α) = 1 :=
congr_arg coe $ proj_Icc_right _

@[simp] lemma proj_I_eq_zero [nontrivial α] : proj_I x = 0 ↔ x ≤ 0 :=
by { rw [← proj_Icc_eq_left (@zero_lt_one α _ _), subtype.ext_iff], refl }

@[simp] lemma proj_I_eq_one : proj_I x = 1 ↔ 1 ≤ x :=
by { rw [← proj_Icc_eq_right (@zero_lt_one α _ _), subtype.ext_iff], refl }

lemma proj_I_mem_Icc : proj_I x ∈ Icc (0 : α) 1 :=
(proj_Icc (0 : α) 1 zero_le_one x).prop

lemma proj_I_eq_self : proj_I x = x ↔ x ∈ Icc (0 : α) 1 :=
⟨λ h, h ▸ proj_I_mem_Icc, λ h, congr_arg coe $ proj_Icc_of_mem _ h⟩

@[simp] lemma proj_I_proj_I : proj_I (proj_I x) = proj_I x :=
proj_I_eq_self.mpr proj_I_mem_Icc

@[simp] lemma proj_Icc_proj_I :
  proj_Icc (0 : α) 1 zero_le_one (proj_I x) = proj_Icc 0 1 zero_le_one x :=
proj_Icc_of_mem _ proj_I_mem_Icc

@[simp] lemma range_proj_I : range (proj_I) = Icc 0 1 :=
by rw [proj_I, range_comp, range_proj_Icc, image_univ, subtype.range_coe]

lemma monotone_proj_I : monotone (proj_I : α → α) :=
monotone_proj_Icc _

lemma strict_mono_on_proj_I : strict_mono_on proj_I (Icc (0 : α) 1) :=
strict_mono_on_proj_Icc _

lemma proj_I_le_max : proj_I x ≤ max 0 x :=
max_le_max le_rfl $ min_le_right _ _

lemma min_le_proj_I : min 1 x ≤ proj_I x :=
le_max_right _ _

lemma proj_I_le_iff : proj_I x ≤ c ↔ 0 ≤ c ∧ (1 ≤ c ∨ x ≤ c) :=
by simp_rw [proj_I_def, max_le_iff, min_le_iff]

@[simp] lemma proj_I_eq_min : proj_I x = min 1 x ↔ 0 ≤ x :=
by simp_rw [proj_I_def, max_eq_right_iff, le_min_iff, zero_le_one, true_and]

lemma min_proj_I (h2 : 0 ≤ c) : min c (proj_I x) = proj_I (min c x) :=
by { cases le_total c x with h3 h3; simp [h2, h3, proj_I_le_iff, proj_I_eq_min.mpr],
     simp [proj_I_eq_min.mpr, h2.trans h3, min_left_comm c, h3] }

lemma continuous_proj_I [topological_space α] [order_topology α] :
  continuous (proj_I : α → α) :=
continuous_proj_Icc.subtype_coe

lemma proj_I_mapsto {α : Type*} [linear_ordered_semiring α] {s : set α} (h0s : (0 : α) ∈ s)
  (h1s : (1 : α) ∈ s) : maps_to proj_I s s :=
λ x hx, (le_total 1 x).elim (λ h2x, by rwa [proj_I_eq_one.mpr h2x]) $
  λ h2x, (le_total 0 x).elim (λ h3x, by rwa [proj_I_eq_self.mpr ⟨h3x, h2x⟩]) $
  λ h3x, by rwa [proj_I_eq_zero.mpr h3x]
-- about path.truncate

lemma truncate_proj_I_right {X : Type*} [topological_space X] {a b : X}
  (γ : path a b) (t₀ t₁ : ℝ) (s : I) :
  γ.truncate t₀ (proj_I t₁) s = γ.truncate t₀ t₁ s :=
begin
  simp_rw [path.truncate, path.coe_mk, path.extend, Icc_extend, function.comp],
  rw [min_proj_I (s.prop.1.trans $ le_max_left _ _), proj_Icc_proj_I],
end

end

section
-- consequences of the extreme value theorem

lemma is_compact.continuous_Sup {α β γ : Type*}
  [conditionally_complete_linear_order α] [topological_space α]
  [order_topology α] [topological_space γ] [topological_space β] {f : γ → β → α}
  {K : set β} (hK : is_compact K) (hf : continuous ↿f) :
    continuous (λ x, Sup (f x '' K)) :=
sorry

lemma is_compact.continuous_Inf {α β γ : Type*}
  [conditionally_complete_linear_order α] [topological_space α]
  [order_topology α] [topological_space γ] [topological_space β] {f : γ → β → α}
  {K : set β} (hK : is_compact K) (hf : continuous ↿f) :
    continuous (λ x, Inf (f x '' K)) :=
@is_compact.continuous_Sup (order_dual α) β γ _ _ _ _ _ _ _ hK hf

lemma is_compact.Sup_lt_of_continuous {α β : Type*}
  [conditionally_complete_linear_order α] [topological_space α]
  [order_topology α] [topological_space β] {f : β → α}
  {K : set β} (hK : is_compact K) (hf : continuous f) (y : α) :
    Sup (f '' K) < y ↔ ∀ x ∈ K, f x < y :=
sorry

lemma is_compact.lt_Inf_of_continuous {α β : Type*}
  [conditionally_complete_linear_order α] [topological_space α]
  [order_topology α] [topological_space β] {f : β → α}
  {K : set β} (hK : is_compact K) (hf : continuous f) (y : α) :
    y < Inf (f '' K) ↔ ∀ x ∈ K, y < f x :=
@is_compact.Sup_lt_of_continuous (order_dual α) β _ _ _ _ _ _ hK hf y


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

section
/-- A locally connected space is a space where every neighborhood filter has a basis of open
  connected sets. -/
class locally_connected_space (α : Type*) [topological_space α] : Prop :=
(has_basis : ∀ x, (𝓝 x).has_basis (λ s : set α, is_open s ∧ x ∈ s ∧ is_connected s) id)

-- class locally_connected_space (α : Type*) [topological_space α] : Prop :=
-- (exists_connected_neihborhoods : ∃ (b : set (set α)), is_topological_basis b ∧
--   ∀ s ∈ b, is_connected s)

variables {α : Type*} [topological_space α]

lemma locally_connected_space_of_connected_subsets
  (h : ∀ (x : α) (U ∈ 𝓝 x), ∃ V ⊆ U, is_open V ∧ x ∈ V ∧ is_connected V) :
  locally_connected_space α :=
begin
  constructor,
  intro x,
  constructor,
  intro t,
  split,
  { intro ht, obtain ⟨V, hVU, hV⟩ := h x t ht, exact ⟨V, hV, hVU⟩ },
  { rintro ⟨V, ⟨hV, hxV, -⟩, hVU⟩, refine mem_nhds_iff.mpr ⟨V, hVU, hV, hxV⟩ }
end

end

section convex

variables {E : Type*} [add_comm_group E] [module ℝ E] [topological_space E]
  [topological_add_group E] [has_continuous_smul ℝ E] {s : set E}

lemma convex.is_preconnected' (hs : convex ℝ s) : is_preconnected s :=
by { rcases s.eq_empty_or_nonempty with rfl|h, exact is_preconnected_empty,
     exact (hs.is_path_connected h).is_connected.is_preconnected }

end convex

section

open metric

lemma continuous.inf_dist {α β : Type*} [topological_space α] [pseudo_metric_space β] {s : set β}
  {f : α → β} (hf : continuous f) : continuous (λ x, inf_dist (f x) s) :=
(continuous_inf_dist_pt _).comp hf

end

section normed_space
open metric

variables {E : Type*} [normed_group E] [normed_space ℝ E]

lemma is_preconnected_ball (x : E) (r : ℝ) : is_preconnected (ball x r) :=
(convex_ball x r).is_preconnected'

lemma is_connected_ball {x : E} {r : ℝ} : is_connected (ball x r) ↔ 0 < r :=
begin
  rw [← @nonempty_ball _ _ x],
  refine ⟨λ h, h.nonempty, λ h, ((convex_ball x r).is_path_connected $ h).is_connected⟩
end

-- make metric.mem_nhds_iff protected
instance normed_space.locally_connected_space : locally_connected_space E :=
begin
  apply locally_connected_space_of_connected_subsets,
  intros x U hU,
  obtain ⟨ε, hε, hU⟩ := metric.mem_nhds_iff.mp hU,
  refine ⟨_, hU, is_open_ball, mem_ball_self hε, is_connected_ball.mpr hε⟩
end

end normed_space

-- TODO: replace mathlib's `connected_component_in`, which is never used, by the following.

section connected_comp_in

variables {α : Type*} [topological_space α] {F s : set α} {x y : α}

/-- Given a set `F` in a topological space `α` and a point `x : α`, the connected
component of `x` in `F` is the connected component of `x` in the subtype `F` seen as
a set in `α`. This definition does not make sense if `x` is not in `F` so we return the
empty set in this case. -/
def connected_comp_in (F : set α) (x : α) : set α :=
if h : x ∈ F then coe '' (connected_component (⟨x, h⟩ : F)) else ∅

lemma connected_comp_in_subset (F : set α) (x : α) :
  connected_comp_in F x ⊆ F :=
by { rw [connected_comp_in], split_ifs; simp }

lemma mem_connected_comp_in_self (h : x ∈ F) : x ∈ connected_comp_in F x :=
by simp [connected_comp_in, mem_connected_component, h]

lemma connected_comp_in_nonempty_iff : (connected_comp_in F x).nonempty ↔ x ∈ F :=
by { rw [connected_comp_in], split_ifs; simp [is_connected_connected_component.nonempty, h] }

lemma is_preconnected.subset_connected_comp_in (hs : is_preconnected s) (hxs : x ∈ s)
  (hsF : s ⊆ F) : s ⊆ connected_comp_in F x :=
begin
  have : is_preconnected ((coe : F → α) ⁻¹' s),
  { refine embedding_subtype_coe.to_inducing.is_preconnected_image.mp _,
    rwa [subtype.image_preimage_coe, inter_eq_left_iff_subset.mpr hsF] },
  have h2xs : (⟨x, hsF hxs⟩ : F) ∈ coe ⁻¹' s := by { rw [mem_preimage], exact hxs },
  have := this.subset_connected_component h2xs,
  rw [connected_comp_in, dif_pos (hsF hxs)],
  refine subset.trans _ (image_subset _ this),
  rw [subtype.image_preimage_coe, inter_eq_left_iff_subset.mpr hsF]
end

lemma is_preconnected_connected_comp_in : is_preconnected (connected_comp_in F x) :=
begin
  rw [connected_comp_in], split_ifs,
  { refine embedding_subtype_coe.to_inducing.is_preconnected_image.mpr
      is_preconnected_connected_component },
  { exact is_preconnected_empty },
end

lemma is_connected_connected_comp_in : is_connected (connected_comp_in F x) ↔ x ∈ F :=
by simp_rw [← connected_comp_in_nonempty_iff, is_connected, is_preconnected_connected_comp_in,
  and_true]

lemma is_preconnected.connected_comp_in (h : is_preconnected F) (hx : x ∈ F) :
  connected_comp_in F x = F :=
(connected_comp_in_subset F x).antisymm (h.subset_connected_comp_in hx subset_rfl)

lemma connected_comp_in_eq (h : y ∈ connected_comp_in F x) :
  connected_comp_in F x = connected_comp_in F y :=
begin
  have hx : x ∈ F := connected_comp_in_nonempty_iff.mp ⟨y, h⟩,
  simp_rw [connected_comp_in, dif_pos hx] at h ⊢,
  obtain ⟨⟨y, hy⟩, h2y, rfl⟩ := h,
  simp_rw [subtype.coe_mk, dif_pos hy, connected_component_eq h2y]
end

lemma connected_comp_in_mem_nhds [locally_connected_space α] (h : F ∈ 𝓝 x) :
  connected_comp_in F x ∈ 𝓝 x :=
begin
  rw (locally_connected_space.has_basis x).mem_iff at h,
  obtain ⟨s, ⟨h1s, hxs, h2s⟩, hsF⟩ := h,
  exact mem_nhds_iff.mpr ⟨s, h2s.is_preconnected.subset_connected_comp_in hxs hsF, h1s, hxs⟩
end

-- lemma interior_connected_comp_in {F : set α} {x : α} (h : x ∉ frontier F) :
--   interior (connected_comp_in F x) = connected_comp_in (interior F) x :=
-- sorry

lemma is_open.connected_comp_in [locally_connected_space α] {F : set α} {x : α} (hF : is_open F) :
  is_open (connected_comp_in F x) :=
begin
  rw [is_open_iff_mem_nhds],
  intros y hy,
  rw [connected_comp_in_eq hy],
  exact connected_comp_in_mem_nhds (is_open_iff_mem_nhds.mp hF y $ connected_comp_in_subset F x hy),
end

end connected_comp_in

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
