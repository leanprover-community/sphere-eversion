import to_mathlib.geometry.manifold.misc_manifold

open bundle set function filter
open_locale manifold topological_space

namespace local_equiv

variables {α β γ : Type*}

/-- This might be useful to formulate many "composition of `f` and `g` is given by `h`" notions,
like `coord_change_comp` in various structures. -/
def eq_on_common_source (e e' : local_equiv α β) : Prop :=
∀ x ∈ e.source ∩ e'.source, e x = e' x

end local_equiv

namespace topological_vector_bundle

variables {R : Type*} {B : Type*} {F : Type*} {E : B → Type*}
variables [nontrivially_normed_field R] [∀ x, add_comm_monoid (E x)] [∀ x, module R (E x)]
  [normed_add_comm_group F] [normed_space R F] [topological_space B]
  [topological_space (total_space E)]

variables {HB : Type*} [topological_space HB]

/-- The chart of the total space by a bundle given by a trivialization along a chart of the base
  space. -/
def chart_at (e : trivialization R F E) (f : local_homeomorph B HB) :
  local_homeomorph (total_space E) (model_prod HB F) :=
e.to_local_homeomorph.trans $ f.prod $ local_homeomorph.refl F

variables (R F E) [∀ x, topological_space (E x)]

/-- The total space of a topological vector bundle forms a charted space.
Currently not an instance, because it creates the metavariable `R`, but it might be fine to change
this. -/
def total_space.to_charted_space [topological_vector_bundle R F E] [charted_space HB B] :
  charted_space (model_prod HB F) (total_space E) :=
{ atlas := image2 chart_at (trivialization_atlas R F E) (atlas HB B),
  chart_at := λ x, chart_at (trivialization_at R F E x.proj) (charted_space.chart_at HB x.proj),
  mem_chart_source := λ x, by simp only [chart_at, trivialization.mem_source,
    mem_base_set_trivialization_at R F E x.proj] with mfld_simps,
  chart_mem_atlas := λ x, mem_image2_of_mem (trivialization_mem_atlas R F E x.proj)
    (chart_mem_atlas HB x.proj) }

end topological_vector_bundle

namespace model_with_corners

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
  {H : Type*} [topological_space H]
  {M : Type*} [topological_space M] (f : local_homeomorph M H) (I : model_with_corners 𝕜 E H)

lemma nhds_within_eq_bot {x : H} {s : set H} : 𝓝[s] x = ⊥ ↔ x ∉ closure s :=
by rw [mem_closure_iff_nhds_within_ne_bot, not_ne_bot]

lemma image_mem_nhds_within_of_mem {x : E} {s : set H} (hs : s ∈ 𝓝 (I.symm x)) :
  I '' s ∈ 𝓝[range I] x :=
begin
  by_cases hx : x ∈ range I,
  { obtain ⟨x, rfl⟩ := hx, rw [I.left_inv] at hs, exact I.image_mem_nhds_within hs },
  { rw [← I.closed_range.closure_eq, ← nhds_within_eq_bot] at hx, rw [hx], exact mem_bot }
end

/-- Given a chart `f` on a manifold with corners, `f.extend` is the extended chart to the model
vector space. -/
@[simp, mfld_simps] def _root_.local_homeomorph.extend : local_equiv M E :=
f.to_local_equiv ≫ I.to_local_equiv

lemma _root_.local_homeomorph.extend_source : (f.extend I).source = f.source :=
by rw [local_homeomorph.extend, local_equiv.trans_source, I.source_eq, preimage_univ, inter_univ]

lemma _root_.local_homeomorph.extend_target : (f.extend I).target = I '' f.target :=
by rw [local_homeomorph.extend, local_equiv.trans_target, I.target_eq, I.image_eq, inter_comm,
  I.to_local_equiv_coe_symm]

end model_with_corners

namespace basic_smooth_vector_bundle_core

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
  {E' : Type*} [normed_add_comm_group E'] [normed_space 𝕜 E']
  {F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]
  {H : Type*} [topological_space H] {I : model_with_corners 𝕜 E H}
  {H' : Type*} [topological_space H'] {I' : model_with_corners 𝕜 E' H'}
  {G : Type*} [topological_space G] {J : model_with_corners 𝕜 F G}
  {M : Type*} [topological_space M] [charted_space H M]
  {M' : Type*} [topological_space M'] [charted_space H' M']
  {N : Type*} [topological_space N] [charted_space G N]
variables {f : M → M'} {m n : ℕ∞} {s : set M} {x : M}
variables [smooth_manifold_with_corners I M] (Z : basic_smooth_vector_bundle_core I M E')

/-- A version of `cont_mdiff_at_iff_target` when the codomain is the total space of
  a `basic_smooth_vector_bundle_core`. The continuity condition in the RHS is weaker. -/
lemma cont_mdiff_within_at_iff_target {f : N → Z.to_topological_vector_bundle_core.total_space}
  {x : N} {s : set N} {n : ℕ∞} :
  cont_mdiff_within_at J (I.prod 𝓘(𝕜, E')) n f s x ↔
    continuous_within_at (bundle.total_space.proj ∘ f) s x ∧
    cont_mdiff_within_at J 𝓘(𝕜, E × E') n (ext_chart_at (I.prod 𝓘(𝕜, E')) (f x) ∘ f) s x :=
begin
  let Z' := Z.to_topological_vector_bundle_core,
  rw [cont_mdiff_within_at_iff_target, and.congr_left_iff],
  refine λ hf, ⟨λ h, Z'.continuous_proj.continuous_within_at.comp h (maps_to_univ _ _), λ h, _⟩,
  sorry -- need trivialization.continuous_within_at_of_comp_left
  -- exact (Z'.local_triv ⟨chart_at _ (f x).1, chart_mem_atlas _ _⟩).to_fiber_bundle_trivialization
  --   .continuous_within_at_of_comp_left h (mem_chart_source _ _) (h.prod hf.continuous_at.snd)
end

lemma cont_mdiff_within_at_iff {x₀ : N} {s : set N} {n : ℕ∞}
  {f : N → Z.to_topological_vector_bundle_core.total_space} :
  cont_mdiff_within_at J (I.prod 𝓘(𝕜, E')) n f s x₀ ↔
  cont_mdiff_within_at J I n (λ x, (f x).1) s x₀ ∧
  cont_mdiff_within_at J 𝓘(𝕜, E') n (λ x, Z.coord_change
    (achart H (f x).1) (achart H (f x₀).1) (chart_at H (f x).1 (f x).1) (f x).2) s x₀ :=
begin
  refine ⟨λ h, ⟨_, _⟩, λ h, _⟩,
  { apply (Z.cont_mdiff_proj _).comp_cont_mdiff_within_at x₀ h },
  { rw [Z.cont_mdiff_within_at_iff_target] at h,
    exact (cont_diff_at_snd.cont_mdiff_at.comp_cont_mdiff_within_at _ h.2) },
  { rw [Z.cont_mdiff_within_at_iff_target],
    exact ⟨h.1.continuous_within_at,
      (cont_mdiff_at_ext_chart_at.comp_cont_mdiff_within_at _ h.1).prod_mk_space h.2⟩ }
end

lemma cont_mdiff_at_iff {x₀ : N} {n : ℕ∞}
  {f : N → Z.to_topological_vector_bundle_core.total_space} :
  cont_mdiff_at J (I.prod 𝓘(𝕜, E')) n f x₀ ↔
  cont_mdiff_at J I n (λ x, (f x).1) x₀ ∧
  cont_mdiff_at J 𝓘(𝕜, E') n (λ x, Z.coord_change
    (achart H (f x).1) (achart H (f x₀).1) (chart_at H (f x).1 (f x).1) (f x).2) x₀ :=
begin
  refine ⟨λ h, ⟨_, _⟩, λ h, _⟩,
  { apply (Z.cont_mdiff_proj _).comp x₀ h },
  { rw [Z.cont_mdiff_at_iff_target] at h, exact (cont_diff_at_snd.cont_mdiff_at.comp _ h.2) },
  { rw [Z.cont_mdiff_at_iff_target],
    exact ⟨h.1.continuous_at, (cont_mdiff_at_ext_chart_at.comp _ h.1).prod_mk_space h.2⟩ }
end

lemma _root_.cont_mdiff_at.proj' {x₀ : M} {v₀ : E'} {n : ℕ∞}
  {f : M → N} (hf : cont_mdiff_at I J n f x₀) :
  cont_mdiff_at (I.prod 𝓘(𝕜, E')) J n
    (λ x : Z.to_topological_vector_bundle_core.total_space, f x.1) ⟨x₀, v₀⟩ :=
cont_mdiff_at.comp _ hf (Z.cont_mdiff_proj _)

end basic_smooth_vector_bundle_core

section smooth_manifold_with_corners
open smooth_manifold_with_corners

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
  {E' : Type*} [normed_add_comm_group E'] [normed_space 𝕜 E']
  {H : Type*} [topological_space H] {I : model_with_corners 𝕜 E H}
  {H' : Type*} [topological_space H'] {I' : model_with_corners 𝕜 E' H'}
  {M : Type*} [topological_space M] [charted_space H M]
  {M' : Type*} [topological_space M'] [charted_space H' M']
variables {f : M → M'} {m n : ℕ∞} {s : set M} {x x₀ : M}

variables [smooth_manifold_with_corners I M] [smooth_manifold_with_corners I' M']

/-- One can reformulate smoothness within a set at a point as continuity within this set at this
point, and smoothness in any chart containing that point. -/
lemma cont_mdiff_within_at_iff_of_mem_maximal_atlas
  {c : local_homeomorph M H} (hc : c ∈ maximal_atlas I M)
  {d : local_homeomorph M' H'} (hd : d ∈ maximal_atlas I' M')
  (hx : x ∈ c.source) (hy : f x ∈ d.source) :
  cont_mdiff_within_at I I' n f s x ↔ continuous_within_at f s x ∧
    cont_diff_within_at 𝕜 n (d.extend I' ∘ f ∘ (c.extend I).symm)
    ((c.extend I).symm ⁻¹' s ∩ range I)
    (c.extend I x) :=
(cont_diff_within_at_local_invariant_prop I I' n).lift_prop_within_at_indep_chart hc hx hd hy


section boundary

variables (I M)

/-- An element is on the boundary of a manifold `M` if its chart maps it to the frontier of the
model space. Note: this also includes all corners of `M`. -/
def boundary : set M := {x : M | ext_chart_at I x x ∈ frontier (range I) }

variables {I M}

lemma mem_boundary {x : M} : x ∈ boundary I M ↔ ext_chart_at I x x ∈ frontier (range I) := iff.rfl

-- /-- All charts agree on whether you are at the boundary. -/
-- lemma mem_boundary_iff_of_mem {x x' : M} (hx : x ∈ (ext_chart_at I x').source) :
--   x ∈ boundary I M ↔ ext_chart_at I x' x ∈ frontier (range I) :=
-- by admit -- likely not going to be used

end boundary

/-
todo: `((ext_chart_at I x).symm ⁻¹' s ∩ range I)` in `cont_mdiff.lean` is not very nice,
since it doesn't have to be a subset of `(ext_chart_at I x).target` when `s` is a subset of the
source, which is annoying.
Of course, near `(ext_chart_at I x x)` it's the same.
`(ext_chart_at I x) '' s` is better.
Also do this in file `mfderiv`

This is a trade-off: the preimage can be nicer since `I.symm` is assumed to be continuous
everywhere, which gives some nice properties.
-/


variables {F G F' : Type*}
variables [normed_add_comm_group F] [normed_add_comm_group G] [normed_add_comm_group F']
variables [normed_space 𝕜 F] [normed_space 𝕜 G] [normed_space 𝕜 F']

-- lemma cont_mdiff_within_at.clm_comp {g : M → F →L[𝕜] G} {f : M → E →L[𝕜] F} {s : set M} {x : M}
--   (hg : cont_mdiff_within_at I 𝓘(𝕜, F →L[𝕜] G) n g s x)
--   (hf : cont_mdiff_within_at I 𝓘(𝕜, E →L[𝕜] F) n f s x) :
--   cont_mdiff_within_at I 𝓘(𝕜, E →L[𝕜] G) n (λ x, (g x).comp (f x)) s x :=
-- sorry

lemma cont_mdiff_at_tangent_bundle {n : ℕ∞} {f : M → tangent_bundle I' M'} :
  cont_mdiff_at I I'.tangent n f x₀ ↔
  cont_mdiff_at I I' n (λ x, (f x).1) x₀ ∧
  cont_mdiff_at I 𝓘(𝕜, E') n (λ x, (tangent_bundle_core I' M').coord_change
    (achart H' (f x).1) (achart H' (f x₀).1) (chart_at H' (f x).1 (f x).1) (f x).2) x₀ :=
(tangent_bundle_core I' M').cont_mdiff_at_iff

theorem cont_mdiff_at.tangent_map_within {v₀ : tangent_space I x₀}
  (hf : cont_mdiff_at I I' n f x₀) (hmn : m + 1 ≤ n) (hs : unique_mdiff_on I s) :
  cont_mdiff_at I.tangent I'.tangent m (tangent_map_within I I' f s) ⟨x₀, v₀⟩ :=
begin
  let z₀ : tangent_bundle I M := ⟨x₀, v₀⟩,
  rw [(tangent_bundle_core I' M').cont_mdiff_at_iff],
  split,
  { rw [← enat.succ_def] at hmn, exact (hf.of_le $ (order.le_succ m).trans hmn).proj' _ },
  have h1 : cont_mdiff_at I.tangent 𝓘(𝕜, E) m (λ x, (ext_chart_at (I.prod 𝓘(𝕜, E)) z₀ x).2) z₀ :=
    cont_diff_at_snd.cont_mdiff_at.comp _ cont_mdiff_at_ext_chart_at,
  convert ((hf.mfderiv' hmn).proj' (tangent_bundle_core I M)).clm_apply h1,
  ext ⟨x, v⟩,
  dsimp only,
  sorry
end

theorem cont_mdiff_on.tangent_map_within
  (hf : cont_mdiff_on I I' n f s) (hmn : m + 1 ≤ n) (hs : unique_mdiff_on I s) :
  cont_mdiff_on I.tangent I'.tangent m (tangent_map_within I I' f s)
  ((tangent_bundle.proj I M) ⁻¹' s) :=
begin
  intros x hx,
  rw [(tangent_bundle_core I' M').cont_mdiff_within_at_iff],
  sorry -- refine ⟨_, _⟩,
end

end smooth_manifold_with_corners
