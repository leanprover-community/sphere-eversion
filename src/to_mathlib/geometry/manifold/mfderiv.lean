import geometry.manifold.diffeomorph
import geometry.manifold.algebra.monoid
import geometry.manifold.metrizable
import to_mathlib.analysis.calculus

open bundle set function filter
open_locale manifold topology
noncomputable theory

namespace vector_bundle_core

variables {𝕜 B F : Type*} [nontrivially_normed_field 𝕜]
  [normed_add_comm_group F] [normed_space 𝕜 F] [topological_space B]
  {ι : Type*} (Z : vector_bundle_core 𝕜 B F ι) {i j : ι}

@[simp, mfld_simps] lemma local_triv_continuous_linear_map_at {b : B} (hb : b ∈ Z.base_set i) :
  (Z.local_triv i).continuous_linear_map_at 𝕜 b = Z.coord_change (Z.index_at b) i b :=
begin
  ext1 v,
  rw [(Z.local_triv i).continuous_linear_map_at_apply 𝕜, (Z.local_triv i).coe_linear_map_at_of_mem],
  exacts [rfl, hb]
end

@[simp, mfld_simps] lemma trivialization_at_continuous_linear_map_at {b₀ b : B}
  (hb : b ∈ (trivialization_at F Z.fiber b₀).base_set) :
  (trivialization_at F Z.fiber b₀).continuous_linear_map_at 𝕜 b =
  Z.coord_change (Z.index_at b) (Z.index_at b₀) b :=
Z.local_triv_continuous_linear_map_at hb

@[simp, mfld_simps] lemma local_triv_symmL {b : B} (hb : b ∈ Z.base_set i) :
  (Z.local_triv i).symmL 𝕜 b = Z.coord_change i (Z.index_at b) b :=
by { ext1 v, rw [(Z.local_triv i).symmL_apply 𝕜, (Z.local_triv i).symm_apply], exacts [rfl, hb] }

@[simp, mfld_simps] lemma trivialization_at_symmL {b₀ b : B}
  (hb : b ∈ (trivialization_at F Z.fiber b₀).base_set) :
  (trivialization_at F Z.fiber b₀).symmL 𝕜 b = Z.coord_change (Z.index_at b₀) (Z.index_at b) b :=
Z.local_triv_symmL hb

@[simp, mfld_simps] lemma trivialization_at_coord_change_eq {b₀ b₁ b : B}
  (hb : b ∈ (trivialization_at F Z.fiber b₀).base_set ∩ (trivialization_at F Z.fiber b₁).base_set)
  (v : F) :
  (trivialization_at F Z.fiber b₀).coord_changeL 𝕜 (trivialization_at F Z.fiber b₁) b v =
  Z.coord_change (Z.index_at b₀) (Z.index_at b₁) b v :=
Z.local_triv_coord_change_eq _ _ hb v

end vector_bundle_core

section
open smooth_manifold_with_corners

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
-- declare a smooth manifold `M` over the pair `(E, H)`.
{E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
{H : Type*} [topological_space H] (I : model_with_corners 𝕜 E H)
{M : Type*} [topological_space M] [charted_space H M] [Is : smooth_manifold_with_corners I M]
-- declare a smooth manifold `M'` over the pair `(E', H')`.
{E' : Type*} [normed_add_comm_group E'] [normed_space 𝕜 E']
{H' : Type*} [topological_space H'] (I' : model_with_corners 𝕜 E' H')
{M' : Type*} [topological_space M'] [charted_space H' M'] [I's : smooth_manifold_with_corners I' M']
-- declare a manifold `M''` over the pair `(E'', H'')`.
{E'' : Type*} [normed_add_comm_group E''] [normed_space 𝕜 E'']
{H'' : Type*} [topological_space H''] {I'' : model_with_corners 𝕜 E'' H''}
{M'' : Type*} [topological_space M''] [charted_space H'' M'']
-- declare a smooth manifold `N` over the pair `(F, G)`.
{F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]
{G : Type*} [topological_space G] {J : model_with_corners 𝕜 F G}
{N : Type*} [topological_space N] [charted_space G N] [Js : smooth_manifold_with_corners J N]
-- declare a smooth manifold `N'` over the pair `(F', G')`.
{F' : Type*} [normed_add_comm_group F'] [normed_space 𝕜 F']
{G' : Type*} [topological_space G'] {J' : model_with_corners 𝕜 F' G'}
{N' : Type*} [topological_space N'] [charted_space G' N'] [J's : smooth_manifold_with_corners J' N']
-- F₁, F₂, F₃, F₄ are normed spaces
{F₁ : Type*} [normed_add_comm_group F₁] [normed_space 𝕜 F₁]
{F₂ : Type*} [normed_add_comm_group F₂] [normed_space 𝕜 F₂]
{F₃ : Type*} [normed_add_comm_group F₃] [normed_space 𝕜 F₃]
{F₄ : Type*} [normed_add_comm_group F₄] [normed_space 𝕜 F₄]
-- declare functions, sets, points and smoothness indices
{e : local_homeomorph M H} {e' : local_homeomorph M' H'}
{f f₁ : M → M'} {s s₁ t : set M} {x : M} {m n : ℕ∞}

end

section

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
{E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
{H : Type*} [topological_space H] {I : model_with_corners 𝕜 E H}
{M : Type*} [topological_space M] [charted_space H M]
{F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]

variables [smooth_manifold_with_corners I M]

namespace tangent_bundle

@[simp, mfld_simps] lemma trivialization_at_continuous_linear_map_at {b₀ b : M}
  (hb : b ∈ (trivialization_at E (tangent_space I) b₀).base_set) :
  (trivialization_at E (tangent_space I) b₀).continuous_linear_map_at 𝕜 b =
  (tangent_bundle_core I M).coord_change (achart H b) (achart H b₀) b :=
(tangent_bundle_core I M).local_triv_continuous_linear_map_at hb

@[simp, mfld_simps] lemma trivialization_at_symmL {b₀ b : M}
  (hb : b ∈ (trivialization_at E (tangent_space I) b₀).base_set) :
  (trivialization_at E (tangent_space I) b₀).symmL 𝕜 b =
    (tangent_bundle_core I M).coord_change (achart H b₀) (achart H b) b :=
(tangent_bundle_core I M).local_triv_symmL hb

lemma coord_change_model_space (b b' x : F) :
  (tangent_bundle_core 𝓘(𝕜, F) F).coord_change (achart F b) (achart F b') x = 1 :=
by simpa only [tangent_bundle_core_coord_change] with mfld_simps using
    fderiv_within_id unique_diff_within_at_univ

lemma symmL_model_space (b b' : F) :
  (trivialization_at F (tangent_space 𝓘(𝕜, F)) b).symmL 𝕜 b' = (1 : F →L[𝕜] F) :=
begin
  rw [tangent_bundle.trivialization_at_symmL, coord_change_model_space],
  apply mem_univ
end

lemma continuous_linear_map_at_model_space (b b' : F) :
  (trivialization_at F (tangent_space 𝓘(𝕜, F)) b).continuous_linear_map_at 𝕜 b' =
  (1 : F →L[𝕜] F) :=
begin
  rw [tangent_bundle.trivialization_at_continuous_linear_map_at, coord_change_model_space],
  apply mem_univ
end

end tangent_bundle

end


section smooth_manifold_with_corners
open smooth_manifold_with_corners

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
  {E' : Type*} [normed_add_comm_group E'] [normed_space 𝕜 E']
  {F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]
  {F' : Type*} [normed_add_comm_group F'] [normed_space 𝕜 F']
  {H : Type*} [topological_space H] {I : model_with_corners 𝕜 E H}
  {H' : Type*} [topological_space H'] {I' : model_with_corners 𝕜 E' H'}
  {G : Type*} [topological_space G] {J : model_with_corners 𝕜 F G}
  {G' : Type*} [topological_space G'] {J' : model_with_corners 𝕜 F' G'}
  {M : Type*} [topological_space M] [charted_space H M]
  {M' : Type*} [topological_space M'] [charted_space H' M']
  {N : Type*} [topological_space N] [charted_space G N]
  {N' : Type*} [topological_space N'] [charted_space G' N']
  {F'' : Type*} [normed_add_comm_group F''] [normed_space 𝕜 F'']
  {E'' : Type*} [normed_add_comm_group E''] [normed_space 𝕜 E'']
  {H'' : Type*} [topological_space H''] {I'' : model_with_corners 𝕜 E'' H''}
  {M'' : Type*} [topological_space M''] [charted_space H'' M'']
  {e : local_homeomorph M H}
variables {f : M → M'} {m n : ℕ∞} {s : set M} {x x' : M}

-- this can be useful to see where we (ab)use definitional equalities
-- local attribute [irreducible] tangent_space

/-! The two instances below deserve some further thought. For example one might not want the tangent
space at every point to carry a canonical norm.

Note that `dual_pair.update` requires `F` to be a `normed_add_comm_group` (though perhaps we could
get away with `has_continuous_smul` with sufficient extra work).

In `rel_mfld.slice` we use `dual_pair.update` applied to `tangent_space`. If we don't add these
instances, then in fact Lean still accepts the definition. What is going on is that Lean
is unfolding the definition of `tangent_space`, realizing that `tangent_space I x = E` and
`tangent_space I' y = E'` and using the `normed_add_comm_group` instances of these types.
Note that this still uses these instances but at the cost that up to reducible transparency, the
term is not type-correct (in other words: you have to unfold `tangent_space` to realize that the
term is type-correct).

This means that many tactics, like `simp`, `rw`, and `dsimp` fail to rewrite within this term,
because the result is not type correct up to reducible transparancy.

Declaring these instances avoids such problems. -/

section

variables [smooth_manifold_with_corners I M]
instance {x : M} : normed_add_comm_group (tangent_space I x) := by delta_instance tangent_space
instance {x : M} : normed_space 𝕜 (tangent_space I x) := by delta_instance tangent_space
end

variables (I)

lemma tangent_bundle_core_coord_change_model_space (x x' z : H) :
  (tangent_bundle_core I H).coord_change (achart H x) (achart H x') z =
  continuous_linear_map.id 𝕜 E :=
by { ext v, exact (tangent_bundle_core I H).coord_change_self (achart _ z) z (mem_univ _) v }

end smooth_manifold_with_corners

section smooth_manifold_with_corners
open smooth_manifold_with_corners

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
  {E' : Type*} [normed_add_comm_group E'] [normed_space 𝕜 E']
  {F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]
  {F' : Type*} [normed_add_comm_group F'] [normed_space 𝕜 F']
  {H : Type*} [topological_space H] {I : model_with_corners 𝕜 E H}
  {H' : Type*} [topological_space H'] {I' : model_with_corners 𝕜 E' H'}
  {G : Type*} [topological_space G] {J : model_with_corners 𝕜 F G}
  {G' : Type*} [topological_space G'] {J' : model_with_corners 𝕜 F' G'}
  {M : Type*} [topological_space M] [charted_space H M]
  {M' : Type*} [topological_space M'] [charted_space H' M']
  {N : Type*} [topological_space N] [charted_space G N]
  {N' : Type*} [topological_space N'] [charted_space G' N']
  {F'' : Type*} [normed_add_comm_group F''] [normed_space 𝕜 F'']
variables {f : M → M'} {m n : ℕ∞} {s : set M} {x x' : M}
-- declare some additional normed spaces, used for fibers of vector bundles
{F₁ : Type*} [normed_add_comm_group F₁] [normed_space 𝕜 F₁]
{F₂ : Type*} [normed_add_comm_group F₂] [normed_space 𝕜 F₂]

variables [smooth_manifold_with_corners I M] [smooth_manifold_with_corners I' M']
  [smooth_manifold_with_corners J N]

open bundle
variables
  {Z : M → Type*} [topological_space (total_space Z)] [∀ b, topological_space (Z b)]
  [∀ b, add_comm_monoid (Z b)] [∀ b, module 𝕜 (Z b)]
  [fiber_bundle F₁ Z] [vector_bundle 𝕜 F₁ Z] [smooth_vector_bundle F₁ Z I]
  {Z₂ : M' → Type*} [topological_space (total_space Z₂)] [∀ b, topological_space (Z₂ b)]
  [∀ b, add_comm_monoid (Z₂ b)] [∀ b, module 𝕜 (Z₂ b)]
  [fiber_bundle F₂ Z₂] [vector_bundle 𝕜 F₂ Z₂] [smooth_vector_bundle F₂ Z₂ I']

open_locale bundle

variables (I I' Z Z₂ F₁ F₂)

/-- When `ϕ` is a continuous linear map that changes vectors in charts around `x` to vectors
  in charts around `y`, `in_coordinates Z Z₂ x₀ x y₀ y ϕ` is a coordinate change of this continuous
  linear map that makes sense from charts around `x₀` to charts around `y₀`
  by composing it with appropriate coordinate changes given by smooth vector bundles `Z` and `Z₂`.
-/
def in_coordinates (x₀ x : M) (y₀ y : M') (ϕ : Z x →L[𝕜] Z₂ y) : F₁ →L[𝕜] F₂ :=
(trivialization_at F₂ Z₂ y₀).continuous_linear_map_at 𝕜 y ∘L ϕ ∘L
(trivialization_at F₁ Z x₀).symmL 𝕜 x

/-- When `ϕ x` is a continuous linear map that changes vectors in charts around `f x` to vectors
  in charts around `g x`, `in_tangent_coordinates I I' f g ϕ x₀ x` is a coordinate change of
  this continuous linear map that makes sense from charts around `f x₀` to charts around `g x₀`
  by composing it with appropriate coordinate changes.
  Note that in the type of `ϕ` is more accurately
  `Π x : N, tangent_space I (f x) →L[𝕜] tangent_space I' (g x)`.
  We are unfolding `tangent_space` in this type so that Lean recognizes that the type of `ϕ` doesn't
  actually depend on `f` or `g`. -/
def in_tangent_coordinates {N} (f : N → M) (g : N → M') (ϕ : N → E →L[𝕜] E') : N → N → E →L[𝕜] E' :=
λ x₀ x, in_coordinates E E' (tangent_space I) (tangent_space I') (f x₀) (f x) (g x₀) (g x) (ϕ x)

variables {F₁ F₂}

/-- rewrite `in_coordinates` using continuous linear equivalences. -/
lemma in_coordinates_eq (x₀ x : M) (y₀ y : M') (ϕ : Z x →L[𝕜] Z₂ y)
  (hx : x ∈ (trivialization_at F₁ Z x₀).base_set)
  (hy : y ∈ (trivialization_at F₂ Z₂ y₀).base_set) :
  in_coordinates F₁ F₂ Z Z₂ x₀ x y₀ y ϕ =
  ((trivialization_at F₂ Z₂ y₀).continuous_linear_equiv_at 𝕜 y hy : Z₂ y →L[𝕜] F₂) ∘L ϕ ∘L
  (((trivialization_at F₁ Z x₀).continuous_linear_equiv_at 𝕜 x hx).symm : F₁ →L[𝕜] Z x) :=
begin
  ext,
  simp_rw [in_coordinates, continuous_linear_map.coe_comp', continuous_linear_equiv.coe_coe,
    trivialization.coe_continuous_linear_equiv_at_eq,
    trivialization.symm_continuous_linear_equiv_at_eq]
end

protected lemma vector_bundle_core.in_coordinates_eq {ι₁ ι₂} (Z₁ : vector_bundle_core 𝕜 M F₁ ι₁)
  (Z₂ : vector_bundle_core 𝕜 M' F₂ ι₂)
  {x₀ x : M} {y₀ y : M'} (ϕ : F₁ →L[𝕜] F₂)
  (hx : x ∈ Z₁.base_set (Z₁.index_at x₀))
  (hy : y ∈ Z₂.base_set (Z₂.index_at y₀)) :
    in_coordinates F₁ F₂ Z₁.fiber Z₂.fiber x₀ x y₀ y ϕ =
    Z₂.coord_change (Z₂.index_at y) (Z₂.index_at y₀) y ∘L ϕ ∘L
    Z₁.coord_change (Z₁.index_at x₀) (Z₁.index_at x) x :=
by simp_rw [in_coordinates, Z₂.trivialization_at_continuous_linear_map_at hy,
  Z₁.trivialization_at_symmL hx]

/-- The map `in_coordinates` is trivial on the model spaces -/
lemma in_coordinates_tangent_bundle_core_model_space
  (x₀ x : H) (y₀ y : H') (ϕ : E →L[𝕜] E') :
    in_coordinates E E' (tangent_space I) (tangent_space I') x₀ x y₀ y ϕ = ϕ :=
begin
  refine (vector_bundle_core.in_coordinates_eq _ _ _ _ _).trans _,
  { exact mem_univ x },
  { exact mem_univ y },
  simp_rw [tangent_bundle_core_index_at, tangent_bundle_core_coord_change_model_space,
    continuous_linear_map.id_comp, continuous_linear_map.comp_id]
end

lemma in_tangent_coordinates_model_space (f : N → H) (g : N → H') (ϕ : N → E →L[𝕜] E') (x₀ : N) :
    in_tangent_coordinates I I' f g ϕ x₀ = ϕ :=
by simp_rw [in_tangent_coordinates, in_coordinates_tangent_bundle_core_model_space]

lemma in_tangent_coordinates_eq (f : N → M) (g : N → M') (ϕ : N → E →L[𝕜] E') {x₀ x : N}
  (hx : f x ∈ (chart_at H (f x₀)).source) (hy : g x ∈ (chart_at H' (g x₀)).source) :
  in_tangent_coordinates I I' f g ϕ x₀ x =
  (tangent_bundle_core I' M').coord_change (achart H' (g x)) (achart H' (g x₀)) (g x) ∘L ϕ x ∘L
  (tangent_bundle_core I M).coord_change (achart H (f x₀)) (achart H (f x)) (f x) :=
(tangent_bundle_core I M).in_coordinates_eq (tangent_bundle_core I' M') (ϕ x) hx hy

variables {I I'}

/-- The function that sends `x` to the `y`-derivative of `f(x,y)` at `g(x)` is `C^n` at `x₀`,
where the derivative is taken as a continuous linear map.
We have to assume that `f` is `C^(n+1)` at `(x₀, g(x₀))` and `g` is `C^n` at `x₀`.
We have to insert a coordinate change from `x₀` to `x` to make the derivative sensible.
`cont_mdiff_at.mfderiv_id` and `cont_mdiff_at.mfderiv_const` are special cases of this.

This lemma should be generalized to a `cont_mdiff_within_at` for `mfderiv_within`. If we do that, we
can deduce `cont_mdiff_on.cont_mdiff_on_tangent_map_within` from this.
-/
lemma cont_mdiff_at.mfderiv {x₀ : N} (f : N → M → M') (g : N → M)
  (hf : cont_mdiff_at (J.prod I) I' n (function.uncurry f) (x₀, g x₀))
  (hg : cont_mdiff_at J I m g x₀) (hmn : m + 1 ≤ n) :
  cont_mdiff_at J 𝓘(𝕜, E →L[𝕜] E') m
    (in_tangent_coordinates I I' g (λ x, f x (g x)) (λ x, mfderiv I I' (f x) (g x)) x₀) x₀ :=
begin
  have h4f : continuous_at (λ x, f x (g x)) x₀,
  { apply continuous_at.comp (by apply hf.continuous_at) (continuous_at_id.prod hg.continuous_at) },
  have h4f := h4f.preimage_mem_nhds (ext_chart_at_source_mem_nhds I' (f x₀ (g x₀))),
  have h3f := cont_mdiff_at_iff_cont_mdiff_at_nhds.mp (hf.of_le $ (self_le_add_left 1 m).trans hmn),
  have h2f : ∀ᶠ x₂ in 𝓝 x₀, cont_mdiff_at I I' 1 (f x₂) (g x₂),
  { refine ((continuous_at_id.prod hg.continuous_at).tendsto.eventually h3f).mono (λ x hx, _),
    exact hx.comp (g x) (cont_mdiff_at_const.prod_mk cont_mdiff_at_id) },
  have h2g := hg.continuous_at.preimage_mem_nhds (ext_chart_at_source_mem_nhds I (g x₀)),
  have : cont_diff_within_at 𝕜 m (λ x, fderiv_within 𝕜
    (ext_chart_at I' (f x₀ (g x₀)) ∘ f ((ext_chart_at J x₀).symm x) ∘ (ext_chart_at I (g x₀)).symm)
    (range I) (ext_chart_at I (g x₀) (g ((ext_chart_at J x₀).symm x))))
    (range J) (ext_chart_at J x₀ x₀),
  { rw [cont_mdiff_at_iff] at hf hg,
    simp_rw [function.comp, uncurry, ext_chart_at_prod, local_equiv.prod_coe_symm] at hf ⊢,
    refine (cont_diff_within_at_fderiv_within _
      (hg.2.mono_of_mem _) I.unique_diff hmn _ _ _ _).mono_of_mem _,
    swap 3,
    { simp_rw [function.comp, ext_chart_at_to_inv], exact hf.2 },
    { refine (ext_chart_at J x₀).target ∩
      (λ x, (ext_chart_at J x₀).symm x) ⁻¹' (g ⁻¹' (ext_chart_at I (g x₀)).source) },
    { exact mem_of_superset self_mem_nhds_within
        ((inter_subset_left _ _).trans $ ext_chart_at_target_subset_range J x₀) },
    { simp_rw [mem_inter_iff, mem_preimage, ext_chart_at_to_inv],
      exact ⟨local_equiv.maps_to _ (mem_ext_chart_source J x₀), mem_ext_chart_source I (g x₀)⟩ },
    { simp_rw [model_with_corners.range_prod],
      exact set.prod_mono ((inter_subset_left _ _).trans $ ext_chart_at_target_subset_range J x₀)
        subset_rfl },
    { refine eventually_of_forall (λ x, mem_range_self _) },
    swap 2,
    { refine inter_mem (ext_chart_at_target_mem_nhds_within J x₀) _,
      refine nhds_within_le_nhds (ext_chart_at_preimage_mem_nhds' _ _ (mem_ext_chart_source J x₀) _),
      exact hg.1.preimage_mem_nhds (ext_chart_at_source_mem_nhds I (g x₀)) },
    simp_rw [function.comp, ext_chart_at_to_inv],
    refine mem_of_superset self_mem_nhds_within _,
    refine (image_subset_range _ _).trans _,
    exact range_comp_subset_range (λ a, chart_at H (g x₀) $ g $ (chart_at G x₀).symm $ J.symm a) I },
  have : cont_mdiff_at J 𝓘(𝕜, E →L[𝕜] E') m
    (λ x, fderiv_within 𝕜 (ext_chart_at I' (f x₀ (g x₀)) ∘ f x ∘ (ext_chart_at I (g x₀)).symm)
    (range I) (ext_chart_at I (g x₀) (g x))) x₀,
  { simp_rw [cont_mdiff_at_iff_source_of_mem_source (mem_chart_source G x₀),
      cont_mdiff_within_at_iff_cont_diff_within_at, function.comp],
    exact this },
  have : cont_mdiff_at J 𝓘(𝕜, E →L[𝕜] E') m
    (λ x, fderiv_within 𝕜 (ext_chart_at I' (f x₀ (g x₀)) ∘ (ext_chart_at I' (f x (g x))).symm ∘
      written_in_ext_chart_at I I' (g x) (f x) ∘ ext_chart_at I (g x) ∘
      (ext_chart_at I (g x₀)).symm) (range I) (ext_chart_at I (g x₀) (g x))) x₀,
  { refine this.congr_of_eventually_eq _,
    filter_upwards [h2g, h2f],
    intros x₂ hx₂ h2x₂,
    have : ∀ x ∈ (ext_chart_at I (g x₀)).symm ⁻¹' (ext_chart_at I (g x₂)).source ∩
        (ext_chart_at I (g x₀)).symm ⁻¹' (f x₂ ⁻¹' (ext_chart_at I' (f x₂ (g x₂))).source),
      (ext_chart_at I' (f x₀ (g x₀)) ∘ (ext_chart_at I' (f x₂ (g x₂))).symm ∘
      written_in_ext_chart_at I I' (g x₂) (f x₂) ∘ ext_chart_at I (g x₂) ∘
      (ext_chart_at I (g x₀)).symm) x =
      ext_chart_at I' (f x₀ (g x₀)) (f x₂ ((ext_chart_at I (g x₀)).symm x)),
    { rintro x ⟨hx, h2x⟩,
      simp_rw [written_in_ext_chart_at, function.comp_apply],
      rw [(ext_chart_at I (g x₂)).left_inv hx, (ext_chart_at I' (f x₂ (g x₂))).left_inv h2x] },
    refine filter.eventually_eq.fderiv_within_eq_nhds (I.unique_diff _ $ mem_range_self _) _,
    refine eventually_of_mem (inter_mem _ _) this,
    { exact ext_chart_at_preimage_mem_nhds' _ _ hx₂ (ext_chart_at_source_mem_nhds I (g x₂)) },
    refine ext_chart_at_preimage_mem_nhds' _ _ hx₂ _,
    exact (h2x₂.continuous_at).preimage_mem_nhds (ext_chart_at_source_mem_nhds _ _) },
  /- The conclusion is equal to the following, when unfolding coord_change of
    `tangent_bundle_core` -/
  have : cont_mdiff_at J 𝓘(𝕜, E →L[𝕜] E') m
    (λ x, (fderiv_within 𝕜 (ext_chart_at I' (f x₀ (g x₀)) ∘ (ext_chart_at I' (f x (g x))).symm)
        (range I') (ext_chart_at I' (f x (g x)) (f x (g x)))).comp
        ((mfderiv I I' (f x) (g x)).comp (fderiv_within 𝕜 (ext_chart_at I (g x) ∘
        (ext_chart_at I (g x₀)).symm) (range I) (ext_chart_at I (g x₀) (g x))))) x₀,
  { refine this.congr_of_eventually_eq _,
    filter_upwards [h2g, h2f, h4f],
    intros x₂ hx₂ h2x₂ h3x₂,
    symmetry,
    rw [(h2x₂.mdifferentiable_at le_rfl).mfderiv],
    have hI := (cont_diff_within_at_ext_coord_change I (g x₂) (g x₀) $
      local_equiv.mem_symm_trans_source _ hx₂ $ mem_ext_chart_source I (g x₂))
      .differentiable_within_at le_top,
    have hI' := (cont_diff_within_at_ext_coord_change I' (f x₀ (g x₀)) (f x₂ (g x₂)) $
      local_equiv.mem_symm_trans_source _
      (mem_ext_chart_source I' (f x₂ (g x₂))) h3x₂).differentiable_within_at le_top,
    have h3f := (h2x₂.mdifferentiable_at le_rfl).2,
    refine fderiv_within.comp₃ _ hI' h3f hI _ _ _ _ (I.unique_diff _ $ mem_range_self _),
    { exact λ x _, mem_range_self _ },
    { exact λ x _, mem_range_self _ },
    { simp_rw [written_in_ext_chart_at, function.comp_apply,
        (ext_chart_at I (g x₂)).left_inv (mem_ext_chart_source I (g x₂))] },
    { simp_rw [function.comp_apply, (ext_chart_at I (g x₀)).left_inv hx₂] } },
  refine this.congr_of_eventually_eq _,
  filter_upwards [h2g, h4f] with x hx h2x,
  rw [in_tangent_coordinates_eq],
  { refl },
  { rwa [ext_chart_at_source] at hx },
  { rwa [ext_chart_at_source] at h2x },
end

/-- The function `x ↦ D_yf(x,y)` is `C^n` at `x₀`, where the derivative is taken as a continuous
linear map. We have to assume that `f` is `C^(n+1)` at `(x₀, x₀)`.
We have to insert a coordinate change from `x₀` to `x` to make the derivative sensible.
This is a special case of `cont_mdiff_at.mfderiv` (with `g = id`),
and `cont_mdiff_at.mfderiv_const` is a special case of this.
-/
lemma cont_mdiff_at.mfderiv_id {x₀ : M} (f : M → M → M')
  (hf : cont_mdiff_at (I.prod I) I' n (function.uncurry f) (x₀, x₀)) (hmn : m + 1 ≤ n) :
  cont_mdiff_at I 𝓘(𝕜, E →L[𝕜] E') m
    (in_tangent_coordinates I I' id (λ x, f x x) (λ x, mfderiv I I' (f x) x) x₀) x₀ :=
hf.mfderiv f id cont_mdiff_at_id hmn

/-- The derivative `D_yf(y)` is `C^n` at `x₀`, where the derivative is taken as a continuous
linear map. We have to assume that `f` is `C^(n+1)` at `x₀`.
We have to insert a coordinate change from `x₀` to `x` to make the derivative sensible.
This is a special case of See `cont_mdiff_at.mfderiv_id` where `f` does not contain any parameters.
-/
lemma cont_mdiff_at.mfderiv_const {x₀ : M} {f : M → M'}
  (hf : cont_mdiff_at I I' n f x₀) (hmn : m + 1 ≤ n) :
  cont_mdiff_at I 𝓘(𝕜, E →L[𝕜] E') m (in_tangent_coordinates I I' id f (mfderiv I I' f) x₀) x₀ :=
begin
  have : cont_mdiff_at (I.prod I) I' n (λ x : M × M, f x.2) (x₀, x₀) :=
  cont_mdiff_at.comp (x₀, x₀) hf cont_mdiff_at_snd,
  apply cont_mdiff_at.mfderiv_id (λ x, f) this hmn
end

end smooth_manifold_with_corners
