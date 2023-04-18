import geometry.manifold.diffeomorph
import geometry.manifold.algebra.monoid
import geometry.manifold.metrizable
import to_mathlib.analysis.calculus

open bundle set function filter
open_locale manifold topology
noncomputable theory

section topology

variables {α β γ : Type*} [topological_space α] [topological_space β]

lemma map_fst_nhds_within_eq {x : α × β} {s : set α} :
  map prod.fst (𝓝[prod.fst ⁻¹' s] x) = 𝓝[s] x.1 :=
by { cases x, rw [← prod_univ, nhds_within_prod_eq, nhds_within_univ, map_fst_prod] }

lemma nhds_within_preimage_fst_le {x : α × β} {s : set α} :
  𝓝[prod.fst ⁻¹' s] x ≤ comap prod.fst (𝓝[s] x.1) :=
by { rw [← map_fst_nhds_within_eq], exact le_comap_map }

lemma filter.eventually.nhds_within_preimage_fst {z : α × β} {s : set α} {p : α × β → Prop}
  (h : ∀ᶠ x in 𝓝[s] z.1, ∀ y, p (x, y)) : ∀ᶠ z' in 𝓝[prod.fst ⁻¹' s] z, p z' :=
begin
  refine eventually.filter_mono nhds_within_preimage_fst_le _,
  simp_rw [eventually_comap, prod.forall],
  simp only [forall_swap] {single_pass := tt},
  convert h, ext x,
  refine forall_congr (λ y, _),
  simp_rw [forall_eq],
end

lemma filter.eventually_eq.nhds_within_preimage_fst {z : α × β} {s : set α} {f g : α × β → γ}
  (h : curry f =ᶠ[𝓝[s] z.1] curry g) : f =ᶠ[𝓝[prod.fst ⁻¹' s] z] g :=
filter.eventually.nhds_within_preimage_fst $ by { simp_rw [← funext_iff], exact h }

lemma eventually_mem_nhds_within' {α} [topological_space α] {s t : set α} {a : α} :
  (∀ᶠ x in 𝓝[s] a, t ∈ 𝓝[s] x) ↔ t ∈ 𝓝[s] a :=
eventually_nhds_within_nhds_within

lemma eventually_mem_nhds_within'' {α} [topological_space α] {s t : set α} {a : α} :
  (∀ᶠ x in 𝓝 a, t ∈ 𝓝[s] x) ↔ t ∈ 𝓝[s] a :=
eventually_nhds_nhds_within

end topology

section charted_space

variables {M H : Type*} [topological_space M] [topological_space H] [charted_space H M]
  (G : structure_groupoid H)

end charted_space

namespace model_with_corners

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
  {H : Type*} [topological_space H]
  {M : Type*} [topological_space M] (f : local_homeomorph M H) (I : model_with_corners 𝕜 E H)

end model_with_corners


-- todo: make `vector_bundle_core.total_space` protected!
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

lemma ext_chart_at_def (x : M) : ext_chart_at I x = (chart_at H x).extend I := rfl

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

section

variables {𝕜 B B' F M : Type*} {E : B → Type*} [nontrivially_normed_field 𝕜]
  [normed_add_comm_group F] [normed_space 𝕜 F]
  [topological_space (total_space E)] [∀ x, topological_space (E x)]

  {EB : Type*} [normed_add_comm_group EB] [normed_space 𝕜 EB]
  {HB : Type*} [topological_space HB] (IB : model_with_corners 𝕜 EB HB)
  (E' : B → Type*) [Π x, has_zero (E' x)]
  {EM : Type*} [normed_add_comm_group EM] [normed_space 𝕜 EM]
  {HM : Type*} [topological_space HM] {IM : model_with_corners 𝕜 EM HM}
  [topological_space M] [charted_space HM M]
  {n : ℕ∞}

variables [topological_space B] [charted_space HB B] [fiber_bundle F E]
variables {F E IB} [smooth_manifold_with_corners IB B]


-- temporary duplicate
-- instance {x : M} [smooth_manifold_with_corners IM M] : normed_add_comm_group (tangent_space IM x) :=
-- by delta_instance tangent_space
-- instance {x : M} [smooth_manifold_with_corners IM M] : normed_space 𝕜 (tangent_space IM x) :=
-- by delta_instance tangent_space


-- /-- Characterization of C^n functions into a smooth vector bundle. -/
-- lemma tangent_bundle.cont_mdiff_at_total_space (f : M → tangent_bundle IB B) (x₀ : M) :
--   cont_mdiff_at IM IB.tangent n f x₀ ↔
--   cont_mdiff_at IM IB n (λ x, (f x).proj) x₀ ∧
--   cont_mdiff_at IM 𝓘(𝕜, tangent_space IB (f x₀).proj) n (λ x, (trivialization_at EB (tangent_space IB) (f x₀).proj (f x)).2) x₀ :=
-- cont_mdiff_at_total_space f x₀

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
-- lemma tangent_bundle_core_coord_change_achart (x x' : M) (z : H) :
--   (tangent_bundle_core I M).coord_change (achart H x) (achart H x') z =
--   fderiv_within 𝕜 (ext_chart_at I x' ∘ (ext_chart_at I x).symm) (range I) (I z) :=
-- rfl

lemma cont_mdiff_prod {f : M → M' × N'} :
  cont_mdiff I (I'.prod J') n f ↔
  cont_mdiff I I' n (λ x, (f x).1) ∧ cont_mdiff I J' n (λ x, (f x).2) :=
⟨λ h, ⟨h.fst, h.snd⟩, λ h, by { convert h.1.prod_mk h.2, ext x; refl }⟩

lemma cont_mdiff_at_prod {f : M → M' × N'} {x : M} :
  cont_mdiff_at I (I'.prod J') n f x ↔
  cont_mdiff_at I I' n (λ x, (f x).1) x ∧ cont_mdiff_at I J' n (λ x, (f x).2) x :=
⟨λ h, ⟨h.fst, h.snd⟩, λ h, by { convert h.1.prod_mk h.2, ext x; refl }⟩

lemma smooth_prod {f : M → M' × N'} :
  smooth I (I'.prod J') f ↔
  smooth I I' (λ x, (f x).1) ∧ smooth I J' (λ x, (f x).2) :=
cont_mdiff_prod

lemma smooth_at_prod {f : M → M' × N'} {x : M} :
  smooth_at I (I'.prod J') f x ↔
  smooth_at I I' (λ x, (f x).1) x ∧ smooth_at I J' (λ x, (f x).2) x :=
cont_mdiff_at_prod

lemma cont_mdiff_within_at.congr_of_eventually_eq_insert {f f' : M → M'}
  (hf : cont_mdiff_within_at I I' n f s x)
  (h : f' =ᶠ[𝓝[insert x s] x] f) : cont_mdiff_within_at I I' n f' s x :=
hf.congr_of_eventually_eq (h.filter_mono $ nhds_within_mono x $ subset_insert x s) $
  h.self_of_nhds_within (mem_insert x s)

lemma cont_mdiff_at.comp_of_eq {g : M' → M''} {x : M} {y : M'}
  (hg : cont_mdiff_at I' I'' n g y) (hf : cont_mdiff_at I I' n f x) (hx : f x = y) :
  cont_mdiff_at I I'' n (g ∘ f) x :=
by { subst hx, exact hg.comp x hf }

lemma cont_mdiff_within_at.comp_of_eq {t : set M'} {g : M' → M''} {x : M} {y : M'}
  (hg : cont_mdiff_within_at I' I'' n g t y) (hf : cont_mdiff_within_at I I' n f s x)
  (st : maps_to f s t) (hx : f x = y) :
  cont_mdiff_within_at I I'' n (g ∘ f) s x :=
by { subst hx, exact hg.comp x hf st }

variables (I)
lemma cont_mdiff_on_model_symm : cont_mdiff_on 𝓘(𝕜, E) I n I.symm (range I) :=
begin
  rw [cont_mdiff_on_iff],
  refine ⟨I.continuous_on_symm, λ x y, _⟩,
  simp only with mfld_simps,
  exact cont_diff_on_id.congr (λ x', I.right_inv)
end
variables {I}


section
variables [smooth_manifold_with_corners I M]

lemma cont_mdiff_on_extend_symm (he : e ∈ maximal_atlas I M) :
  cont_mdiff_on 𝓘(𝕜, E) I n (e.extend I).symm (I '' e.target) :=
begin
  have h1 := cont_mdiff_on_model_symm I,
  have h2 := cont_mdiff_on_symm_of_mem_maximal_atlas he,
  refine h2.comp (h1.mono $ image_subset_range _ _) _,
  simp_rw [image_subset_iff, local_equiv.restr_coe_symm, I.to_local_equiv_coe_symm,
    preimage_preimage, I.left_inv, preimage_id']
end

variables (I)
lemma cont_mdiff_on_ext_chart_at_symm (x : M) :
  cont_mdiff_on 𝓘(𝕜, E) I n (ext_chart_at I x).symm (ext_chart_at I x).target :=
begin
  convert cont_mdiff_on_extend_symm (chart_mem_maximal_atlas I x),
  rw [ext_chart_at_target, I.image_eq]
end

end

variables (I)

lemma model_with_corners.fderiv_within_comp_symm (x : H) :
  fderiv_within 𝕜 (I ∘ I.symm) (range I) (I x) = continuous_linear_map.id 𝕜 E :=
begin
  have : fderiv_within 𝕜 (I ∘ I.symm) (range I) (I x) = fderiv_within 𝕜 id (range I) (I x),
  { refine fderiv_within_congr I.unique_diff_at_image (λ y hy, _) (by simp only with mfld_simps),
    exact model_with_corners.right_inv _ hy },
  rwa fderiv_within_id I.unique_diff_at_image at this
end

lemma tangent_bundle_core_coord_change_model_space (x x' : H) (z : H) :
  (tangent_bundle_core I H).coord_change (achart H x) (achart H x') z =
  continuous_linear_map.id 𝕜 E :=
begin
  simp only [tangent_bundle_core_coord_change_achart, ext_chart_at, I.fderiv_within_comp_symm] with mfld_simps,
end

variables [smooth_manifold_with_corners I M] [smooth_manifold_with_corners I' M']
  [smooth_manifold_with_corners J N]

lemma cont_diff_on_coord_change' {e e' : local_homeomorph M H}
  (h : e ∈ atlas H M) (h' : e' ∈ atlas H M) :
  cont_diff_on 𝕜 ⊤ (I ∘ (e.symm ≫ₕ e') ∘ I.symm) (I.symm ⁻¹' (e.symm ≫ₕ e').source ∩ range I) :=
(has_groupoid.compatible (cont_diff_groupoid ⊤ I) h h').1

end smooth_manifold_with_corners

section vector_bundle

open smooth_manifold_with_corners vector_bundle_core
open_locale bundle

variables {𝕜 B F M : Type*} {E : B → Type*}
  [nontrivially_normed_field 𝕜]
  [∀ x, add_comm_monoid (E x)] [∀ x, module 𝕜 (E x)]
  [normed_add_comm_group F] [normed_space 𝕜 F]
  [topological_space (total_space E)] [∀ x, topological_space (E x)]
  {EB : Type*} [normed_add_comm_group EB] [normed_space 𝕜 EB]
  {HB : Type*} [topological_space HB] {IB : model_with_corners 𝕜 EB HB}
  [topological_space B] [charted_space HB B]
  {EM : Type*} [normed_add_comm_group EM] [normed_space 𝕜 EM]
  {HM : Type*} [topological_space HM] {IM : model_with_corners 𝕜 EM HM}
  [topological_space M] [charted_space HM M]
  {n : ℕ∞}
  [fiber_bundle F E] [vector_bundle 𝕜 F E]
  {e e' : trivialization F (π E)}

theorem vector_bundle_core.smooth_at_coord_change {ι} (Z : vector_bundle_core 𝕜 B F ι)
  [Z.is_smooth IB] (i j : ι) {x₀ : B}
  (hx₀ : x₀ ∈ Z.base_set i ∩ Z.base_set j) :
  smooth_at IB 𝓘(𝕜, F →L[𝕜] F) (Z.coord_change i j) x₀ :=
(Z.smooth_on_coord_change IB i j).smooth_at $
  ((Z.is_open_base_set i).inter (Z.is_open_base_set j)).mem_nhds hx₀

variables (IB) [smooth_manifold_with_corners IB B] [smooth_vector_bundle F E IB]
lemma smooth_at_coord_change (e e' : trivialization F (π E)) {x₀ : B}
  (hx₀ : x₀ ∈ e.base_set ∩ e'.base_set)
  [mem_trivialization_atlas e] [mem_trivialization_atlas e']  :
  smooth_at IB 𝓘(𝕜, F →L[𝕜] F) (λ b : B, (e.coord_changeL 𝕜 e' b : F →L[𝕜] F)) x₀ :=
(smooth_on_coord_change e e').smooth_at $ (e.open_base_set.inter e'.open_base_set).mem_nhds hx₀

variables {IB}
lemma cont_mdiff_at_coord_change_apply (e e' : trivialization F (π E)) {x₀ : M}
  {f : M → B} {g : M → F} (hf : cont_mdiff_at IM IB n f x₀)
  (hg : cont_mdiff_at IM 𝓘(𝕜, F) n g x₀)
  (hx₀ : f x₀ ∈ e.base_set ∩ e'.base_set)
  [mem_trivialization_atlas e] [mem_trivialization_atlas e']  :
  cont_mdiff_at IM 𝓘(𝕜, F) n (λ x, e.coord_changeL 𝕜 e' (f x) (g x)) x₀ :=
(((smooth_at_coord_change IB e e' hx₀).of_le le_top).comp x₀ hf).clm_apply hg

variables (IB)
theorem trivialization.smooth_at (e : trivialization F (π E)) [mem_trivialization_atlas e]
  {x₀ : total_space E} (hx₀ : x₀.proj ∈ e.base_set) :
  smooth_at (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) e x₀ :=
begin
  rw [smooth_at_prod],
  refine ⟨(smooth_at_proj E).congr_of_eventually_eq _, _⟩,
  { exact eventually_of_mem (e.open_source.mem_nhds $ e.mem_source.mpr hx₀)
      (λ x hx, e.coe_fst hx) },
  simp_rw [smooth_at, cont_mdiff_at_iff_source_of_mem_source (mem_chart_source _ _)],
  simp only [fiber_bundle.ext_chart_at, function.comp, prod_univ, -ext_chart_at] with mfld_simps,
  let e' := trivialization_at F E x₀.proj,
  let c := (ext_chart_at IB x₀.proj).symm,
  have h0 := (ext_chart_at IB x₀.proj).left_inv (mem_ext_chart_source IB x₀.proj),
  have : cont_mdiff_within_at 𝓘(𝕜, EB × F) 𝓘(𝕜, F) ⊤
    (λ (x : EB × F), e'.coord_changeL 𝕜 e (c x.1) x.2)
    (prod.fst ⁻¹' range IB) (ext_chart_at IB x₀.proj x₀.proj, (e' x₀).2),
  { refine cont_mdiff_within_at.clm_apply _ cont_diff_within_at_snd.cont_mdiff_within_at,
    have h1 := smooth_at_coord_change IB e' e ⟨mem_base_set_trivialization_at F E x₀.proj, hx₀⟩,
    refine h1.cont_mdiff_within_at.comp_of_eq _ (maps_to_univ _ _) _,
    { refine ((cont_mdiff_on_ext_chart_at_symm IB x₀.proj _ $ (ext_chart_at IB x₀.proj).maps_to $
        mem_ext_chart_source IB x₀.proj).mono_of_mem _).comp_of_eq _ (maps_to_preimage _ _) rfl,
      { exact ext_chart_at_target_mem_nhds_within IB x₀.proj },
      exact cont_diff_within_at_fst.cont_mdiff_within_at },
    exact h0 },
  refine this.congr_of_eventually_eq_insert _,
  rw [insert_eq_of_mem],
  swap, exact mem_range_self _,
  refine filter.eventually.nhds_within_preimage_fst _,
  dsimp only,
  have h1 := (continuous_at_ext_chart_at_symm IB x₀.proj).preimage_mem_nhds
    ((trivialization_at F E _).open_base_set.mem_nhds $ mem_base_set_trivialization_at _ _ _),
  rw [h0] at h1,
  have h2 := (continuous_at_ext_chart_at_symm IB x₀.proj).preimage_mem_nhds
    (e.open_base_set.mem_nhds $ by rwa [h0]),
  filter_upwards [nhds_within_le_nhds h1, nhds_within_le_nhds h2] with b h1b h2b y,
  rw [e'.coord_changeL_apply e ⟨h1b, h2b⟩, e'.mk_symm h1b]
end

theorem trivialization.smooth_on (e : trivialization F (π E)) [mem_trivialization_atlas e] :
  smooth_on (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) e e.source :=
λ x hx, (e.smooth_at IB $ e.mem_source.mp hx).smooth_within_at

theorem smooth_at_trivialization_at
  {x₀ : B} {x : total_space E} (hx : x.proj ∈ (trivialization_at F E x₀).base_set) :
  smooth_at (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) (trivialization_at F E x₀) x :=
(trivialization_at F E x₀).smooth_at IB hx

theorem smooth_on_trivialization_at (x₀ : B) :
  smooth_on (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) (trivialization_at F E x₀)
  (trivialization_at F E x₀).source :=
(trivialization_at F E x₀).smooth_on IB

end vector_bundle


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

/-- A congruence lemma for `mfderiv`, (ab)using the fact that `tangent_space I' (f x)` is
definitionally equal to `E'`. -/
lemma mfderiv_congr_point {x' : M} (h : x = x') :
  @eq (E →L[𝕜] E') (mfderiv I I' f x) (mfderiv I I' f x') :=
by subst h

/-- A congruence lemma for `mfderiv`, (ab)using the fact that `tangent_space I' (f x)` is
definitionally equal to `E'`. -/
lemma mfderiv_congr {f' : M → M'} (h : f = f') :
  @eq (E →L[𝕜] E') (mfderiv I I' f x) (mfderiv I I' f' x) :=
by subst h

/-- The derivative of the projection `M × M' → M` is the projection `TM × TM' → TM` -/
lemma mfderiv_fst (x : M × M') :
  mfderiv (I.prod I') I prod.fst x = continuous_linear_map.fst 𝕜 E E' :=
begin
  simp_rw [mfderiv, if_pos smooth_at_fst.mdifferentiable_at, written_in_ext_chart_at,
    ext_chart_at_prod, function.comp, local_equiv.prod_coe, local_equiv.prod_coe_symm],
  have : unique_diff_within_at 𝕜 (range (I.prod I')) (ext_chart_at (I.prod I') x x) :=
  (I.prod I').unique_diff _ (mem_range_self _),
  refine (filter.eventually_eq.fderiv_within_eq this _ _).trans _,
  swap 3,
  { exact (ext_chart_at I x.1).right_inv ((ext_chart_at I x.1).maps_to $
      mem_ext_chart_source I x.1) },
  { refine eventually_of_mem (ext_chart_at_target_mem_nhds_within (I.prod I') x)
      (λ y hy, local_equiv.right_inv _ _),
    rw [ext_chart_at_prod] at hy,
    exact hy.1 },
  exact fderiv_within_fst this,
end

/-- The derivative of the projection `M × M' → M'` is the projection `TM × TM' → TM'` -/
lemma mfderiv_snd (x : M × M') :
  mfderiv (I.prod I') I' prod.snd x = continuous_linear_map.snd 𝕜 E E' :=
begin
  simp_rw [mfderiv, if_pos smooth_at_snd.mdifferentiable_at, written_in_ext_chart_at,
    ext_chart_at_prod, function.comp, local_equiv.prod_coe, local_equiv.prod_coe_symm],
  have : unique_diff_within_at 𝕜 (range (I.prod I')) (ext_chart_at (I.prod I') x x) :=
  (I.prod I').unique_diff _ (mem_range_self _),
  refine (filter.eventually_eq.fderiv_within_eq this _ _).trans _,
  swap 3,
  { exact (ext_chart_at I' x.2).right_inv ((ext_chart_at I' x.2).maps_to $
      mem_ext_chart_source I' x.2) },
  { refine eventually_of_mem (ext_chart_at_target_mem_nhds_within (I.prod I') x)
      (λ y hy, local_equiv.right_inv _ _),
    rw [ext_chart_at_prod] at hy,
    exact hy.2 },
  exact fderiv_within_snd this,
end

lemma mdifferentiable_at.prod_mk {f : N → M} {g : N → M'} {x : N}
  (hf : mdifferentiable_at J I f x)
  (hg : mdifferentiable_at J I' g x) :
  mdifferentiable_at J (I.prod I') (λ x, (f x, g x)) x :=
⟨hf.1.prod hg.1, hf.2.prod hg.2⟩


-- todo: rename differentiable_at.fderiv_within_prod -> differentiable_within_at.fderiv_within_prod
lemma mdifferentiable_at.mfderiv_prod {f : N → M} {g : N → M'} {x : N}
  (hf : mdifferentiable_at J I f x)
  (hg : mdifferentiable_at J I' g x) :
  mfderiv J (I.prod I') (λ x, (f x, g x)) x = (mfderiv J I f x).prod (mfderiv J I' g x) :=
begin
  classical,
  simp_rw [mfderiv, if_pos (hf.prod_mk hg), if_pos hf, if_pos hg],
  exact differentiable_at.fderiv_within_prod hf.2 hg.2 (J.unique_diff _ (mem_range_self _))
end

lemma mfderiv_prod_left {x₀ : M} {y₀ : M'} :
  mfderiv I (I.prod I') (λ x, (x, y₀)) x₀ = continuous_linear_map.inl 𝕜 E E' :=
begin
  refine ((mdifferentiable_at_id I).mfderiv_prod (mdifferentiable_at_const I I')).trans _,
  rw [mfderiv_id, mfderiv_const],
  refl
end

lemma mfderiv_prod_right {x₀ : M} {y₀ : M'} :
  mfderiv I' (I.prod I') (λ y, (x₀, y)) y₀ = continuous_linear_map.inr 𝕜 E E' :=
begin
  refine ((mdifferentiable_at_const I' I).mfderiv_prod (mdifferentiable_at_id I')).trans _,
  rw [mfderiv_id, mfderiv_const],
  refl
end

lemma mfderiv_prod_eq_add {f : N × M → M'} {p : N × M}
  (hf : mdifferentiable_at (J.prod I) I' f p) :
  mfderiv (J.prod I) I' f p =
  (show F × E →L[𝕜] E', from mfderiv (J.prod I) I' (λ (z : N × M), f (z.1, p.2)) p +
  mfderiv (J.prod I) I' (λ (z : N × M), f (p.1, z.2)) p) :=
begin
  dsimp only,
  rw [← @prod.mk.eta _ _ p] at hf,
  rw [mfderiv_comp p (by apply hf) (smooth_fst.prod_mk smooth_const).mdifferentiable_at,
    mfderiv_comp p (by apply hf) (smooth_const.prod_mk smooth_snd).mdifferentiable_at,
    ← continuous_linear_map.comp_add,
    smooth_fst.mdifferentiable_at.mfderiv_prod smooth_const.mdifferentiable_at,
    smooth_const.mdifferentiable_at.mfderiv_prod smooth_snd.mdifferentiable_at,
    mfderiv_fst, mfderiv_snd, mfderiv_const, mfderiv_const],
  symmetry,
  convert continuous_linear_map.comp_id _,
  { exact continuous_linear_map.fst_prod_zero_add_zero_prod_snd },
  simp_rw [prod.mk.eta],
end

-- lemma cont_mdiff_within_at_insert :
--   cont_mdiff_within_at I I' n f (insert x' s) x ↔ cont_mdiff_within_at I I' n f s x :=
-- begin
--   sorry
-- end

-- alias cont_mdiff_within_at_insert ↔ cont_mdiff_within_at.of_insert cont_mdiff_within_at.insert'

-- lemma cont_mdiff_within_at.insert (h : cont_mdiff_within_at I I' n f s x) :
--   cont_mdiff_within_at I I' n f (insert x s) x :=
-- h.insert'

/-- A function is `C^n` at a point, for `n : ℕ`, if and only if it is `C^n` on
a neighborhood of this point. -/
lemma cont_mdiff_within_at_iff_cont_mdiff_within_at_nhds_within {n : ℕ} :
  cont_mdiff_within_at I I' n f s x ↔
  ∀ᶠ x' in 𝓝[insert x s] x, cont_mdiff_within_at I I' n f s x' :=
begin
  refine ⟨_, λ h, h.self_of_nhds_within (mem_insert x s)⟩,
  rw [cont_mdiff_within_at_iff_cont_mdiff_on_nhds],
  rintro ⟨u, hu, h⟩,
  filter_upwards [eventually_mem_nhds_within'.mpr hu, hu] with x' hx' h2x',
  exact (h x' h2x').mono_of_mem (nhds_within_mono x' (subset_insert x s) hx')
end


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
  in charts around `y`, `in_coordinates' Z Z₂ x₀ x y₀ y ϕ` is a coordinate change of this continuous
  linear map that makes sense from charts around `x₀` to charts around `y₀`
  by composing it with appropriate coordinate changes given by smooth vector bundles `Z` and `Z₂`.
-/
def in_coordinates' (x₀ x : M) (y₀ y : M') (ϕ : Z x →L[𝕜] Z₂ y) : F₁ →L[𝕜] F₂ :=
(trivialization_at F₂ Z₂ y₀).continuous_linear_map_at 𝕜 y ∘L ϕ ∘L
(trivialization_at F₁ Z x₀).symmL 𝕜 x

/-- When `ϕ x` is a continuous linear map that changes vectors in charts around `f x` to vectors
  in charts around `g x`, `in_coordinates I I' f g ϕ x₀ x` is a coordinate change of this continuous
  linear map that makes sense from charts around `f x₀` to charts around `g x₀`
  by composing it with appropriate coordinate changes.
  Note that in the type of `ϕ` is more accurately
  `Π x : N, tangent_space I (f x) →L[𝕜] tangent_space I' (g x)`.
  We are unfolding `tangent_space` in this type so that Lean recognizes that the type of `ϕ` doesn't
  actually depend on `f` or `g`. -/
def in_coordinates (f : N → M) (g : N → M') (ϕ : N → E →L[𝕜] E') : N → N → E →L[𝕜] E' :=
λ x₀ x, in_coordinates' E E' (tangent_space I) (tangent_space I') (f x₀) (f x) (g x₀) (g x) (ϕ x)

variables {F₁ F₂}

/-! Todo: use `in_coordinates'` instead of `in_coordinates_core'`.
These are the same mathematical object, but not equal, since they are defined differently if the
`x` and the `y` are not in the right charts. -/
def in_coordinates_core' {ι₁ ι₂} (Z₁ : vector_bundle_core 𝕜 M F₁ ι₁)
  (Z₂ : vector_bundle_core 𝕜 M' F₂ ι₂) (x₀ x : M) (y₀ y : M') (ϕ : F₁ →L[𝕜] F₂) : F₁ →L[𝕜] F₂ :=
Z₂.coord_change (Z₂.index_at y) (Z₂.index_at y₀) y ∘L ϕ ∘L
  Z₁.coord_change (Z₁.index_at x₀) (Z₁.index_at x) x

/-! Todo: use `in_coordinates` instead of `in_coordinates_core`.
These are the same mathematical object, but not equal, since they are defined differently if the
`f x` and the `g x` are not in the right charts. -/
def in_coordinates_core (f : N → M) (g : N → M') (ϕ : N → E →L[𝕜] E') :
  N → N → E →L[𝕜] E' :=
λ x₀ x, in_coordinates_core' (tangent_bundle_core I M) (tangent_bundle_core I' M')
  (f x₀) (f x) (g x₀) (g x) (ϕ x)

/-- rewrite `in_coordinates'` using continuous linear equivalences. -/
lemma in_coordinates'_eq (x₀ x : M) (y₀ y : M') (ϕ : Z x →L[𝕜] Z₂ y)
  (hx : x ∈ (trivialization_at F₁ Z x₀).base_set)
  (hy : y ∈ (trivialization_at F₂ Z₂ y₀).base_set) :
  in_coordinates' F₁ F₂ Z Z₂ x₀ x y₀ y ϕ =
  ((trivialization_at F₂ Z₂ y₀).continuous_linear_equiv_at 𝕜 y hy : Z₂ y →L[𝕜] F₂) ∘L ϕ ∘L
  (((trivialization_at F₁ Z x₀).continuous_linear_equiv_at 𝕜 x hx).symm : F₁ →L[𝕜] Z x) :=
begin
  ext,
  simp_rw [in_coordinates', continuous_linear_map.coe_comp', continuous_linear_equiv.coe_coe,
    trivialization.coe_continuous_linear_equiv_at_eq,
    trivialization.symm_continuous_linear_equiv_at_eq]
end

lemma in_coordinates_core'_eq {ι₁ ι₂} (Z₁ : vector_bundle_core 𝕜 M F₁ ι₁)
  (Z₂ : vector_bundle_core 𝕜 M' F₂ ι₂)
  {x₀ x : M} {y₀ y : M'} (ϕ : F₁ →L[𝕜] F₂)
  (hx : x ∈ Z₁.base_set (Z₁.index_at x₀))
  (hy : y ∈ Z₂.base_set (Z₂.index_at y₀)) :
    in_coordinates_core' Z₁ Z₂ x₀ x y₀ y ϕ =
    in_coordinates' F₁ F₂ Z₁.fiber Z₂.fiber x₀ x y₀ y ϕ :=
by simp_rw [in_coordinates', in_coordinates_core',
    Z₂.trivialization_at_continuous_linear_map_at hy, Z₁.trivialization_at_symmL hx]

/-- The map `in_coordinates'` is trivial on the model spaces -/
lemma in_coordinates'_tangent_bundle_core_model_space
  (x₀ x : H) (y₀ y : H') (ϕ : E →L[𝕜] E') :
    in_coordinates' E E' (tangent_space I) (tangent_space I') x₀ x y₀ y ϕ = ϕ :=
begin
  have : in_coordinates_core' (tangent_bundle_core I H) (tangent_bundle_core I' H') x₀ x y₀ y ϕ = ϕ,
  { simp_rw [in_coordinates_core', tangent_bundle_core_index_at,
    tangent_bundle_core_coord_change_model_space,
    continuous_linear_map.id_comp, continuous_linear_map.comp_id] },
  conv_rhs { rw [← this] },
  rw [in_coordinates_core'_eq],
  exacts [rfl, mem_univ x, mem_univ y],
end

lemma in_coordinates_model_space (f : N → H) (g : N → H') (ϕ : N → E →L[𝕜] E') (x₀ : N) :
    in_coordinates I I' f g ϕ x₀ = ϕ :=
by simp_rw [in_coordinates, in_coordinates'_tangent_bundle_core_model_space]

lemma in_coordinates_core_eq (f : N → M) (g : N → M') (ϕ : N → E →L[𝕜] E') {x₀ x : N}
  (hx : f x ∈ (chart_at H (f x₀)).source) (hy : g x ∈ (chart_at H' (g x₀)).source) :
  in_coordinates I I' f g ϕ x₀ x =
  (tangent_bundle_core I' M').coord_change (achart H' (g x)) (achart H' (g x₀)) (g x) ∘L ϕ x ∘L
  (tangent_bundle_core I M).coord_change (achart H (f x₀)) (achart H (f x)) (f x) :=
(in_coordinates_core'_eq (tangent_bundle_core I M) (tangent_bundle_core I' M') (ϕ x) hx hy).symm

variables {I I'}

attribute [mfld_simps] mem_insert_iff

/-- Proving this without the assumption `x₀ ∈ s` might be possible, but is nontrivial.
  Todo: use `mfderiv_within`, either with the same set or a different set. -/
lemma cont_mdiff_within_at.mfderiv {s : set N} {x₀ : N} (f : N → M → M') (g : N → M)
  (hf : cont_mdiff_within_at (J.prod I) I' n (function.uncurry f) (prod.fst ⁻¹' s) (x₀, g x₀))
  (hg : cont_mdiff_within_at J I m g s x₀) (hx₀ : x₀ ∈ s) (hmn : m + 1 ≤ n) :
  cont_mdiff_within_at J 𝓘(𝕜, E →L[𝕜] E') m
    (in_coordinates I I' g (λ x, f x (g x)) (λ x, mfderiv I I' (f x) (g x)) x₀) s x₀ :=
begin
  have h4f : (λ x, f x (g x)) ⁻¹' (ext_chart_at I' (f x₀ (g x₀))).source ∈ 𝓝[s] x₀,
  { have : continuous_within_at (λ x, f x (g x)) s x₀,
    { apply continuous_within_at.comp (by apply hf.continuous_within_at)
        (continuous_within_at_id.prod hg.continuous_within_at),
      simp_rw [maps_to', image_subset_iff, preimage_preimage, preimage_id] },
    exact this.preimage_mem_nhds_within (ext_chart_at_source_mem_nhds I' (f x₀ (g x₀))) },
  have h2f : ∀ᶠ x₂ in 𝓝[s] x₀, cont_mdiff_within_at I I' 1 (f x₂) (g '' s) (g x₂),
  { have := cont_mdiff_within_at_iff_cont_mdiff_within_at_nhds_within.mp
      (hf.of_le $ (self_le_add_left 1 m).trans hmn),
    have := (continuous_within_at_id.prod hg.continuous_within_at).eventually _,
    filter_upwards [this] with x hx,
    swap, exact cont_mdiff_within_at (J.prod I) I' ↑1 (uncurry f) (prod.fst ⁻¹' s),
    refine hx.comp (g x) (cont_mdiff_within_at_const.prod_mk cont_mdiff_within_at_id) _,
    classical,
    simp_rw [maps_to', image_subset_iff, preimage_preimage, id, preimage_const],
    sorry, --false
    sorry
    },
  have h2g : g ⁻¹' (ext_chart_at I (g x₀)).source ∈ 𝓝[s] x₀ :=
    hg.continuous_within_at.preimage_mem_nhds_within
      (ext_chart_at_source_mem_nhds I (g x₀)),
  have : cont_diff_within_at 𝕜 m (λ x', fderiv_within 𝕜
    (ext_chart_at I' (f x₀ (g x₀)) ∘ f ((ext_chart_at J x₀).symm x') ∘ (ext_chart_at I (g x₀)).symm)
    (range I) (ext_chart_at I (g x₀) (g ((ext_chart_at J x₀).symm x'))))
    ((ext_chart_at J x₀).symm ⁻¹' s ∩ range J) (ext_chart_at J x₀ x₀),
  { rw [cont_mdiff_within_at_iff] at hf hg,
    simp_rw [function.comp, uncurry, ext_chart_at_prod, local_equiv.prod_coe_symm] at hf ⊢,
    refine (cont_diff_within_at_fderiv_within _
      (hg.2.insert.mono_of_mem _) I.unique_diff hmn _ _ _ _).mono_of_mem _,
    swap 3,
    { simp_rw [function.comp, ext_chart_at_to_inv], exact hf.2.insert },
    { refine (ext_chart_at J x₀).symm ⁻¹' (s) ∩ (ext_chart_at J x₀).target ∩
        (ext_chart_at J x₀).symm ⁻¹' (g ⁻¹' (ext_chart_at I (g x₀)).source) },
    { refine mem_of_superset self_mem_nhds_within ((inter_subset_left _ _).trans $ _),
      sorry -- set theory made stupid because of an insert
      -- exact inter_subset_inter_right _ (ext_chart_at_target_subset_range J x₀)
      },
    { simp_rw [mem_inter_iff, mem_preimage, ext_chart_at_to_inv],
      exact ⟨⟨hx₀, local_equiv.maps_to _ (mem_ext_chart_source J x₀)⟩,
        mem_ext_chart_source I (g x₀)⟩ },
    { simp_rw [model_with_corners.range_prod],
      rw [inter_assoc, inter_prod],
      sorry,  -- more stupid set theory made stupid because of an insert
      -- refine inter_subset_inter _ _,
      -- { sorry },
      -- exact set.prod_mono ((inter_subset_left _ _).trans $ ext_chart_at_target_subset_range J x₀)
      --   subset_rfl
         },
    { refine eventually_of_forall (λ x', mem_range_self _) },
    swap 2,
    { sorry,
      -- refine inter_mem (ext_chart_at_target_mem_nhds_within J x₀) _,
      -- ext_chart_at_preimage_mem_nhds_within
      -- refine nhds_within_le_nhds (ext_chart_at_preimage_mem_nhds' _ _ (mem_ext_chart_source J x₀) _),
      -- exact hg.1.preimage_mem_nhds (ext_chart_at_source_mem_nhds I (g x₀))
      },
    simp_rw [function.comp, ext_chart_at_to_inv],
    refine mem_of_superset self_mem_nhds_within _,
    refine (image_subset_range _ _).trans _,
    exact range_comp_subset_range (λ a, chart_at H (g x₀) $ g $ (chart_at G x₀).symm $ J.symm a) I },
  have : cont_mdiff_within_at J 𝓘(𝕜, E →L[𝕜] E') m
    (λ x', fderiv_within 𝕜 (ext_chart_at I' (f x₀ (g x₀)) ∘ f x' ∘ (ext_chart_at I (g x₀)).symm)
    (range I) (ext_chart_at I (g x₀) (g x'))) s x₀,
  { simp_rw [cont_mdiff_within_at_iff_source_of_mem_source (mem_chart_source G x₀),
      cont_mdiff_within_at_iff_cont_diff_within_at, function.comp],
    exact this },
  have : cont_mdiff_within_at J 𝓘(𝕜, E →L[𝕜] E') m
    (λ x', fderiv_within 𝕜 (ext_chart_at I' (f x₀ (g x₀)) ∘ (ext_chart_at I' (f x' (g x'))).symm ∘
      written_in_ext_chart_at I I' (g x') (f x') ∘ ext_chart_at I (g x') ∘
      (ext_chart_at I (g x₀)).symm) (range I) (ext_chart_at I (g x₀) (g x'))) s x₀,
  { refine this.congr_of_eventually_eq_insert _,
    rw [insert_eq_of_mem hx₀],
    filter_upwards [h2g, h2f],
    intros x₂ hx₂ h2x₂,
    have : ∀ x' ∈ (ext_chart_at I (g x₀)).symm ⁻¹' (ext_chart_at I (g x₂)).source ∩
        (ext_chart_at I (g x₀)).symm ⁻¹' (f x₂ ⁻¹' (ext_chart_at I' (f x₂ (g x₂))).source),
      (ext_chart_at I' (f x₀ (g x₀)) ∘ (ext_chart_at I' (f x₂ (g x₂))).symm ∘
      written_in_ext_chart_at I I' (g x₂) (f x₂) ∘ ext_chart_at I (g x₂) ∘
      (ext_chart_at I (g x₀)).symm) x' =
      ext_chart_at I' (f x₀ (g x₀)) (f x₂ ((ext_chart_at I (g x₀)).symm x')),
    { rintro x' ⟨hx', h2x'⟩,
      simp_rw [written_in_ext_chart_at, function.comp_apply],
      rw [(ext_chart_at I (g x₂)).left_inv hx', (ext_chart_at I' (f x₂ (g x₂))).left_inv h2x'] },
    refine filter.eventually_eq.fderiv_within_eq_nhds (I.unique_diff _ $ mem_range_self _) _,
    refine eventually_of_mem (inter_mem _ _) this,
    { exact ext_chart_at_preimage_mem_nhds' _ _ hx₂ (ext_chart_at_source_mem_nhds I (g x₂)) },
    refine ext_chart_at_preimage_mem_nhds' _ _ hx₂ _,
    sorry
    -- exact h2x₂.continuous_within_at.preimage_mem_nhds_within (ext_chart_at_source_mem_nhds _ _)
     },
  refine this.congr_of_eventually_eq_insert _,
  rw [insert_eq_of_mem hx₀],
  filter_upwards [h2g, h2f, h4f],
  intros x₂ hx₂ h2x₂ h3x₂,
  symmetry,
  rw [in_coordinates_core_eq],
  swap, { rwa [ext_chart_at_source] at hx₂ },
  swap, { rwa [ext_chart_at_source] at h3x₂ },
  sorry,
  -- rw [(h2x₂.mdifferentiable_at le_rfl).mfderiv],
  -- have hI := (cont_diff_within_at_ext_coord_change I (g x₂) (g x₀) $
  --   local_equiv.mem_symm_trans_source _ hx₂ $ mem_ext_chart_source I (g x₂))
  --   .differentiable_within_at le_top,
  -- have hI' := (cont_diff_within_at_ext_coord_change I' (f x₀ (g x₀)) (f x₂ (g x₂)) $
  --   local_equiv.mem_symm_trans_source _
  --   (mem_ext_chart_source I' (f x₂ (g x₂))) h3x₂).differentiable_within_at le_top,
  -- have h3f := (h2x₂.mdifferentiable_at le_rfl).2,
  -- refine fderiv_within.comp₃ _ hI' h3f hI _ _ _ _ (I.unique_diff _ $ mem_range_self _),
  -- { exact λ x _, mem_range_self _ },
  -- { exact λ x _, mem_range_self _ },
  -- { simp_rw [written_in_ext_chart_at, function.comp_apply,
  --     (ext_chart_at I (g x₂)).left_inv (mem_ext_chart_source I (g x₂))] },
  -- { simp_rw [function.comp_apply, (ext_chart_at I (g x₀)).left_inv hx₂] }
end

/-- The function that sends `x` to the `y`-derivative of `f(x,y)` at `g(x)` is `C^n` at `x₀`,
where the derivative is taken as a continuous linear map.
We have to assume that `f` is `C^(n+1)` at `(x₀, g(x₀))` and `g` is `C^n` at `x₀`.
We have to insert appropriate coordinate changes to make the derivative sensible.
`cont_mdiff_at.mfderiv_id` and `cont_mdiff_at.mfderiv_const` are special cases of this.

This lemma should be generalized to a `cont_mdiff_within_at` for `mfderiv_within`. If we do that, we
can deduce `cont_mdiff_on.cont_mdiff_on_tangent_map_within` from this.
-/
lemma cont_mdiff_at.mfderiv {x₀ : N} (f : N → M → M') (g : N → M)
  (hf : cont_mdiff_at (J.prod I) I' n (function.uncurry f) (x₀, g x₀))
  (hg : cont_mdiff_at J I m g x₀) (hmn : m + 1 ≤ n) :
  cont_mdiff_at J 𝓘(𝕜, E →L[𝕜] E') m
    (in_coordinates I I' g (λ x, f x (g x)) (λ x, mfderiv I I' (f x) (g x)) x₀) x₀ :=
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
  rw [in_coordinates_core_eq],
  { refl },
  { rwa [ext_chart_at_source] at hx },
  { rwa [ext_chart_at_source] at h2x },
end

/-- The function `x ↦ D_yf(x,y)` is `C^n` at `x₀`, where the derivative is taken as a continuous
linear map. We have to assume that `f` is `C^(n+1)` at `(x₀, x₀)`.
We have to insert appropriate coordinate changes to make the derivative sensible.
This is a special case of `cont_mdiff_at.mfderiv` (with `g = id`),
and `cont_mdiff_at.mfderiv_const` is a special case of this.
-/
lemma cont_mdiff_at.mfderiv_id {x₀ : M} (f : M → M → M')
  (hf : cont_mdiff_at (I.prod I) I' n (function.uncurry f) (x₀, x₀)) (hmn : m + 1 ≤ n) :
  cont_mdiff_at I 𝓘(𝕜, E →L[𝕜] E') m
    (in_coordinates I I' id (λ x, f x x) (λ x, mfderiv I I' (f x) x) x₀) x₀ :=
hf.mfderiv f id cont_mdiff_at_id hmn

/-- The derivative `D_yf(y)` is `C^n` at `x₀`, where the derivative is taken as a continuous
linear map. We have to assume that `f` is `C^(n+1)` at `x₀`.
We have to insert appropriate coordinate changes to make the derivative sensible.
This is a special case of See `cont_mdiff_at.mfderiv_id` where `f` does not contain any parameters.
-/
lemma cont_mdiff_at.mfderiv_const {x₀ : M} {f : M → M'}
  (hf : cont_mdiff_at I I' n f x₀) (hmn : m + 1 ≤ n) :
  cont_mdiff_at I 𝓘(𝕜, E →L[𝕜] E') m (in_coordinates I I' id f (mfderiv I I' f) x₀) x₀ :=
begin
  have : cont_mdiff_at (I.prod I) I' n (λ x : M × M, f x.2) (x₀, x₀) :=
  cont_mdiff_at.comp (x₀, x₀) hf cont_mdiff_at_snd,
  apply cont_mdiff_at.mfderiv_id (λ x, f) this hmn
end

lemma cont_mdiff_at.mfderiv_apply {x₀ : N'} (f : N → M → M') (g : N → M) (g₁ : N' → N)
  (g₂ : N' → E)
  (hf : cont_mdiff_at (J.prod I) I' n (function.uncurry f) (g₁ x₀, g (g₁ x₀)))
  (hg : cont_mdiff_at J I m g (g₁ x₀))
  (hg₁ : cont_mdiff_at J' J m g₁ x₀)
  (hg₂ : cont_mdiff_at J' 𝓘(𝕜, E) m g₂ x₀) (hmn : m + 1 ≤ n) :
  cont_mdiff_at J' 𝓘(𝕜, E') m
    (λ x, in_coordinates I I' g (λ x, f x (g x)) (λ x, mfderiv I I' (f x) (g x))
      (g₁ x₀) (g₁ x) (g₂ x))
    x₀ :=
(cont_mdiff_at.comp x₀ (by apply hf.mfderiv f g hg hmn) hg₁).clm_apply hg₂

instance has_smooth_add_self : has_smooth_add 𝓘(𝕜, F) F :=
⟨by { convert cont_diff_add.cont_mdiff, exact model_with_corners_self_prod.symm,
  exact charted_space_self_prod }⟩

theorem cont_mdiff_at_tangent_bundle_trivialization_at_continuous_linear_map
  (x₀ : tangent_bundle I M) :
  cont_mdiff_at I.tangent 𝓘(𝕜, E) m (λ x : tangent_bundle I M,
    (trivialization_at E (tangent_space I) x₀.proj).continuous_linear_map_at 𝕜 x.proj x.2) x₀ :=
begin
  let e := trivialization_at E (tangent_space I) x₀.proj,
  refine cont_mdiff_at.congr_of_eventually_eq _ _,
  swap 3,
  have h1 := (continuous_proj E (tangent_space I)).continuous_at.preimage_mem_nhds
    (e.open_base_set.mem_nhds $ mem_base_set_trivialization_at _ _ _),
  filter_upwards [h1] with x hx,
  rw [trivialization.continuous_linear_map_at_apply, e.coe_linear_map_at_of_mem hx],
  exact (e.smooth_at I $ mem_base_set_trivialization_at E _ _).snd.of_le le_top,
end

/-- Not useful by itself. TODO: generalize to `cont_mdiff_within_at` of `tangent_map_within` -/
theorem cont_mdiff_at.cont_mdiff_at_tangent_map (x₀ : tangent_bundle I M)
  (hf : cont_mdiff_at I I' n f x₀.proj) (hmn : m + 1 ≤ n) :
  cont_mdiff_at I.tangent I'.tangent m (tangent_map I I' f) x₀ :=
begin
  rw cont_mdiff_at_total_space,
  refine ⟨(hf.comp x₀ (cont_mdiff_at_proj (tangent_space I))).of_le $
    (self_le_add_right m 1).trans hmn, _⟩,
  dsimp only [tangent_map, total_space.proj_mk],
  let e := trivialization_at E (tangent_space I) x₀.proj,
  let e' := trivialization_at E' (tangent_space I') (f x₀.proj),
  have : cont_mdiff_at I.tangent 𝓘(𝕜, E') m (λ x : tangent_bundle I M,
    in_coordinates I I' id f (mfderiv I I' f) x₀.proj x.proj $
    e.continuous_linear_map_at 𝕜 x.proj x.2) x₀,
  { refine cont_mdiff_at.mfderiv_apply (λ _, f) id total_space.proj
      (λ x, e.continuous_linear_map_at 𝕜 x.proj x.2) _ cont_mdiff_at_id (cont_mdiff_at_proj _) _
      hmn,
    apply cont_mdiff_at.comp (x₀.proj, x₀.proj) (by exact hf) cont_mdiff_at_snd,
    apply cont_mdiff_at_tangent_bundle_trivialization_at_continuous_linear_map },
  refine this.congr_of_eventually_eq _,
  have h1 := (continuous_proj E (tangent_space I)).continuous_at.preimage_mem_nhds
    (e.open_base_set.mem_nhds $ mem_base_set_trivialization_at _ _ _),
  have h2 := (hf.continuous_at.comp (continuous_proj E (tangent_space I)).continuous_at)
    .preimage_mem_nhds (e'.open_base_set.mem_nhds $ mem_base_set_trivialization_at _ _ _),
  filter_upwards [h1, h2] with x hx h2x,
  dsimp only [in_coordinates, in_coordinates', id_def],
  simp_rw [continuous_linear_map.comp_apply, e.symmL_continuous_linear_map_at hx,
    trivialization.continuous_linear_map_at_apply, e'.coe_linear_map_at_of_mem h2x],
end

end smooth_manifold_with_corners

section maps

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
{E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
{E' : Type*} [normed_add_comm_group E'] [normed_space 𝕜 E']
{F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]
{H : Type*} [topological_space H]
{H' : Type*} [topological_space H']
{G : Type*} [topological_space G]
{G' : Type*} [topological_space G']
{I : model_with_corners 𝕜 E H} {I' : model_with_corners 𝕜 E' H'}
{J : model_with_corners 𝕜 F G} {J' : model_with_corners 𝕜 F G'}

variables {M : Type*} [topological_space M] [charted_space H M]
{M' : Type*} [topological_space M'] [charted_space H' M']
{N : Type*} [topological_space N] [charted_space G N]
{N' : Type*} [topological_space N'] [charted_space G' N']
{n : ℕ∞}
(f : C^∞⟮I, M; J, N⟯)

namespace cont_mdiff_map

/-- The first projection of a product, as a smooth map. -/
def fst : C^n⟮I.prod I', M × M'; I, M⟯ := ⟨prod.fst, cont_mdiff_fst⟩

/-- The second projection of a product, as a smooth map. -/
def snd : C^n⟮I.prod I', M × M'; I', M'⟯ := ⟨prod.snd, cont_mdiff_snd⟩

/-- Given two smooth maps `f` and `g`, this is the smooth map `(x, y) ↦ (f x, g y)`. -/
def prod_mk (f : C^n⟮J, N; I, M⟯) (g : C^n⟮J, N; I', M'⟯) : C^n⟮J, N; I.prod I', M × M'⟯ :=
⟨λ x, (f x, g x), f.2.prod_mk g.2⟩

end cont_mdiff_map

namespace diffeomorph

instance : continuous_map_class (M ≃ₘ⟮I, J⟯ N) M N :=
{ coe := coe_fn,
  coe_injective' := coe_fn_injective,
  map_continuous := λ f, f.continuous }

end diffeomorph

end maps

section
variables {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
  {H : Type*} [topological_space H] (I : model_with_corners ℝ E H) {M : Type*}
  [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
  {G : Type*} [normed_add_comm_group G] [normed_space ℝ G] [finite_dimensional ℝ G]
  {HG : Type*} [topological_space HG] (IG : model_with_corners ℝ G HG) {N : Type*}
  [topological_space N] [charted_space HG N] [smooth_manifold_with_corners IG N]

def filter.germ.cont_mdiff_at' {x : M} (φ : germ (𝓝 x) N) (n : ℕ∞) : Prop :=
quotient.lift_on' φ (λ f, cont_mdiff_at I IG n f x) (λ f g h, propext begin
  split,
  all_goals { refine λ H, H.congr_of_eventually_eq _ },
  exacts [h.symm, h]
end)
end
