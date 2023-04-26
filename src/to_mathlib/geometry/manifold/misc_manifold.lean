import to_mathlib.geometry.manifold.mfderiv
import to_mathlib.analysis.calculus
import geometry.manifold.diffeomorph
import geometry.manifold.algebra.monoid
import geometry.manifold.metrizable

open bundle set function filter
open_locale manifold topology
noncomputable theory

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


namespace vector_bundle_core

variables {𝕜 B F : Type*} [nontrivially_normed_field 𝕜]
  [normed_add_comm_group F] [normed_space 𝕜 F] [topological_space B]
  {ι : Type*} (Z : vector_bundle_core 𝕜 B F ι) {i j : ι}

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

instance {x : M} : has_continuous_add (tangent_space I x) := by delta_instance tangent_space

end

section real

variables {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
{H : Type*} [topological_space H] {I : model_with_corners ℝ E H}
{M : Type*} [topological_space M] [charted_space H M]
{F : Type*} [normed_add_comm_group F] [normed_space ℝ F]

variables [smooth_manifold_with_corners I M]

instance {x : M} : path_connected_space (tangent_space I x) := by delta_instance tangent_space

end real

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

variables [smooth_manifold_with_corners I M] [smooth_manifold_with_corners I' M']
  [smooth_manifold_with_corners J N]

-- lemma cont_diff_on_coord_change' {e e' : local_homeomorph M H}
--   (h : e ∈ atlas H M) (h' : e' ∈ atlas H M) :
--   cont_diff_on 𝕜 ⊤ (I ∘ (e.symm ≫ₕ e') ∘ I.symm) (I.symm ⁻¹' (e.symm ≫ₕ e').source ∩ range I) :=
-- (has_groupoid.compatible (cont_diff_groupoid ⊤ I) h h').1

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

lemma mdifferentiable_at.prod_mk {f : N → M} {g : N → M'} {x : N}
  (hf : mdifferentiable_at J I f x)
  (hg : mdifferentiable_at J I' g x) :
  mdifferentiable_at J (I.prod I') (λ x, (f x, g x)) x :=
⟨hf.1.prod hg.1, hf.2.prod hg.2⟩

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

open bundle
variables
  {Z : M → Type*} [topological_space (total_space Z)] [∀ b, topological_space (Z b)]
  [∀ b, add_comm_monoid (Z b)] [∀ b, module 𝕜 (Z b)]
  [fiber_bundle F₁ Z] [vector_bundle 𝕜 F₁ Z] [smooth_vector_bundle F₁ Z I]
  {Z₂ : M' → Type*} [topological_space (total_space Z₂)] [∀ b, topological_space (Z₂ b)]
  [∀ b, add_comm_monoid (Z₂ b)] [∀ b, module 𝕜 (Z₂ b)]
  [fiber_bundle F₂ Z₂] [vector_bundle 𝕜 F₂ Z₂] [smooth_vector_bundle F₂ Z₂ I']

open_locale bundle

/-- The function that sends `x` to the `y`-derivative of `f(x,y)` at `g(x)` applied to `g₂(x)` is
`C^n` at `x₀`, where the derivative is taken as a continuous linear map.
We have to assume that `f` is `C^(n+1)` at `(x₀, g(x₀))` and `g` is `C^n` at `x₀`.
We have to insert a coordinate change from `x₀` to `g₁(x)` to make the derivative sensible.

This is  similar to `cont_mdiff_at.mfderiv`, but where the continuous linear map is applied to a
(variable) vector.
-/
lemma cont_mdiff_at.mfderiv_apply {x₀ : N'} (f : N → M → M') (g : N → M) (g₁ : N' → N)
  (g₂ : N' → E)
  (hf : cont_mdiff_at (J.prod I) I' n (function.uncurry f) (g₁ x₀, g (g₁ x₀)))
  (hg : cont_mdiff_at J I m g (g₁ x₀))
  (hg₁ : cont_mdiff_at J' J m g₁ x₀)
  (hg₂ : cont_mdiff_at J' 𝓘(𝕜, E) m g₂ x₀) (hmn : m + 1 ≤ n) :
  cont_mdiff_at J' 𝓘(𝕜, E') m
    (λ x, in_tangent_coordinates I I' g (λ x, f x (g x)) (λ x, mfderiv I I' (f x) (g x))
      (g₁ x₀) (g₁ x) (g₂ x))
    x₀ :=
((hf.mfderiv f g hg hmn).comp_of_eq hg₁ rfl).clm_apply hg₂

instance has_smooth_add_self : has_smooth_add 𝓘(𝕜, F) F :=
⟨by { convert cont_diff_add.cont_mdiff, exact model_with_corners_self_prod.symm,
  exact charted_space_self_prod }⟩

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
