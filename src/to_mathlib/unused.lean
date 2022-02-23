import algebra.module.ulift
import measure_theory.constructions.borel_space
import to_mathlib.analysis.calculus

/-!
Lemmas that are unused in the sphere-eversion project, but were formulated for one reason or another
(because they seemed useful at the time). If the lemmas are still useful, we would still like to
move them to mathlib, but if they aren't that useful after all, we can decide to remove them.

This file should *not* be imported in any other file (and this file can import anything).
-/

open_locale filter unit_interval topological_space uniformity
open function filter set

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
@[simp] lemma base_apply {α β : Type*} (f : α → β) (x : α) : ↿f x = f x := rfl
@[simp] lemma induction_apply {α β γ δ : Type*} {h : has_uncurry β γ δ} (f : α → β) (x : α)
  (c : γ) : ↿f (x, c) = ↿(f x) c :=
rfl

-- @[simp] lemma uncurry_loop_apply {F : Type*} [normed_group F] [normed_space ℝ F]
--   [finite_dimensional ℝ F] {α : Type*} (f : α → loop F) (x : α) (t : ℝ) :
--   ↿f (x, t) = f x t :=
-- rfl

@[simp] lemma uncurry_path_apply {X α : Type*} [topological_space X] {x y : α → X}
  (f : Π a, path (x a) (y a)) (a : α) (t : I) : ↿f (a, t) = f a t :=
rfl

-- trying to make a simp set that unfolds `↿`. Doesn't always work.
mk_simp_attribute uncurry_simps "unfolds all occurrences of the uncurry operation `↿`."
attribute [uncurry_simps] function.has_uncurry_base function.has_uncurry_induction
  path.has_uncurry_path
-- attribute [uncurry_simps] has_uncurry_loop


end


section
variables {α : Type*} [uniform_space α]
-- to uniform_space/basic

-- `uniformity_eq_symm` should probably be reformulated in the library
lemma symm_eq_uniformity : map (@prod.swap α α) (𝓤 α) = 𝓤 α :=
uniformity_eq_symm.symm

lemma nhds_eq_comap_uniformity_rev {y : α} : 𝓝 y = (𝓤 α).comap (λ x, (x, y)) :=
by { rw [uniformity_eq_symm, map_swap_eq_comap_swap, comap_comap], exact nhds_eq_comap_uniformity }

end

-- useful / better reformulation of existing lemma (unused in mathlib)
lemma continuous_subtype_is_closed_cover' {α β : Type*} [topological_space α] [topological_space β]
  {ι : Sort*} {f : α → β} (c : ι → set α)
  (h_lf : locally_finite c)
  (h_is_closed : ∀ i, is_closed (c i))
  (h_cover : (⋃ i, c i) = univ)
  (f_cont  : ∀ i, continuous (λ(x : c i), f x)) :
  continuous f :=
continuous_subtype_is_closed_cover (λ i, (∈ c i)) h_lf h_is_closed
  (by simpa [eq_univ_iff_forall] using h_cover) f_cont

section lift

open topological_space
/-! We used the below lemmas about ulift to remove a universe restriction in
`cont_diff_parametric_primitive_of_cont_diff`.
Due to a new proof that is not necessary anymore. -/

universe variables v u

variables {E : Type u}

-- set_option pp.universes true
-- note: we can almost certainly remove all `.{v}` below
open ulift

@[to_additive, simps apply] def monoid_hom.up [mul_one_class E] : E →* ulift E :=
⟨up, rfl, λ x y, rfl⟩
@[to_additive, simps] def monoid_hom.down [mul_one_class E] : ulift E →* E :=
⟨down, rfl, λ x y, rfl⟩

instance [normed_group E] : normed_group (ulift.{v} E) :=
normed_group.induced add_monoid_hom.down equiv.ulift.injective

instance {F} [normed_field F] [normed_group E] [normed_space F E] : normed_space F (ulift.{v} E) :=
{ norm_smul_le := by { rintro x ⟨y⟩, exact normed_space.norm_smul_le x y },
  ..ulift.module' }

instance {X} [topological_space X] [second_countable_topology X] :
  second_countable_topology (ulift.{v} X) :=
homeomorph.ulift.second_countable_topology

instance {X} [uniform_space X] : uniform_space (ulift.{v} X) :=
uniform_space.comap down ‹_›

lemma uniformity.ulift {X} [uniform_space X] :
  uniformity (ulift X) = comap (prod.map down down) (uniformity X) :=
uniformity_comap rfl

lemma uniform_continuous.ulift {X} [uniform_space X] :
  uniform_continuous (@homeomorph.ulift X _) :=
by { rw [uniform_continuous, uniformity.ulift], exact tendsto_comap }

lemma homeomorph.complete_space {X Y} [uniform_space X] [uniform_space Y] [complete_space Y]
  (φ : X ≃ₜ Y) (hφ : uniform_continuous φ) : complete_space X :=
begin
  constructor,
  intros f hf,
  obtain ⟨y, hy⟩ := complete_space.complete (hf.map hφ),
  refine ⟨φ.symm y, _⟩,
  rw [← φ.symm.map_nhds_eq],
  rw [map_le_iff_le_comap] at hy,
  convert hy,
  -- better lemma here would be useful
  exact map_eq_comap_of_inverse (funext φ.left_inv) (funext φ.right_inv)
end

instance {X} [uniform_space X] [complete_space X] : complete_space (ulift.{v} X) :=
homeomorph.complete_space homeomorph.ulift uniform_continuous.ulift

instance {E} [measurable_space E] : measurable_space (ulift.{v} E) :=
measurable_space.comap down ‹_›

instance {X} [measurable_space X] [topological_space X] [borel_space X] :
  borel_space (ulift.{v} X) :=
⟨by { rw [← borel_comap.symm, (borel_space.measurable_eq.symm : borel X = _)], refl }⟩

attribute [simps] mul_equiv.ulift

/-- `ulift M → M` is a linear equivalence. -/
@[simps {simp_rhs := tt}] def linear_equiv.ulift (R M : Type*)
  [semiring R] [add_comm_monoid M] [module R M] : ulift.{v} M ≃ₗ[R] M :=
{ map_smul' := λ x m, rfl, ..add_equiv.ulift }

/-- `ulift M → M` is a continuous linear equivalence -/
@[simps apply symm_apply {simp_rhs := tt}]
def continuous_linear_equiv.ulift (R M : Type*) [semiring R] [topological_space M]
  [add_comm_monoid M] [module R M] : ulift.{v} M ≃L[R] M :=
{ ..linear_equiv.ulift R M, ..homeomorph.ulift }

lemma cont_diff_up {F X : Type*} [nondiscrete_normed_field F] [normed_group X]
  [normed_space F X] {n : with_top ℕ} : cont_diff F n (@up X) :=
(continuous_linear_equiv.ulift F X).symm.cont_diff

lemma cont_diff_down {F X : Type*} [nondiscrete_normed_field F] [normed_group X]
  [normed_space F X] {n : with_top ℕ} : cont_diff F n (@down X) :=
(continuous_linear_equiv.ulift F X).cont_diff

lemma cont_diff_up_iff {F X Y : Type*} [nondiscrete_normed_field F] [normed_group X]
  [normed_space F X] [normed_group Y] [normed_space F Y] {n : with_top ℕ} (f : X → Y) :
  cont_diff F n (λ x, up (f x)) ↔ cont_diff F n f :=
(continuous_linear_equiv.ulift F Y).symm.comp_cont_diff_iff

end lift
