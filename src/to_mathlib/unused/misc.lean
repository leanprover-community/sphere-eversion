import algebra.module.ulift
import measure_theory.constructions.borel_space
import to_mathlib.analysis.calculus
import to_mathlib.data.real_basic
import order.filter.small_sets

/-!
Lemmas that are unused in the sphere-eversion project, but were formulated for one reason or another
(because they seemed useful at the time). If the lemmas are still useful, we would still like to
move them to mathlib, but if they aren't that useful after all, we can decide to remove them.

This file should *not* be imported in any other file (and this file can import anything).
-/

open_locale filter unit_interval topological_space uniformity
open function filter set

section order
lemma max_eq_of_lt_left {a b c : ℝ} (h : a < c) : max a b = c ↔ b = c :=
by simp [max_eq_iff, h.ne, h.le] {contextual := tt}
end order

namespace filter

variables {α β : Type*} {f : filter α} {g : filter β}

lemma eventually_eventually_of_eventually_prod {p : α → β → Prop}
  (h : ∀ᶠ (z : α × β) in f ×ᶠ g, p z.1 z.2) : ∀ᶠ x in f, ∀ᶠ y in g, p x y :=
begin
  rw [filter.eventually_prod_iff] at h, rcases h with ⟨pa, hpa, pb, hpb, h⟩,
  filter_upwards [hpa], intros a ha,
  filter_upwards [hpb], intros b hb, exact h ha hb
end

-- property of `small_sets`
lemma tendsto_sup_dist {X Y ι : Type*} {l : filter ι} [topological_space X] [metric_space Y]
  {f : X → Y} {t : X} (h : continuous_at f t)
  {s : ι → set X} (hs : tendsto s l (𝓝 t).small_sets) :
  tendsto (λ i, ⨆ x ∈ s i, dist (f x) (f t)) l (𝓝 0) :=
begin
  rw metric.tendsto_nhds,
  have nonneg : ∀ n, 0 ≤ ⨆ x ∈ s n, dist (f x) (f t),
    from λ n, real.bcsupr_nonneg (λ _ _, dist_nonneg),
  simp only [dist_zero_right, real.norm_eq_abs, abs_of_nonneg, nonneg],
  intros ε ε_pos,
  apply ((𝓝 t).has_basis_small_sets.tendsto_right_iff.mp hs _ $
         metric.tendsto_nhds.mp h (ε/2) (half_pos ε_pos)).mono (λ n hn, _),
  apply lt_of_le_of_lt _ (half_lt_self ε_pos),
  exact real.bcsupr_le (half_pos ε_pos).le (λ x hx, (hn hx).out.le),
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

section
open filter

lemma mem_closure_inter_of_mem_nhds_of_mem_closure {X : Type*} [topological_space X] {x : X}
  {u v : set X} (hu : u ∈ 𝓝 x) (hv : x ∈ closure v) : x ∈ closure (u ∩ v) :=
begin
  rcases mem_nhds_iff.mp hu with ⟨w, w_sub, w_op, hw⟩,
  exact closure_mono (v.inter_subset_inter_left w_sub) (closure_inter_open w_op ⟨hw, hv⟩)
end

lemma continuous.symm {X Y : Type*} [topological_space X]
  [topological_space Y] [locally_compact_space Y] [t2_space Y]
  {f : X ≃ Y} (hf : continuous f) (hf' : ∀ K, is_compact K → is_compact (f ⁻¹' K)) :
  continuous f.symm :=
begin
  rw continuous_iff_is_closed,
  intros F hF,
  rw ← f.image_eq_preimage,
  apply is_closed_of_closure_subset,
  intros y hy,
  obtain ⟨K, K_cpct, K_in⟩ := exists_compact_mem_nhds y,
  have hy' : y ∈ closure (K ∩ f '' F),
  { exact mem_closure_inter_of_mem_nhds_of_mem_closure K_in hy },
  have : K ∩ f '' F = f '' (f ⁻¹' K ∩ F),
  { rw ← set.image_inter (f.injective),
    rw f.image_preimage },
  have : is_compact (K ∩ f '' F),
  { rw this,
    apply is_compact.image _ hf,
    specialize hf' K K_cpct,
    exact hf'.inter_right hF },
  have := this.is_closed,
  rw this.closure_eq at hy',
  exact hy'.2
end

lemma continuous_parametric_symm {X Y Z : Type*} [topological_space X]
  [t2_space X] [locally_compact_space X]
  [topological_space Y] [t2_space Y]
  [topological_space Z] [t2_space Z] [locally_compact_space Z]
  {f : X → Y ≃ Z}
  (hf : continuous (λ p : X × Y, f p.1 p.2))
  (hf' : ∀ K, is_compact K → is_compact ((λ p : X × Y, (p.1, f p.1 p.2)) ⁻¹' K)) :
  continuous (λ p : X × Z, (f p.1).symm p.2) :=
begin
  let φ₀ : (X × Y) ≃ (X × Z) :=
  { to_fun := λ p : X × Y, (p.1, f p.1 p.2),
    inv_fun := λ p : X × Z, (p.1, (f p.1).symm p.2),
    left_inv := λ x, by simp,
    right_inv := λ x, by simp },
  have φ₀_cont : continuous φ₀, from continuous_fst.prod_mk hf,
  exact continuous_snd.comp (φ₀_cont.symm hf')
end

end

section continuous_linear

-- two lemmas about continuous bilinear maps, not that useful
variables {X 𝕜 E E' F : Type*}
variables [nondiscrete_normed_field 𝕜]
  [normed_group E] [normed_group E'] [normed_group F]
  [normed_space 𝕜 E] [normed_space 𝕜 E'] [normed_space 𝕜 F]

namespace continuous_linear_map

lemma has_fderiv_at_const_left [normed_group X] [normed_space 𝕜 X]
  (L : E →L[𝕜] E' →L[𝕜] F) {f : X → E'} {f' : X →L[𝕜] E'}
  (x : X) {c : E} (hf : has_fderiv_at f f' x) : has_fderiv_at (λ x, L c (f x)) ((L c).comp f') x :=
(L c).has_fderiv_at.comp x hf

lemma has_fderiv_at_const_right [normed_group X] [normed_space 𝕜 X]
  (L : E →L[𝕜] E' →L[𝕜] F) {f : X → E} {f' : X →L[𝕜] E}
  (x : X) {c : E'}
  (hf : has_fderiv_at f f' x) : has_fderiv_at (λ x, L (f x) c) ((flip L c).comp f') x :=
(flip L).has_fderiv_at_const_left x hf

end continuous_linear_map

-- (unused)
@[simp] lemma continuous_linear_equiv.coe_one : (⇑(1 : E ≃L[𝕜] E) : E → E) = id := rfl

-- (unused)
@[simp] lemma continuous_linear_equiv.one_symm : (1 : E ≃L[𝕜] E).symm = 1 := rfl

end continuous_linear
