import topology.path_connected
import topology.urysohns_lemma
import topology.uniform_space.compact_separated
import linear_algebra.affine_space.independent
import analysis.normed_space.finite_dimension
import topology.algebra.floor_ring
import topology.paracompact
import topology.shrinking_lemma

/-!
Lemmas that are unused in the sphere-eversion project, but were formulated for one reason or another
(because they seemed useful at the time). If the lemmas are still useful, we would still like to
move them to mathlib, but if they aren't that useful after all, we can decide to remove them.

This file should *not* be imported in any other file (and this file can import anything).
-/

open_locale filter unit_interval topological_space uniformity
open function filter

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
