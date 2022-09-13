import analysis.calculus.cont_diff
import linear_algebra.dual

import notations
import to_mathlib.analysis.normed_space.operator_norm
import to_mathlib.analysis.calculus
import to_mathlib.linear_algebra.basic

/-! # Dual pairs

Convex integration improves maps by successively modify their derivative in a direction of a
vector field (almost) without changing their derivative along some complementary hyperplace.

In this file we introduce the linear algebra part of the story of such modifications.
The main gadget here are dual pairs on a real topological vector space `E`.
Each `p : dual_pair E` is made of a (continuous) linear form `p.π : E →L[ℝ] ℝ` and a vector
`p.v : E` such that `p.π p.v = 1`.

Those pairs are used to build the updating operation turning `φ : E →L[ℝ] F` into
`p.update φ w` which equals `φ` on `ker p.π` and sends `v` to the given `w : F`.

After formalizing the above definitions, we first record a number of trivial algebraic lemmas.
Then we prove a lemma which is geometrically obvious but not so easy to formalize:
`injective_update_iff` states, starting with an injective `φ`, that the updated
map `p.update φ w` is injective if and only if `w` isn't in the image of `ker p.π` under `φ`.
This is crucial in order to apply convex integration to immersions.

Then we prove continuity and smoothness lemmas for this operation.
-/


noncomputable theory

open function continuous_linear_map

/-! ## General theory -/

section no_norm
variables (E : Type*) {E' F G : Type*}
variables [add_comm_group E] [module ℝ E] [topological_space E]
variables [add_comm_group E'] [module ℝ E'] [topological_space E']
variables [normed_add_comm_group F] [normed_space ℝ F] [normed_add_comm_group G] [normed_space ℝ G]

-- TODO: move mathlib's dual_pair out of the root namespace!

/-- A continuous linear form `π` and a vector `v` that pair to one. In particular `ker π` is a
hyperplane and `v` spans a complement of this hyperplane. -/
structure dual_pair :=
(π : E →L[ℝ] ℝ)
(v : E)
(pairing : π v = 1)

namespace dual_pair
variables {E F}

local attribute [simp] continuous_linear_map.to_span_singleton_apply

lemma ker_pi_ne_top (p : dual_pair E) : p.π.ker ≠ ⊤ :=
begin
  intro H,
  have : (p.π : E →ₗ[ℝ] ℝ) p.v = 1 := p.pairing,
  simpa [linear_map.ker_eq_top.mp H]
end

lemma pi_ne_zero (p : dual_pair E) : p.π ≠ 0 :=
begin
  intro H,
  simpa [H] using p.pairing
end

lemma v_ne_zero (p : dual_pair E) : p.v ≠ 0 :=
begin
  intro H,
  simpa [H] using p.pairing
end

/-- Given a dual pair `p`, `p.span_v` is the line spanned by `p.v`. -/
def span_v (p : dual_pair E) : submodule ℝ E := submodule.span ℝ {p.v}

lemma mem_span_v (p : dual_pair E) {u : E} : u ∈ p.span_v ↔ ∃ t : ℝ, u = t • p.v :=
by simp [dual_pair.span_v, submodule.mem_span_singleton, eq_comm]

/-- Update a continuous linear map `φ : E →L[ℝ] F` using a dual pair `p` on `E` and a
vector `w : F`. The new map coincides with `φ` on `ker p.π` and sends `p.v` to `w`. -/
def update (p : dual_pair E) (φ : E →L[ℝ] F) (w : F) : E →L[ℝ] F :=
φ + (w - φ p.v) ⬝ p.π

@[simp]
lemma update_ker_pi (p : dual_pair E) (φ : E →L[ℝ] F) (w : F) {u} (hu : u ∈ p.π.ker) :
  p.update φ w u = φ u :=
begin
  rw continuous_linear_map.mem_ker at hu,
  simp only [update, hu, continuous_linear_map.to_span_singleton_apply, add_zero,
             continuous_linear_map.coe_comp', comp_app, zero_smul, continuous_linear_map.add_apply]
end

@[simp]
lemma update_v (p : dual_pair E) (φ : E →L[ℝ] F) (w : F) :
  p.update φ w p.v = w :=
by simp only [update, p.pairing, continuous_linear_map.to_span_singleton_apply,
              continuous_linear_map.coe_comp', add_sub_cancel'_right, one_smul, comp_app,
              continuous_linear_map.add_apply]

@[simp]
lemma update_self (p : dual_pair E) (φ : E →L[ℝ] F)  :
  p.update φ (φ p.v) = φ :=
by simp only [update, add_zero, continuous_linear_map.to_span_singleton_zero,
              continuous_linear_map.zero_comp, sub_self]

@[simp]
lemma update_update (p : dual_pair E) (φ : E →L[ℝ] F) (w w' : F) :
  p.update (p.update φ w') w = p.update φ w :=
by simp_rw [update, add_apply, coe_comp', comp_app, to_span_singleton_apply, p.pairing,
  one_smul, add_sub_cancel'_right, add_assoc, ← continuous_linear_map.add_comp,
  ← to_span_singleton_add, sub_add_eq_add_sub, add_sub_cancel'_right]

lemma inf_eq_bot (p : dual_pair E) : p.π.ker ⊓ p.span_v = ⊥ :=
begin
  rw eq_bot_iff,
  intros x hx,
  have : p.π x = 0 ∧ ∃ a : ℝ, a • p.v = x,
    by simpa [dual_pair.span_v, submodule.mem_span_singleton] using hx,
  rcases this with ⟨H, t, rfl⟩,
  rw [p.π.map_smul, p.pairing, algebra.id.smul_eq_mul, mul_one] at H,
  simp [H]
end

lemma sup_eq_top (p : dual_pair E) : p.π.ker ⊔ p.span_v = ⊤ :=
begin
  rw submodule.sup_eq_top_iff,
  intro x,
  refine ⟨x - p.π x • p.v, _, p.π x • p.v, _, _⟩;
  simp [dual_pair.span_v, submodule.mem_span_singleton, p.pairing]
end

lemma decomp (p : dual_pair E) (e : E) : ∃ u ∈ p.π.ker, ∃ t : ℝ, e = u + t•p.v :=
begin
  have : e ∈ p.π.ker ⊔ p.span_v,
  { rw p.sup_eq_top,
    exact submodule.mem_top },
  simp_rw [submodule.mem_sup, dual_pair.mem_span_v] at this,
  rcases this with ⟨u, hu, -, ⟨t, rfl⟩, rfl⟩,
  use [u, hu, t, rfl]
end

-- useful with `dual_pair.decomp`
lemma update_apply (p : dual_pair E) (φ : E →L[ℝ] F) {w : F} {t : ℝ} {u} (hu : u ∈ p.π.ker) :
  p.update φ w (u + t • p.v) = φ u + t • w :=
by rw [map_add, map_smul, p.update_v, p.update_ker_pi _ _ hu]


/-- Map a dual pair under a linear equivalence. -/
@[simps] def map (p : dual_pair E) (L : E ≃L[ℝ] E') : dual_pair E' :=
⟨p.π ∘L ↑L.symm, L p.v, (congr_arg p.π $ L.symm_apply_apply p.v).trans p.pairing⟩

lemma update_comp_left (p : dual_pair E) (ψ : F →L[ℝ] G) (φ : E →L[ℝ] F) (w : F) :
  p.update (ψ ∘L φ) (ψ w) = ψ ∘L p.update φ w :=
begin
  ext1 u,
  simp only [update, add_apply, continuous_linear_map.comp_apply, to_span_singleton_apply,
    ψ.map_add, ψ.map_smul, ψ.map_sub],
end

lemma update_comp_right (p : dual_pair E) (ψ : E' →L[ℝ] F) (φ : E ≃L[ℝ] E') (w : F) :
  p.update (ψ ∘L ↑φ) w = (p.map φ).update ψ w ∘L ↑φ :=
begin
  ext1 u,
  simp only [update, add_apply, continuous_linear_map.comp_apply, to_span_singleton_apply, map,
    continuous_linear_equiv.coe_coe, φ.symm_apply_apply],
end

lemma map_update_comp_right (p : dual_pair E) (ψ : E →L[ℝ] F) (φ : E ≃L[ℝ] E') (w : F) :
  (p.map φ).update (ψ ∘L ↑φ.symm) w = p.update ψ w ∘L ↑φ.symm :=
begin
  -- todo: use `update_comp_right`
  ext1 u,
  simp only [update, add_apply, continuous_linear_map.comp_apply, to_span_singleton_apply, map,
    continuous_linear_equiv.coe_coe, φ.symm_apply_apply],
end

/-! ## Injectivity criterion -/

@[simp] lemma injective_update_iff
  (p : dual_pair E) {φ : E →L[ℝ] F} (hφ : injective φ) {w : F} :
  injective (p.update φ w) ↔ w ∉ p.π.ker.map φ :=
begin
  change injective (p.update φ w) ↔ w ∉ φ '' p.π.ker,
  split,
  { rintros h ⟨u, hu, rfl⟩,
    have : p.update φ (φ u) p.v = φ u,
    exact p.update_v φ (φ u),
    conv_rhs at this { rw ←  p.update_ker_pi φ (φ u) hu },
    rw ← h this at hu,
    simp only [set_like.mem_coe, continuous_linear_map.mem_ker] at hu,
    rw p.pairing at hu,
    linarith },
  { intros h u u' huu',
    rcases p.decomp u with ⟨a, ha, t, rfl⟩,
    rcases p.decomp u' with ⟨a', ha', t', rfl⟩,
    suffices : (t - t') • p.v = a' - a,
    { rw [sub_smul] at this,
      rw eq_add_of_sub_eq' this,
      abel },
    have : φ a + t • w = φ a' + t' • w,
      by simpa only [(p.update φ w).map_add, ha, ha', update_ker_pi, update_v,
        continuous_linear_map.map_smul] using huu',
    have hw : (t -t') • w = φ (a' - a),
    { rw [sub_smul, φ.map_sub],
      rw eq_sub_of_add_eq this,
      abel },
    have haa' : a' - a ∈ p.π.ker := p.π.ker.sub_mem ha' ha,
    have ht : t - t' = 0,
    { by_contra' ht,
      apply h,
      refine ⟨(t - t')⁻¹ • (a' - a), p.π.ker.smul_mem _ haa', _⟩,
      have := congr_arg (λ u : F, (t - t')⁻¹ • u) hw,
      simp only [ht, inv_smul_smul₀, ne.def, not_false_iff, map_sub] at this,
      rwa [← φ.map_sub, ← φ.map_smul, eq_comm] at this },
    rw [eq_comm, ht, zero_smul] at hw ⊢,
    rw ← φ.map_zero at hw,
    exact hφ hw }
end

end dual_pair
end no_norm

/-! ## Smoothness and continuity -/

namespace dual_pair
variables {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
          {F : Type*} [normed_add_comm_group F] [normed_space ℝ F]


/- In the next two lemmas, finite dimensionality of `E` is clearly uneeded, but allows
to use `cont_diff_clm_apply` and `continuous_clm_apply`. -/

lemma smooth_update [finite_dimensional ℝ E] (p : dual_pair E)
  {G : Type*} [normed_add_comm_group G] [normed_space ℝ G]
  {φ : G → (E →L[ℝ] F)} (hφ : 𝒞 ∞ φ) {w : G → F} (hw : 𝒞 ∞ w) :
  𝒞 ∞ (λ g, p.update (φ g) (w g)) :=
begin
  apply hφ.add,
  rw cont_diff_clm_apply,
  intro y,
  exact (hw.sub (cont_diff_clm_apply.mp hφ p.v)).const_smul _,
end

lemma continuous_update [finite_dimensional ℝ E] (p : dual_pair E)
  {X : Type*} [topological_space X]
  {φ : X → (E →L[ℝ] F)} (hφ : continuous φ) {w : X → F} (hw : continuous w) :
  continuous (λ g, p.update (φ g) (w g)) :=
begin
  apply hφ.add,
  rw continuous_clm_apply,
  intro y,
  exact (hw.sub (continuous_clm_apply.mp hφ p.v)).const_smul _
end

end dual_pair

variables {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
          {F : Type*} [normed_add_comm_group F] [normed_space ℝ F]

/-- Given a finite basis `e : basis ι ℝ E`, and `i : ι`, `e.dual_pair i`
is given by the `i`th basis element and its dual. -/
def basis.dual_pair [finite_dimensional ℝ E] {ι : Type*} [fintype ι] [decidable_eq ι]
  (e : basis ι ℝ E) (i : ι) : dual_pair E :=
{ π := (e.dual_basis i).to_continuous_linear_map,
  v := e i,
  pairing := by simp only [basis.coord_apply, finsupp.single_eq_same, basis.repr_self,
                           linear_map.coe_to_continuous_linear_map', basis.coe_dual_basis] }
