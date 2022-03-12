import analysis.calculus.cont_diff
import linear_algebra.dual

import notations
import to_mathlib.analysis.normed_space.operator_norm
import to_mathlib.analysis.calculus



noncomputable theory

open function

variables (E : Type*) [normed_group E] [normed_space ℝ E] (F : Type*)
                        [normed_group F] [normed_space ℝ F]

-- TODO: move mathlib's dual_pair out of the root namespace!

/-- A continuous linear form `π` and a vector `v` that pair to one. In particular `ker π` is a
hyperplane and `v` spans a complement of this hyperplane. -/
structure dual_pair' :=
(π : E →L[ℝ] ℝ)
(v : E)
(pairing : π v = 1)

namespace dual_pair'
variables {E F}

local attribute [simp] continuous_linear_map.to_span_singleton_apply

lemma ker_pi_ne_top (p : dual_pair' E) : p.π.ker ≠ ⊤ :=
begin
  intro H,
  have : (p.π : E →ₗ[ℝ]  ℝ) p.v = 1 := p.pairing,
  simpa [linear_map.ker_eq_top.mp H]
end

/-- Given a dual pair `p`, `p.span_v` is the line spanned by `p.v`. -/
def span_v (p : dual_pair' E) : submodule ℝ E := submodule.span ℝ {p.v}

/-- Update a continuous linear map `φ : E →L[ℝ] F` using a dual pair `p` on `E` and a
vector `w : F`. The new map coincides with `φ` on `ker p.π` and sends `p.v` to `w`. -/
def update (p : dual_pair' E) (φ : E →L[ℝ] F) (w : F) : E →L[ℝ] F :=
φ + (w - φ p.v) ⬝ p.π

@[simp]
lemma update_ker_pi (p : dual_pair' E) (φ : E →L[ℝ] F) (w : F) {u} (hu : u ∈ p.π.ker) :
  p.update φ w u = φ u :=
begin
  rw continuous_linear_map.mem_ker at hu,
  simp only [update, hu, continuous_linear_map.to_span_singleton_apply, add_zero,
             continuous_linear_map.coe_comp', comp_app, zero_smul, continuous_linear_map.add_apply]
end

@[simp]
lemma update_v (p : dual_pair' E) (φ : E →L[ℝ] F) (w : F) :
  p.update φ w p.v = w :=
by simp only [update, p.pairing, continuous_linear_map.to_span_singleton_apply,
              continuous_linear_map.coe_comp', add_sub_cancel'_right, one_smul, comp_app,
              continuous_linear_map.add_apply]

@[simp]
lemma update_self (p : dual_pair' E) (φ : E →L[ℝ] F)  :
  p.update φ (φ p.v) = φ :=
by simp only [update, add_zero, continuous_linear_map.to_span_singleton_zero,
              continuous_linear_map.zero_comp, sub_self]

-- meant for use in the next lemma
lemma sum_eq_top (p : dual_pair' E) : p.π.ker ⊔ p.span_v = ⊤ :=
begin

  sorry
end

lemma decomp (p : dual_pair' E) (e : E) : ∃ u ∈ p.π.ker, ∃ t : ℝ, e = u + t•p.v :=
begin

  sorry
end

/- In the next two lemmas, finite dimensionality of `E` is clearly uneeded, but allows
to use `cont_diff_clm_apply` and ` continuous_clm_apply`. -/

lemma smooth_update [finite_dimensional ℝ E] (p : dual_pair' E) {G : Type*} [normed_group G] [normed_space ℝ G]
  {φ : G → (E →L[ℝ] F)} (hφ : 𝒞 ∞ φ) {w : G → F} (hw : 𝒞 ∞ w) :
  𝒞 ∞ (λ g, p.update (φ g) (w g)) :=
begin
  apply hφ.add,
  rw cont_diff_clm_apply,
  intro y,
  exact (hw.sub (cont_diff_clm_apply.mp hφ p.v)).const_smul _,
end

lemma continuous_update [finite_dimensional ℝ E] (p : dual_pair' E) {X : Type*} [topological_space X]
  {φ : X → (E →L[ℝ] F)} (hφ : continuous φ) {w : X → F} (hw : continuous w) :
  continuous (λ g, p.update (φ g) (w g)) :=
begin
  apply hφ.add,
  rw continuous_clm_apply,
  intro y,
  exact (hw.sub (continuous_clm_apply.mp hφ p.v)).const_smul _
end

/-- Given a finite basis `e : basis ι ℝ E`, and `i : ι`, `e.dual_pair' i`
is given by the `i`th basis element and its dual. -/
def _root_.basis.dual_pair' [finite_dimensional ℝ E] {ι : Type*} [fintype ι] [decidable_eq ι]
  (e : basis ι ℝ E) (i : ι) : dual_pair' E :=
{ π := (e.dual_basis i).to_continuous_linear_map,
  v := e i,
  pairing := by simp only [basis.coord_apply, finsupp.single_eq_same, basis.repr_self,
                           linear_map.coe_to_continuous_linear_map', basis.coe_dual_basis] }

end dual_pair'
