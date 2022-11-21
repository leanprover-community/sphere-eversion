import local.ample_set
import local.dual_pair
import local.relation

/-! # Slices of first order relations

Recal that a first order partial differential relation for maps between real normed vector spaces
`E` and `F` is a set `R` in `one_jet E F := E × F × (E →L[ℝ] F)`. In this file we study slices
of such relations. The word slice is meant to convey the idea of intersecting with an affine
subspace. Here we fix `(x, y, φ) : one_jet E F` and some hyperplane `H` in `E`. The points
`x` and `y` are fixed and we will take a slice in `E →L[ℝ] F` by intersecting `R` with the affine
subspace of linear maps that coincide with `φ` on `H`.

It will be convenient for convex integration purposes to identify this slice with `F`. There is
no natural identification but we can build one by fixing more data that a hyperplane in `E`.
Namely we fix `p : dual_pair E` (where `ker p.π` is the relevant hyperplane) and reformulate
"linear map that coincides with `φ` on `H`" as `p.update φ w` for some `w : F`.

This `slice` definition allows to define `rel_loc.is_ample`, the ampleness condition for first
order relations: a relation is ample if all its slices are ample sets.

At the end of the file we consider 1-jet sections and slices corresponding to points in their image.
-/

variables {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
variables {F : Type*} [normed_add_comm_group F] [normed_space ℝ F]
variables {X : Type*} [inner_product_space ℝ X]
variables {R : rel_loc E F}
open set

/-! ## Slices and ampleness -/
namespace rel_loc

/-- The slice of a local relation `R : rel_loc E F` for a dual pair `p` at a jet `θ` is
the set of `w` in `F` such that updating `θ` using `p` and `w` leads to a jet in `R`. -/
def slice (R : rel_loc E F) (p : dual_pair E) (θ : E × F × (E →L[ℝ] F)) : set F :=
{w | (θ.1, θ.2.1, p.update θ.2.2 w) ∈ R}

lemma mem_slice (R : rel_loc E F) {p : dual_pair E} {θ : E × F × (E →L[ℝ] F)} {w : F} :
  w ∈ R.slice p θ ↔ (θ.1, θ.2.1, p.update θ.2.2 w) ∈ R :=
iff.rfl

/-- A relation is ample if all its slices are ample. -/
def is_ample (R : rel_loc E F) : Prop := ∀ (p : dual_pair E) (θ : E × F × (E →L[ℝ] F)),
ample_set (R.slice p θ)

lemma is_ample.mem_hull (h : is_ample R) {θ : E × F × (E →L[ℝ] F)}
  (hθ : θ ∈ R) (v : F) (p) : v ∈ hull (connected_component_in (R.slice p θ) (θ.2.2 p.v)) :=
begin
  rw h p θ (θ.2.2 p.v),
  exact mem_univ _,
  rw [mem_slice, p.update_self, prod.mk.eta, prod.mk.eta],
  exact hθ
end

lemma slice_update {θ : E × F × (E →L[ℝ] F)}
  {p : dual_pair E} (x : F) :
  R.slice p (θ.1, θ.2.1, (p.update θ.2.2 x)) = R.slice p θ :=
begin
  ext1 w,
  dsimp [slice],
  rw [p.update_update]
end

/-- In order to check ampleness, it suffices to consider slices through elements of the relation. -/
lemma is_ample_iff : R.is_ample ↔
  ∀ ⦃θ : one_jet E F⦄ (p : dual_pair E), θ ∈ R → ample_set (R.slice p θ) :=
begin
  simp_rw [is_ample],
  refine ⟨λ h θ p hθ, h p θ, λ h p θ w hw, _⟩,
  dsimp [slice] at hw,
  have := h p hw,
  rw [slice_update] at this,
  exact this w hw
end

open_locale pointwise

lemma slice_of_ker_eq_ker {θ : one_jet E F}
  {p p' : dual_pair E} (hpp' : p.π = p'.π) :
  R.slice p θ = θ.2.2 (p.v - p'.v) +ᵥ R.slice p' θ :=
begin
  rcases θ with ⟨x, y, φ⟩,
  have key : ∀ w, p'.update φ w = p.update φ (w + φ (p.v - p'.v)),
  { intros w,
    simp only [dual_pair.update, hpp', map_sub, add_right_inj],
    congr' 2,
    abel },
  ext w,
  simp only [slice, mem_set_of_eq, map_sub, vadd_eq_add, mem_vadd_set_iff_neg_vadd_mem, key],
  have : -(φ p.v - φ p'.v) + w + (φ p.v - φ p'.v) = w,
  abel,
  rw this,
end

lemma ample_slice_of_ample_slice {θ : one_jet E F}
  {p p' : dual_pair E} (hpp' : p.π = p'.π) (h : ample_set (R.slice p θ)) :
  ample_set (R.slice p' θ) :=
begin
  rw slice_of_ker_eq_ker hpp'.symm,
  exact ample_set.vadd h
end

lemma ample_slice_of_forall (R : rel_loc E F) {x y φ} (p : dual_pair E)
  (h : ∀ w, (x, y, p.update φ w) ∈ R) : ample_set (R.slice p (x, y, φ)) :=
begin
  rw show R.slice p (x, y, φ) = univ, from eq_univ_of_forall h,
  exact ample_set_univ
end

end rel_loc

open rel_loc

/-! ## Slices for 1-jet sections and formal solutions. -/

namespace jet_sec

/-- The slice associated to a jet section and a dual pair at some point. -/
def slice_at (𝓕 : jet_sec E F) (R : rel_loc E F) (p : dual_pair E) (x : E) : set F :=
R.slice p (x, 𝓕.f x, 𝓕.φ x)

/-- A 1-jet section `𝓕` is short for a dual pair `p` at a point `x` if the derivative of
the function `𝓕.f` at `x` is in the convex hull of the relevant connected component of the
corresponding slice. -/
def is_short_at (𝓕 : jet_sec E F) (R : rel_loc E F) (p : dual_pair E) (x : E) : Prop :=
D 𝓕.f x p.v ∈ hull (connected_component_in (𝓕.slice_at R p x) $ 𝓕.φ x p.v)

end jet_sec

namespace rel_loc.formal_sol

/-- The slice associated to a formal solution and a dual pair at some point. -/
def slice_at (𝓕 : formal_sol R) (p : dual_pair E) (x : E) : set F :=
R.slice p (x, 𝓕.f x, 𝓕.φ x)

/-- A formal solution `𝓕` is short for a dual pair `p` at a point `x` if the derivative of
the function `𝓕.f` at `x` is in the convex hull of the relevant connected component of the
corresponding slice. -/
def is_short_at (𝓕 : formal_sol R) (p : dual_pair E) (x : E) : Prop :=
D 𝓕.f x p.v ∈ hull (connected_component_in (𝓕.slice_at p x) $ 𝓕.φ x p.v)

end rel_loc.formal_sol

lemma rel_loc.is_ample.is_short_at (hR : is_ample R) (𝓕 : formal_sol R) (p : dual_pair E)
  (x : E) : 𝓕.is_short_at p x :=
hR.mem_hull (𝓕.is_sol x) _ p
