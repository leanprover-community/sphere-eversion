import local.ample_set
import local.dual_pair
import local.relation

variables {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
variables {F : Type*} [normed_add_comm_group F] [normed_space ℝ F]
variables (P : Type*) [normed_add_comm_group P] [normed_space ℝ P]


open set

namespace rel_loc

/-- The slice of a local relation `R : rel_loc E F` for a dual pair `p` at a jet `θ` is
the set of `w` in `F` such that updating `θ` using `p` and `w` leads to a jet in `R`. -/
def slice (R : rel_loc E F) (p : dual_pair' E) (θ : E × F × (E →L[ℝ] F)) : set F :=
{w | (θ.1, θ.2.1, p.update θ.2.2 w) ∈ R}

lemma mem_slice (R : rel_loc E F) {p : dual_pair' E} {θ : E × F × (E →L[ℝ] F)} {w : F} :
  w ∈ R.slice p θ ↔ (θ.1, θ.2.1, p.update θ.2.2 w) ∈ R :=
iff.rfl

/-- A relation is ample if all its slices are ample. -/
def is_ample (R : rel_loc E F) : Prop := ∀ (p : dual_pair' E) (θ : E × F × (E →L[ℝ] F)),
ample_set (R.slice p θ)

/- FIXME: the proof below is awful. -/
lemma is_ample.mem_hull {R : rel_loc E F} (h : is_ample R) {θ : E × F × (E →L[ℝ] F)}
  (hθ : θ ∈ R) (v : F) (p) : v ∈ hull (connected_component_in (R.slice p θ) (θ.2.2 p.v)) :=
begin
  rw h p θ (θ.2.2 p.v) _,
  exact mem_univ _,
  dsimp [rel_loc.slice],
  rw p.update_self,
  cases θ,
  cases θ_snd,
  exact hθ
end

lemma slice_update {R : rel_loc E F} {θ : E × F × (E →L[ℝ] F)}
  {p : dual_pair' E} (x : F) :
  R.slice p (θ.1, θ.2.1, (p.update θ.2.2 x)) = R.slice p θ :=
begin
  ext1 w,
  dsimp [slice],
  rw [p.update_update]
end

/-- In order to check ampleness, it suffices to consider slices through elements of the relation. -/
lemma is_ample_iff {R : rel_loc E F} : R.is_ample ↔
  ∀ ⦃θ : one_jet E F⦄ (p : dual_pair' E), θ ∈ R → ample_set (R.slice p θ) :=
begin
  simp_rw [is_ample],
  refine ⟨λ h θ p hθ, h p θ, λ h p θ w hw, _⟩,
  dsimp [slice] at hw,
  have := h p hw,
  rw [slice_update] at this,
  exact this w hw
end


open_locale pointwise

lemma slice_of_ker_eq_ker {R : rel_loc E F} {θ : one_jet E F}
  {p p' : dual_pair' E} (hpp' : p.π = p'.π) :
  R.slice p θ = θ.2.2 (p.v - p'.v) +ᵥ R.slice p' θ :=
begin
  rcases θ with ⟨x, y, φ⟩,
  have key : ∀ w, p'.update φ w = p.update φ (w + φ (p.v - p'.v)),
  { intros w,
    simp only [dual_pair'.update, hpp', map_sub, add_right_inj],
    congr' 2,
    abel },
  ext w,
  simp only [slice, mem_set_of_eq, map_sub, vadd_eq_add, mem_vadd_set_iff_neg_vadd_mem, key],
  have : -(φ p.v - φ p'.v) + w + (φ p.v - φ p'.v) = w,
  abel,
  rw this,
end

lemma ample_slice_of_ample_slice {R : rel_loc E F} {θ : one_jet E F}
  {p p' : dual_pair' E} (hpp' : p.π = p'.π) (h : ample_set (R.slice p θ)) :
  ample_set (R.slice p' θ) :=
begin
  rw slice_of_ker_eq_ker hpp'.symm,
  exact ample_set.vadd h
end

end rel_loc

open rel_loc

namespace rel_loc.jet_sec

variables  {R : rel_loc E F}

/-- The slice associated to a jet section and a dual pair at some point. -/
def slice_at (𝓕 : jet_sec E F) (R : rel_loc E F) (p : dual_pair' E) (x : E) : set F :=
R.slice p (x, 𝓕.f x, 𝓕.φ x)

/-- The slice associated to a formal solution and a dual pair at some point. -/
def _root_.rel_loc.formal_sol.slice_at (𝓕 : formal_sol R) (p : dual_pair' E) (x : E) : set F :=
R.slice p (x, 𝓕.f x, 𝓕.φ x)

lemma mem_slice (𝓕 : formal_sol R) (p : dual_pair' E) {x : E} :
  𝓕.φ x p.v ∈ 𝓕.slice_at p x :=
by simpa [rel_loc.formal_sol.slice_at, rel_loc.slice] using  𝓕.is_sol x

/-- A formal solution `𝓕` is short for a dual pair `p` at a point `x` if the derivative of
the function `𝓕.f` at `x` is in the convex hull of the relevant connected component of the
corresponding slice. -/
def is_short_at (𝓕 : jet_sec E F) (R : rel_loc E F) (p : dual_pair' E) (x : E) : Prop :=
D 𝓕.f x p.v ∈ hull (connected_component_in (𝓕.slice_at R p x) $ 𝓕.φ x p.v)

def _root_.rel_loc.formal_sol.is_short_at (𝓕 : formal_sol R)(p : dual_pair' E) (x : E) : Prop :=
D 𝓕.f x p.v ∈ hull (connected_component_in (𝓕.slice_at p x) $ 𝓕.φ x p.v)

lemma _root_.rel_loc.is_ample.is_short_at {R : rel_loc E F} (hR : is_ample R) (𝓕 : formal_sol R) (p : dual_pair' E)
  (x : E) : 𝓕.is_short_at p x :=
hR.mem_hull (𝓕.is_sol x) _ p


end rel_loc.jet_sec
