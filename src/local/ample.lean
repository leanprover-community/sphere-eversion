import analysis.convex.basic
import topology.subset_properties
import linear_algebra.dimension
import analysis.normed_space.complemented

/-!
# Ample subsets of real vector spaces

## Implementation notes

The definition of ample subset asks for a vector space structure and a topology on the ambiant type
without any link between those structures, but we will only be using these for finite dimensional
vector spaces with their natural topology.
-/

open set

variables {E : Type*} [add_comm_group E] [vector_space ℝ E] [topological_space E]

/-- A subset of a topological real vector space is ample if the convex hull of each of its
connected components is the full space. -/
def ample_set (s : set E) :=
∀ x : s, convex_hull (subtype.val '' (connected_component x)) = univ

local notation ` I ` := interval (0 : ℝ) 1

def path_connected {E : Type*} [topological_space E] {F : set E} (x y : F) : Prop :=
∃ (f : I → F), continuous f ∧ f ⟨0, left_mem_interval⟩ = x ∧ f ⟨1, right_mem_interval⟩ = y

def path_connected_set {E : Type*} [topological_space E] (F : set E) : Prop :=
∀ (x y : F), path_connected x y

def flip_interval : I → I := λ x,
{ val := 1 - x.1,
  property :=
  begin
    rcases x with ⟨_, _, _⟩,
    norm_num at *,
    split; linarith
  end }

lemma continuous_flip : continuous flip_interval := sorry

lemma path_connected_equivalence {E : Type*} [topological_space E] (F : set E) :
  equivalence (path_connected : F → F → Prop) :=
begin
  classical,
  refine ⟨_, _, _⟩,
  { intro x,
    refine ⟨λ _, x, continuous_const, rfl, rfl⟩ },
  { rintro x y ⟨f, hf, rfl, rfl⟩,
    refine ⟨f ∘ flip_interval, _, _, _⟩,
    apply hf.comp continuous_flip,
    dsimp [flip_interval], simp,
    dsimp [flip_interval], simp },
  sorry
end

open submodule

theorem codim_two_complement_is_pc (F : subspace ℝ E) (cd : 2 ≤ vector_space.dim ℝ F.quotient) :
  path_connected_set (- F.carrier) :=
begin
  obtain ⟨F', compl⟩ := exists_is_compl F,
  have : 2 ≤ vector_space.dim ℝ F',
    rwa ← linear_equiv.dim_eq (quotient_equiv_of_is_compl _ _ compl),
  intros x y,
  let u := ((prod_equiv_of_is_compl _ _ compl).symm x).1,
  let u' := ((prod_equiv_of_is_compl _ _ compl).symm x).2,
  let v := ((prod_equiv_of_is_compl _ _ compl).symm y).1,
  let v' := ((prod_equiv_of_is_compl _ _ compl).symm y).2,
  have : u' ≠ 0,
    intro z,
    rw prod_equiv_of_is_compl_symm_apply_snd_eq_zero at z,
    apply x.2,
    apply z,
  have : v' ≠ 0,
    intro z,
    rw prod_equiv_of_is_compl_symm_apply_snd_eq_zero at z,
    apply y.2,
    apply z,
  have : segment (x : E) (u' : E) ∩ F = ∅,
    sorry,
end


/-- Lemma 2.13: The complement of a linear subspace of codimension at least 2 is ample. -/
theorem ample_codim_two (F : subspace ℝ E) (cd : 2 ≤ vector_space.dim ℝ F.quotient) :
  ample_set (- F.carrier) :=
begin

end