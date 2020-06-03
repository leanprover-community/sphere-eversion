import analysis.convex.basic
import topology.subset_properties

/-!
# Ample subsets of real vector spaces

## Implementation notes

The definition of ample subset asks for a vector space structure and a topology on the ambiant type
without any link between those structures, but we will only be using these for finite dimensional
vector spaces with their natural topology.
-/

open set

variables {F : Type*} [add_comm_group F] [vector_space ℝ F] [topological_space F]

/-- A subset of a topological real vector space is ample if the convex hull of each of its 
connected components is the full space. -/
def ample_set (s : set F) := 
∀ x : s, convex_hull (subtype.val '' (connected_component x)) = univ