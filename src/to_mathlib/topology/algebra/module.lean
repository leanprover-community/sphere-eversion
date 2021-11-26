import analysis.convex.topology
import linear_algebra.affine_space.affine_map

open affine_map

open_locale affine convex

variables {𝕂 E F : Type*} 

lemma continuous_line_map [ring 𝕂] [topological_space 𝕂] [topological_ring 𝕂]
  [add_comm_group E] [topological_space E] [topological_add_group E] 
  [module 𝕂 E] [has_continuous_smul 𝕂 E]
  (a b : E) : 
  continuous (line_map a b : 𝕂 → E) := 
begin
  change continuous (λ x, line_map a b x),
  conv {congr, funext, rw line_map_apply_module},
  continuity
end

section real_topological_vector_space

variables [add_comm_group E] [module ℝ E]

lemma segment_eq_image_line_map (a b : E) : 
  [a -[ℝ] b] = line_map a b '' unit_interval :=
begin
  convert segment_eq_image ℝ a b,
  ext,
  exact line_map_apply_module _ _ _
end

lemma convex.is_path_connected' [topological_space E] [topological_add_group E] 
  [has_continuous_smul ℝ E] {s : set E} 
  (hconv : convex ℝ s) (hne : s.nonempty) :
  is_path_connected s :=
begin
  refine is_path_connected_iff.mpr ⟨hne, _⟩,
  intros x y x_in y_in,
  have H := hconv.segment_subset x_in y_in,
  rw segment_eq_image_line_map at H,
  exact joined_in.of_line (continuous_line_map x y).continuous_on (line_map_apply_zero _ _) 
    (line_map_apply_one _ _) H
end

end real_topological_vector_space
