import to_mathlib.partition
import to_mathlib.unused.cont_mdiff

open_locale topological_space filter manifold
open topological_space filter

variables
  {E : Type*} [normed_add_comm_group E] [normed_space ℝ E] [finite_dimensional ℝ E]
  {F : Type*} [normed_add_comm_group F] [normed_space ℝ F]


universes uH uM

variables {H : Type uH} [topological_space H] (I : model_with_corners ℝ E H)
  {M : Type uM} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
  [sigma_compact_space M] [t2_space M]

lemma exists_cont_diff_of_convex_of_is_open {s : set E} (hs : is_open s)
  {P : E → F → Prop} (hP : ∀ x ∈ s, convex ℝ {y | P x y})
  {n : ℕ∞}
  (hP' : ∀ x ∈ s, ∃ U ∈ 𝓝 x, ∃ f : E → F, cont_diff_on ℝ n f U ∧ ∀ x ∈ U, P x (f x)) :
  ∃ f : E → F, cont_diff_on ℝ n f s ∧ ∀ x ∈ s, P x (f x) :=
begin
  classical,
  let S : opens E := ⟨s, hs⟩,
  suffices : ∃ f : S → F, cont_mdiff 𝓘(ℝ, E) 𝓘(ℝ, F) n f ∧ ∀ (x : ↥S), P x (f x),
  { rcases this with ⟨f, hf, hf'⟩,
    refine ⟨λ x, if hx : x ∈ s then f ⟨x, hx⟩ else 0, cont_mdiff_iff_cont_diff_on'.mp hf, _⟩,
    intros x hx,
    rw dif_pos hx,
    exact hf' ⟨x, hx⟩ },
  let PS : S → F → Prop := λ s y, P s y,
  change ∃ f : S → F, cont_mdiff 𝓘(ℝ, E) 𝓘(ℝ, F) n f ∧ ∀ (x : ↥S), PS x (f x),
  haveI : locally_compact_space S := hs.locally_compact_space,
  haveI : t2_space S := subtype.t2_space,
  apply exists_cont_mdiff_of_convex,
  { rintros ⟨x, hx⟩,
    exact hP x hx },
  { rintros ⟨x, hx : x ∈ S⟩,
    rcases hP' x hx with ⟨U, U_in, f, hf, hf'⟩,
    refine ⟨coe ⁻¹' U, _, f ∘ coe, _, _⟩,
    { rw nhds_subtype_eq_comap,
      exact preimage_mem_comap U_in },
    { rw cont_mdiff_on_iff_cont_diff_on',
      exact hf.mono (s.inter_subset_right U) },
    { rintros ⟨x, hx : x ∈ s⟩ (hx' : x ∈ U),
      exact hf' x hx' } }
end
