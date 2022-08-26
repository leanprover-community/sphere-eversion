import geometry.manifold.cont_mdiff

open topological_space structure_groupoid.local_invariant_prop

section
variables {H : Type*} {M : Type*} [topological_space H] [topological_space M] [charted_space H M]
{H' : Type*} {M' : Type*} [topological_space H'] [topological_space M'] [charted_space H' M']

variables {G : structure_groupoid H} {G' : structure_groupoid H'}
{P : (H → H') → set H → H → Prop} (hG : G.local_invariant_prop G' P)

include hG

lemma lift_prop_comp_coe {s : opens M}  {f : M → M'} :
  lift_prop P (f ∘ (coe : s → M)) ↔ lift_prop_on P f s :=
sorry

lemma lift_prop_opens [inhabited M'] {s : opens M} [decidable_pred (λ x, x ∈ s)]
  {f : s → M'} :
  lift_prop P f ↔ lift_prop_on P (λ x : M, if hx : x ∈ s then f ⟨x, hx⟩ else default) s :=
sorry

lemma lift_prop_on_comp_coe {s : opens M} {t : set M} {f : M → M'} :
  lift_prop_on P (f ∘ (coe : s → M)) (coe ⁻¹' t) ↔ lift_prop_on P f (s ∩ t) :=
sorry
end

section
noncomputable theory
universes uM uH

open_locale topological_space filter manifold
open filter topological_space function set

variables
  {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
  {F : Type*} [normed_add_comm_group F] [normed_space ℝ F]

lemma cont_mdiff_iff_cont_diff_on {s : opens E}  {f : E → F} {n : ℕ∞} :
  cont_mdiff 𝓘(ℝ, E) 𝓘(ℝ, F) n (f ∘ (coe : s → E)) ↔ cont_diff_on ℝ n f s :=
begin
  rw ← cont_mdiff_on_iff_cont_diff_on,
  have key := lift_prop_comp_coe (cont_diff_within_at_local_invariant_prop 𝓘(ℝ, E) 𝓘(ℝ, F) n),
  exact ⟨λ h x x_in,key.mp h x x_in, λ h x, key.mpr h x⟩
end

lemma cont_mdiff_iff_cont_diff_on' {s : opens E} [decidable_pred (λ x, x ∈ s)]
  {f : s → F} {n : ℕ∞} :
  cont_mdiff 𝓘(ℝ, E) 𝓘(ℝ, F) n f ↔ cont_diff_on ℝ n (λ x : E, if hx : x ∈ s then f ⟨x, hx⟩ else 0) s :=
begin
  rw ← cont_mdiff_on_iff_cont_diff_on,
  letI : inhabited F := ⟨0⟩,
  have key := lift_prop_opens (cont_diff_within_at_local_invariant_prop 𝓘(ℝ, E) 𝓘(ℝ, F) n),
  exact ⟨λ h x x_in, key.mp h x x_in, λ h x, key.mpr h x⟩
end

lemma cont_mdiff_on_iff_cont_diff_on' {s : opens E} {t : set E} {f : E → F} {n : ℕ∞} :
  cont_mdiff_on 𝓘(ℝ, E) 𝓘(ℝ, F) n (f ∘ (coe : s → E)) (coe ⁻¹' t) ↔ cont_diff_on ℝ n f (s ∩ t) :=
begin
  rw ← cont_mdiff_on_iff_cont_diff_on,
  have key := lift_prop_on_comp_coe (cont_diff_within_at_local_invariant_prop 𝓘(ℝ, E) 𝓘(ℝ, F) n),
  exact ⟨λ h x x_in, key.mp h x x_in, λ h x, key.mpr h x⟩
end
end
