import local.h_principle
import global.parametricity_for_free
import interactive_expr
set_option trace.filter_inst_type true

/-!
This is a stop-gap file to prove the parametric local h-principle.
-/
noncomputable theory

open metric finite_dimensional set function rel_loc
open_locale topological_space

section parametric_h_principle


variables {E : Type*} [normed_add_comm_group E] [normed_space ℝ E] [finite_dimensional ℝ E]
          {F : Type*} [normed_add_comm_group F] [normed_space ℝ F] [measurable_space F] [borel_space F]
          [finite_dimensional ℝ F]
          {P : Type*} [normed_add_comm_group P] [normed_space ℝ P]

variables [finite_dimensional ℝ E] [finite_dimensional ℝ F]

variables {R : rel_loc E F} (h_op: is_open R) (h_ample: R.is_ample) (L : landscape E)
variables {ε : ℝ} (ε_pos : 0 < ε)

include h_op h_ample ε_pos

/- not the full local h-principle sphere eversion,
but just a homotopy of solutions from a homotopy of formal solutions
We don't use the `L.C` in the statement, since we want a set in `ℝ`, not in `E`. -/
lemma rel_loc.htpy_formal_sol.exists_sol (𝓕 : R.htpy_formal_sol) (C : set ℝ) (hC : is_closed C)
  (h_hol : ∀ᶠ t near C, ∀ x, (𝓕 t).is_holonomic_at x) :
  ∃ f : ℝ → E → F,
    (𝒞 ∞ $ uncurry f) ∧
    (∀ᶠ t near C, ∀ x, f t x = 𝓕.f t x) ∧
    (∀ x, x ∉ L.K₁ → ∀ t, f t x = 𝓕.f t x) ∧
    (∀ᶠ x near L.K₀, ∀ t, ∥f t x - 𝓕.f t x∥ ≤ ε) ∧
    (∀ᶠ x near L.K₀, ∀ t, (x, f t x, D (f t) x) ∈ R) :=
begin
  sorry
end

end parametric_h_principle
