import loops.reparametrization

import local.corrugation
import local.relation

/-!
# Local h-principle for open and ample relations

This file proves lem:h_principle_open_ample_loc
-/

noncomputable theory

open_locale unit_interval classical filter topological_space
open filter set rel_loc

-- `∀ᶠ x near s, p x` means property `p` holds at every point in a neighborhood of the set `s`.
local notation `∀ᶠ` binders ` near ` s `, ` r:(scoped p, filter.eventually p $ 𝓝ˢ s) := r

local notation `D` := fderiv ℝ
local notation `hull` := convex_hull ℝ

variables (E : Type*) [normed_group E] [normed_space ℝ E] [finite_dimensional ℝ E]
          {F : Type*} [normed_group F] [normed_space ℝ F] [measurable_space F] [borel_space F]
          [finite_dimensional ℝ F]

open_locale unit_interval
/--
The setup for local h-principle is three nested subsets `K₀ ⊆ K₁ ⊆ U` with `U` open,
`K₀` and `K₁` compact, `K₀ ⊆ interior K₁` and a closed subset `C`.
-/
structure landscape :=
(U C K₀ K₁ : set E)
(hU : is_open U)
(hC : is_closed C)
(hK₀ : is_compact K₀)
(hK₁ : is_compact K₁)
(h₀₁ : K₀ ⊆ interior K₁)
(hK₁U : K₁ ⊆ U)

section improve_step
/-!
## Improvement step

This section proves lem:integration_step.
-/

/--
The setup for a one-step improvement towards a local h-principle is three nested subsets
`K₀ ⊆ K₁ ⊆ U` with `U` open, `K₀` and `K₁` compact, `K₀ ⊆ interior K₁` and a closed subset `C`
together with a dual pair `p` and a subspace `E'` of the corresponding hyperplane `ker p.π`.
-/
structure step_landscape extends landscape E :=
(E' : submodule ℝ E)
(p : dual_pair' E)
(hEp : E' ≤ p.π.ker)

variables {E}

open_locale classical

variables {R : rel_loc E F} {U : set E}

/-- A one-step improvement landscape accepts a formal solution if it can improve it. -/
structure step_landscape.accepts (L : step_landscape E) (𝓕 : formal_sol R U) : Prop :=
(h_op : R.is_open_over L.U)
(hK₀ : ∀ᶠ x near L.K₀, 𝓕.is_part_holonomic_at L.E' x)
(h_short : ∀ x ∈ L.U, 𝓕.is_short_at L.p x)
(hC : ∀ᶠ x near L.C, 𝓕.is_holonomic_at x)

def step_landscape.Ω (L : step_landscape E) (𝓕 : formal_sol R L.U) : set (E × F) :=
⋃ x ∈ L.U, ({x} : set E) ×ˢ (connected_comp_in (𝓕.slice_at L.p x) $ 𝓕.φ x L.p.v)

def step_landscape.K (L : step_landscape E) : set E := L.K₁ ∩ L.C

def step_landscape.b (L : step_landscape E) (𝓕 : formal_sol R L.U) : E → F := λ x, 𝓕.φ x L.p.v

def step_landscape.g (L : step_landscape E) (𝓕 : formal_sol R L.U) : E → F := λ x, D 𝓕.f x L.p.v

lemma step_landscape.is_compact_K (L : step_landscape E) : is_compact L.K :=
L.hK₁.inter_right L.hC

lemma step_landscape.hKU (L : step_landscape E) : L.K ⊆ L.U :=
((inter_subset_left _ _).trans L.hK₁U)


lemma step_landscape.accepts.open {L : step_landscape E} {𝓕 : formal_sol R L.U} (h : L.accepts 𝓕) :
  is_open (L.Ω 𝓕 ∩ (L.U ×ˢ (univ : set F))) :=
sorry

lemma step_landscape.accepts.connected {L : step_landscape E} {𝓕 : formal_sol R L.U} (h : L.accepts 𝓕) :
  ∀ x ∈ L.U, is_connected (prod.mk x ⁻¹' (L.Ω 𝓕)) :=
begin

  sorry
end

lemma step_landscape.accepts.smooth_b {L : step_landscape E} {𝓕 : formal_sol R L.U} (h : L.accepts 𝓕) :
  ∀ x ∈ L.U, smooth_at (L.b 𝓕) x :=
sorry

lemma step_landscape.accepts.smooth_g {L : step_landscape E} {𝓕 : formal_sol R L.U} (h : L.accepts 𝓕) :
  ∀ x ∈ L.U, smooth_at (L.g 𝓕) x :=
sorry

lemma step_landscape.accepts.mem {L : step_landscape E} {𝓕 : formal_sol R L.U} (h : L.accepts 𝓕) :
  ∀ x ∈ L.U, (x, L.b 𝓕 x) ∈ L.Ω 𝓕 :=
sorry

lemma step_landscape.accepts.rel {L : step_landscape E} {𝓕 : formal_sol R L.U} (h : L.accepts 𝓕) :
  ∀ᶠ (x : E) near L.K, (L.g 𝓕) x = (L.b 𝓕) x :=
sorry

lemma step_landscape.accepts.hull {L : step_landscape E} {𝓕 : formal_sol R L.U} (h : L.accepts 𝓕) :
  ∀ x ∈ L.U, L.g 𝓕 x ∈ hull (prod.mk x ⁻¹' L.Ω 𝓕) :=
sorry

def step_landscape.loop (L : step_landscape E) {𝓕 : formal_sol R L.U} (h : L.accepts 𝓕) :
E → ℝ → loop F :=
classical.some (exists_loops L.hU L.is_compact_K L.hKU h.open h.connected h.smooth_g h.smooth_b h.mem h.rel h.hull)

variables {L : step_landscape E}

/--
Homotopy of formal solutions obtained by corrugation in the direction of `p : dual_pair' E`
in some landscape to improve a formal solution `𝓕` from being `L.E'`-holonomic to
`L.E' ⊔ span {p.v}`-holonomic near `L.K₀`.
-/
def rel_loc.formal_sol.improve_step (𝓕 : formal_sol R L.U) (ε : ℝ) : htpy_formal_sol R L.U :=
if h : L.accepts 𝓕 ∧ 0 < ε
then
  sorry
else
  𝓕.const_htpy

namespace rel_loc.formal_sol

variables (𝓕 : formal_sol R L.U) (ε : ℝ)

lemma improve_step_rel_t_eq_0 : 𝓕.improve_step ε 0 = 𝓕 :=
sorry

lemma improve_step_rel_C : ∀ᶠ x near L.C, ∀ t, 𝓕.improve_step ε t x = 𝓕 x :=
sorry

lemma improve_step_rel_compl_K₁ : ∀ x ∉ L.K₁, ∀ t, 𝓕.improve_step ε t x = 𝓕 x :=
sorry

variables {ε}

lemma improve_step_c0_close (ε_pos : 0 < ε) : ∀ x t, ∥𝓕.improve_step ε t x - 𝓕 x∥ ≤ ε :=
sorry


lemma improve_step_hol
  (h_op : R.is_open_over L.U)
  (h_part_hol : ∀ᶠ x near L.K₀, 𝓕.is_part_holonomic_at L.E' x)
  (h_short : ∀ x ∈ L.U, 𝓕.is_short_at L.p x)
  (h_hol : ∀ᶠ x near L.C, 𝓕.is_holonomic_at x)
  (ε_pos : 0 < ε) :
  ∀ᶠ x near L.K₀, (𝓕.improve_step ε 1).is_part_holonomic_at (L.E' ⊔ L.p.span_v) x :=
sorry

end rel_loc.formal_sol

end improve_step

section improve
/-!
## Full improvement

This section proves lem:h_principle_open_ample_loc.
-/

variables {E}

/--
Homotopy of formal solutions obtained by successive corrugations in some landscape `L` to improve a
formal solution `𝓕` until it becomes holonomic near `L.K₀`.
-/
def rel_loc.formal_sol.improve {R : rel_loc E F} {L : landscape E} (𝓕 : formal_sol R L.U) (ε : ℝ) :
  htpy_formal_sol R L.U :=
if h : R.is_open_over L.U ∧
       R.is_ample ∧
       (∀ᶠ x near L.C, 𝓕.is_holonomic_at x) ∧
       0 < ε
then
  sorry
else
  𝓕.const_htpy

namespace rel_loc.formal_sol
variables {L : landscape E} {R : rel_loc E F} (𝓕 : formal_sol R L.U) (ε : ℝ)
  (h_op : R.is_open_over L.U)
  (h_ample : R.is_ample)
  (h_hol : ∀ᶠ x near L.C, 𝓕.is_holonomic_at x)

include h_op h_ample h_hol

lemma improve_rel_t_eq_0 : 𝓕.improve ε 0 = 𝓕 :=
sorry

lemma improve_rel_C : ∀ᶠ x near L.C, ∀ t, 𝓕.improve ε t x = 𝓕 x :=
sorry

lemma improve_rel_compl_K₁ : ∀ x ∉ L.K₁, ∀ t, 𝓕.improve ε t x = 𝓕 x :=
sorry

lemma improve_c0_close {ε : ℝ} (ε_pos : 0 < ε) : ∀ x t, ∥𝓕.improve ε t x - 𝓕 x∥ ≤ ε :=
sorry

lemma improve_hol : ∀ᶠ x near L.K₀, (𝓕.improve ε 1).is_holonomic_at x :=
sorry

end rel_loc.formal_sol
end improve
