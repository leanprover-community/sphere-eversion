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
local notation `𝒞` := times_cont_diff ℝ
local notation `∞` := ⊤
local notation `hull` := convex_hull ℝ
local notation u ` ⬝ `:70 φ:65 :=
  continuous_linear_map.comp (continuous_linear_map.to_span_singleton ℝ u) φ


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

namespace step_landscape

/-- A one-step improvement landscape accepts a formal solution if it can improve it. -/
structure accepts (L : step_landscape E) (𝓕 : formal_sol R U) : Prop :=
(h_op : R.is_open_over L.U)
(hK₀ : ∀ᶠ x near L.K₀, 𝓕.is_part_holonomic_at L.E' x)
(h_short : ∀ x ∈ L.U, 𝓕.is_short_at L.p x)
(hC : ∀ᶠ x near L.C, 𝓕.is_holonomic_at x)

def Ω (L : step_landscape E) (𝓕 : formal_sol R L.U) : set (E × F) :=
⋃ x ∈ L.U, ({x} : set E) ×ˢ (connected_comp_in (𝓕.slice_at L.p x) $ 𝓕.φ x L.p.v)

def π (L : step_landscape E) : E →L[ℝ] ℝ := L.p.π

def v (L : step_landscape E) : E := L.p.v

def K (L : step_landscape E) : set E := L.K₁ ∩ L.C

def b (L : step_landscape E) (𝓕 : formal_sol R L.U) : E → F := λ x, 𝓕.φ x L.v

def g (L : step_landscape E) (𝓕 : formal_sol R L.U) : E → F := λ x, D 𝓕.f x L.v

lemma is_compact_K (L : step_landscape E) : is_compact L.K :=
L.hK₁.inter_right L.hC

lemma hKU (L : step_landscape E) : L.K ⊆ L.U :=
((inter_subset_left _ _).trans L.hK₁U)

lemma mem_Ω {L : step_landscape E} {𝓕 : formal_sol R L.U} {x : E} {w : F} (H : (x, w) ∈ L.Ω 𝓕) :
  (x, 𝓕.f x, L.p.update (𝓕.φ x) w) ∈ R :=
begin
  obtain ⟨x, -, h, rfl⟩ : ∃ x', x' ∈ L.U ∧
                                w ∈ connected_comp_in (𝓕.slice_at L.p x') (𝓕.φ x' L.p.v) ∧ x' = x,
  by simpa [step_landscape.Ω] using H,
  exact (connected_comp_in_subset _ _ h : _)
end

lemma accepts.open {L : step_landscape E} {𝓕 : formal_sol R L.U} (h : L.accepts 𝓕) :
  is_open (L.Ω 𝓕 ∩ (L.U ×ˢ (univ : set F))) :=
sorry

lemma accepts.connected {L : step_landscape E} {𝓕 : formal_sol R L.U} (h : L.accepts 𝓕) :
  ∀ x ∈ L.U, is_connected (prod.mk x ⁻¹' (L.Ω 𝓕)) :=
begin

  sorry
end

lemma accepts.smooth_b {L : step_landscape E} {𝓕 : formal_sol R L.U} (h : L.accepts 𝓕) :
  ∀ x ∈ L.U, smooth_at (L.b 𝓕) x :=
sorry

lemma accepts.smooth_g {L : step_landscape E} {𝓕 : formal_sol R L.U} (h : L.accepts 𝓕) :
  ∀ x ∈ L.U, smooth_at (L.g 𝓕) x :=
sorry

lemma accepts.mem {L : step_landscape E} {𝓕 : formal_sol R L.U} (h : L.accepts 𝓕) :
  ∀ x ∈ L.U, (x, L.b 𝓕 x) ∈ L.Ω 𝓕 :=
sorry

lemma accepts.rel {L : step_landscape E} {𝓕 : formal_sol R L.U} (h : L.accepts 𝓕) :
  ∀ᶠ (x : E) near L.K, (L.g 𝓕) x = (L.b 𝓕) x :=
sorry

lemma accepts.hull {L : step_landscape E} {𝓕 : formal_sol R L.U} (h : L.accepts 𝓕) :
  ∀ x ∈ L.U, L.g 𝓕 x ∈ hull (prod.mk x ⁻¹' L.Ω 𝓕) :=
sorry

-- The next lemma uses compactnes of K₁, openness of R above U and continuity of 𝓕
lemma mem_of_c0_close (L : step_landscape E) {𝓕 : formal_sol R L.U}
  (h_op : R.is_open_over L.U) :
  ∃ ε > 0, ∀ (x : E) (z : F) (ψ : E →L[ℝ] F),
           x ∈ L.K₁ → ∥z - 𝓕.f x∥ < ε → ∥ψ - 𝓕.φ x∥ < ε → (x, z, ψ) ∈ R :=
sorry

/-- The loop family to use in some landscape to improve a formal solution. -/
def loop (L : step_landscape E) {𝓕 : formal_sol R L.U} (h : L.accepts 𝓕) :
ℝ → E → loop F :=
classical.some (exists_loops L.hU L.is_compact_K L.hKU h.open h.connected h.smooth_g
                             h.smooth_b h.mem h.rel h.hull)

lemma loop_mem (L : step_landscape E) {𝓕 : formal_sol R L.U} (h : L.accepts 𝓕) :
∀ (x ∈ L.U) t s, L.loop h t x s ∈ (prod.mk x ⁻¹' L.Ω 𝓕) :=
λ x x_in t s,
(((classical.some_spec $ exists_loops L.hU L.is_compact_K L.hKU h.open h.connected h.smooth_g
                             h.smooth_b h.mem h.rel h.hull).2.2.1 x x_in).2.2 t s).1

lemma loop_base (L : step_landscape E) {𝓕 : formal_sol R L.U} (h : L.accepts 𝓕) :
∀ (x ∈ L.U) s, L.loop h 0 x s = L.b 𝓕 x :=
λ x x_in s,
  ((classical.some_spec (exists_loops L.hU L.is_compact_K L.hKU h.open h.connected h.smooth_g
                             h.smooth_b h.mem h.rel h.hull)).2.2.1 x x_in).1 s

lemma loop_smooth (L : step_landscape E) {𝓕 : formal_sol R L.U} (h : L.accepts 𝓕) :
∀ (x ∈ L.U) t s, smooth_at ↿(L.loop h) ((t, x, s) : ℝ × E × ℝ) :=
λ x x_in t s,
(((classical.some_spec $ exists_loops L.hU L.is_compact_K L.hKU h.open h.connected h.smooth_g
                             h.smooth_b h.mem h.rel h.hull).2.2.1 x x_in).2.2 t s).2

lemma loop_avg (L : step_landscape E) {𝓕 : formal_sol R L.U} (h : L.accepts 𝓕) :
 ∀ (x ∈ L.U), (L.loop h 1 x).average = L.g 𝓕 x :=
λ x x_in,
((classical.some_spec $ exists_loops L.hU L.is_compact_K L.hKU h.open h.connected h.smooth_g
                             h.smooth_b h.mem h.rel h.hull).2.2.1 x x_in).2.1


variables (L : step_landscape E)

-- This should be large enough to make everything true
def N (L : step_landscape E) {𝓕 : formal_sol R L.U} {ε : ℝ} (h : L.accepts 𝓕 ∧ 0 < ε) : ℝ :=
sorry

-- Cut-off function which needs to satisfies the next three lemmas
def ρ (L : step_landscape E) : E → ℝ :=
sorry

lemma ρ_smooth (L : step_landscape E) : 𝒞 ∞ L.ρ :=
sorry

lemma hρ₀ (L : step_landscape E) : ∀ᶠ x near L.K₀, L.ρ x = 1 :=
sorry

lemma hρ₁ (L : step_landscape E) : closure {x | L.ρ x ≠ 0} ⊆ L.K₁ :=
sorry

/--
Homotopy of formal solutions obtained by corrugation in the direction of `p : dual_pair' E`
in some landscape to improve a formal solution `𝓕` from being `L.E'`-holonomic to
`L.E' ⊔ span {p.v}`-holonomic near `L.K₀`.
-/
def improve_step (𝓕 : formal_sol R L.U) (ε : ℝ) : htpy_formal_sol R L.U :=
if h : L.accepts 𝓕 ∧ 0 < ε
then
  { f := λ t, 𝓕.f +  corrugation L.π (L.N h) (L.loop h.1 t),
    f_diff := sorry,
    φ := λ t x , L.p.update (𝓕.φ x) (L.loop h.1 (t*L.ρ x) x $ (L.N h) * L.π x) +
                 (t*L.ρ x) • (corrugation.remainder L.p.π (L.N h) (L.loop h.1 1) x),
    φ_diff := sorry,
    is_sol := begin
      intros t x x_in,
      rcases h with ⟨h, ε_pos⟩,
      have := L.loop_mem h x x_in (t*L.ρ x),
      have := step_landscape.mem_Ω (this $ L.N ⟨h, ε_pos⟩ * L.π x),
      dsimp only,
      by_cases h : x ∈ L.K₁,
      { rcases L.mem_of_c0_close _ with ⟨δ, δ_pos, hδ⟩,

        all_goals { sorry } },
      {
        sorry },

      all_goals { sorry },
    end }
else
  𝓕.const_htpy

variables (𝓕 : formal_sol R L.U) (ε : ℝ)

lemma improve_step_rel_t_eq_0 : L.improve_step 𝓕 ε 0 = 𝓕 :=
sorry

lemma improve_step_rel_C : ∀ᶠ x near L.C, ∀ t, L.improve_step 𝓕 ε t x = 𝓕 x :=
sorry

lemma improve_step_rel_compl_K₁ : ∀ x ∉ L.K₁, ∀ t, L.improve_step 𝓕 ε t x = 𝓕 x :=
sorry

variables {ε}

lemma improve_step_c0_close (ε_pos : 0 < ε) : ∀ x t, ∥L.improve_step 𝓕 ε t x - 𝓕 x∥ ≤ ε :=
sorry


lemma improve_step_hol
  (h_op : R.is_open_over L.U)
  (h_part_hol : ∀ᶠ x near L.K₀, 𝓕.is_part_holonomic_at L.E' x)
  (h_short : ∀ x ∈ L.U, 𝓕.is_short_at L.p x)
  (h_hol : ∀ᶠ x near L.C, 𝓕.is_holonomic_at x)
  (ε_pos : 0 < ε) :
  ∀ᶠ x near L.K₀, (L.improve_step 𝓕 ε 1).is_part_holonomic_at (L.E' ⊔ L.p.span_v) x :=
sorry

end step_landscape

end improve_step

lemma finite_dimensional.fin_succ_basis (K V : Type*) [division_ring K] [add_comm_group V] [module K V]
  [finite_dimensional K V] [nontrivial V] : ∃ (n : ℕ), nonempty (basis (fin (n + 1)) K V) :=
sorry

section improve
/-!
## Full improvement

This section proves lem:h_principle_open_ample_loc.
-/

open finite_dimensional submodule

variables {E}

/--
Homotopy of formal solutions obtained by successive corrugations in some landscape `L` to improve a
formal solution `𝓕` until it becomes holonomic near `L.K₀`.
-/
def rel_loc.formal_sol.improve {R : rel_loc E F} {L : landscape E} {𝓕 : formal_sol R L.U} {ε : ℝ}
(ε_pos : 0 < ε) (h_op : R.is_open_over L.U) (h_ample : R.is_ample)
(h_hol :∀ᶠ x near L.C, 𝓕.is_holonomic_at x) : ∃ H : htpy_formal_sol R L.U,
 (H 0 = 𝓕) ∧
 (∀ᶠ x near L.C, ∀ t, H t x = 𝓕 x ) ∧
 (∀ x, x ∉ L.K₁ → ∀ t, H t x = 𝓕 x) ∧
 (∀ x t, ∥H t x - 𝓕 x∥ ≤ ε) ∧
 (∀ᶠ x near L.K₀, (H 1).is_holonomic_at x) :=
begin
  by_cases hE : nontrivial E,
  { haveI := hE,
    rcases fin_succ_basis ℝ E with ⟨n, ⟨e⟩⟩,

    let E' : fin (n+1) → submodule ℝ E := λ k, span ℝ $ e '' {j : fin (n+1) | j < k},
    suffices : ∀ k : fin (n + 1), ∃ H : htpy_formal_sol R L.U,
      (H 0 = 𝓕) ∧
      (∀ᶠ x near L.C, ∀ t, H t x = 𝓕 x ) ∧
      (∀ x, x ∉ L.K₁ → ∀ t, H t x = 𝓕 x) ∧
      (∀ x t, ∥H t x - 𝓕 x∥ ≤ ε) ∧
      (∀ᶠ x near L.K₀, (H 1).is_part_holonomic_at (E' k) x),
    sorry ; { have eq_top : E' (fin.last n) = ⊤,
      {
        sorry },
      have key := this (fin.last n),
      rw [eq_top] at key,
      simp_rw is_part_holonomic_top at key,
      exact key },
    intro k,
    apply fin.induction_on k,
    { use 𝓕.const_htpy,
      have eq_bot : E' 0 = ⊥,
      {
        sorry },
      sorry ; simp [eq_bot, ε_pos.le] },
    { rintros k ⟨H, hH₀, hHC, hHK₁, hHc0, hH_hol⟩,
      let S : step_landscape E :=
      { E' := E' k,
        p := e.dual_pair' k,
        hEp := sorry,
        ..L},
      have h_span : S.E' ⊔ S.p.span_v = E' k.succ,
      {
        sorry },
      have acc : S.accepts (H 1) :=
      { h_op := sorry,
        hK₀ := sorry,
        h_short := sorry,
        hC := sorry  },
      refine ⟨H.comp (S.improve_step (H 1) ε), _, _, _, _, _⟩,
      sorry;{ simp [hH₀] },
      {
        sorry },
      {
        sorry },
      {
        sorry },
      { have := S.improve_step_hol (H 1) h_op _ _ _ ε_pos,
        sorry ; { rw [h_span] at this,
          rw htpy_formal_sol.comp_1,
          exact this },
        {
          sorry },
        {
          sorry },
        {
          sorry }, } } },
  {
    sorry },
end


end improve
