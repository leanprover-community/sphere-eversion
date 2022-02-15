import to_mathlib.analysis.normed_group
import to_mathlib.analysis.normed_space.finite_dimension
import to_mathlib.linear_algebra.basis
import to_mathlib.topology.nhds_set

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

variables (R : rel_loc E F) --{U : set E}

namespace step_landscape

/-- A one-step improvement landscape accepts a formal solution if it can improve it. -/
structure accepts (L : step_landscape E) (𝓕 : jet_sec L.U F) : Prop :=
(h_op : R.is_open_over L.U)
(hK₀ : ∀ᶠ x near L.K₀, 𝓕.is_part_holonomic_at L.E' x)
(h_short : ∀ x ∈ L.U, 𝓕.is_short_at R L.p x)
(hC : ∀ᶠ x near L.C, 𝓕.is_holonomic_at x)

def Ω (L : step_landscape E) (𝓕 : jet_sec L.U F) : set (E × F) :=
⋃ x ∈ L.U, ({x} : set E) ×ˢ (connected_comp_in (𝓕.slice_at R L.p x) $ 𝓕.φ x L.p.v)

def π (L : step_landscape E) : E →L[ℝ] ℝ := L.p.π

def v (L : step_landscape E) : E := L.p.v

def K (L : step_landscape E) : set E := L.K₁ ∩ L.C

def b (L : step_landscape E) (𝓕 : jet_sec L.U F) : E → F := λ x, 𝓕.φ x L.v

def g (L : step_landscape E) (𝓕 : jet_sec L.U F) : E → F := λ x, D 𝓕.f x L.v

lemma is_compact_K (L : step_landscape E) : is_compact L.K :=
L.hK₁.inter_right L.hC

lemma hKU (L : step_landscape E) : L.K ⊆ L.U :=
((inter_subset_left _ _).trans L.hK₁U)

variables {R}

lemma mem_Ω {L : step_landscape E} {𝓕 : jet_sec L.U F} {x : E} {w : F} (H : (x, w) ∈ L.Ω R 𝓕) :
  (x, 𝓕.f x, L.p.update (𝓕.φ x) w) ∈ R :=
begin
  obtain ⟨x, -, h, rfl⟩ : ∃ x', x' ∈ L.U ∧
                                w ∈ connected_comp_in (𝓕.slice_at R L.p x') (𝓕.φ x' L.p.v) ∧ x' = x,
  by simpa [step_landscape.Ω] using H,
  exact (connected_comp_in_subset _ _ h : _)
end

lemma accepts.open {L : step_landscape E} {𝓕 : jet_sec L.U F} (h : L.accepts R 𝓕) :
  is_open (L.Ω R 𝓕 ∩ (L.U ×ˢ (univ : set F))) :=
sorry

lemma accepts.connected {L : step_landscape E} {𝓕 : formal_sol R L.U} (h : L.accepts R 𝓕) :
  ∀ x ∈ L.U, is_connected (prod.mk x ⁻¹' (L.Ω R 𝓕)) :=
begin

  sorry
end

lemma accepts.smooth_b {L : step_landscape E} {𝓕 : jet_sec L.U F} (h : L.accepts R 𝓕) :
  ∀ x ∈ L.U, smooth_at (L.b 𝓕) x :=
sorry

lemma accepts.smooth_g {L : step_landscape E} {𝓕 : jet_sec L.U F} (h : L.accepts R 𝓕) :
  ∀ x ∈ L.U, smooth_at (L.g 𝓕) x :=
sorry

lemma accepts.mem {L : step_landscape E} {𝓕 : jet_sec L.U F} (h : L.accepts R 𝓕) :
  ∀ x ∈ L.U, (x, L.b 𝓕 x) ∈ L.Ω R 𝓕 :=
sorry

lemma accepts.rel {L : step_landscape E} {𝓕 : jet_sec L.U F} (h : L.accepts R 𝓕) :
  ∀ᶠ (x : E) near L.K, (L.g 𝓕) x = (L.b 𝓕) x :=
sorry

lemma accepts.hull {L : step_landscape E} {𝓕 : jet_sec L.U F} (h : L.accepts R 𝓕) :
  ∀ x ∈ L.U, L.g 𝓕 x ∈ hull (prod.mk x ⁻¹' L.Ω R 𝓕) :=
sorry

/-- The loop family to use in some landscape to improve a formal solution. -/
def loop (L : step_landscape E) {𝓕 : formal_sol R L.U} (h : L.accepts R 𝓕) :
ℝ → E → loop F :=
classical.some (exists_loops L.hU L.is_compact_K L.hKU h.open h.connected h.smooth_g
                             h.smooth_b h.mem h.rel h.hull)

lemma loop_mem (L : step_landscape E) {𝓕 : formal_sol R L.U} (h : L.accepts R 𝓕) :
∀ (x ∈ L.U) t s, L.loop h t x s ∈ (prod.mk x ⁻¹' L.Ω R 𝓕) :=
λ x x_in t s,
(classical.some_spec $ exists_loops L.hU L.is_compact_K L.hKU h.open h.connected h.smooth_g
                             h.smooth_b h.mem h.rel h.hull).mem_Ω x x_in t s

lemma loop_t_zero_eq (L : step_landscape E) {𝓕 : formal_sol R L.U} (h : L.accepts R 𝓕) :
∀ x s, L.loop h 0 x s = L.b 𝓕 x :=
λ x s,
  (classical.some_spec (exists_loops L.hU L.is_compact_K L.hKU h.open h.connected h.smooth_g
                             h.smooth_b h.mem h.rel h.hull)).t_zero x s

lemma loop_s_zero_eq (L : step_landscape E) {𝓕 : formal_sol R L.U} (h : L.accepts R 𝓕) :
∀ x t, L.loop h t x 0 = L.b 𝓕 x :=
λ x t,
  (classical.some_spec (exists_loops L.hU L.is_compact_K L.hKU h.open h.connected h.smooth_g
                             h.smooth_b h.mem h.rel h.hull)).s_zero x t

lemma loop_t_zero_is_const (L : step_landscape E) {𝓕 : formal_sol R L.U} (h : L.accepts R 𝓕) (x : E) :
  (L.loop h 0 x).is_const :=
begin
  intros s s',
  simp only [L.loop_t_zero_eq h x]
end

lemma update_zero (L : step_landscape E) {𝓕 : formal_sol R L.U} (h : L.accepts R 𝓕) (x : E) (s : ℝ) :
L.p.update (𝓕.φ x) ((L.loop h 0 x) s) = 𝓕.φ x :=
begin
  rw L.loop_t_zero_eq h x s,
  exact L.p.update_self _,
end

lemma loop_smooth (L : step_landscape E) {𝓕 : formal_sol R L.U} (h : L.accepts R 𝓕) :
∀ (x ∈ L.U) t s, smooth_at ↿(L.loop h) ((t, x, s) : ℝ × E × ℝ) :=
λ x x_in t s,
(classical.some_spec $ exists_loops L.hU L.is_compact_K L.hKU h.open h.connected h.smooth_g
                             h.smooth_b h.mem h.rel h.hull).smooth x x_in t s

lemma loop_C1 (L : step_landscape E) {𝓕 : formal_sol R L.U} (h : L.accepts R 𝓕) :
∀ (x ∈ L.U) t, 𝒞 1 ↿(L.loop h t) :=
sorry


lemma loop_avg (L : step_landscape E) {𝓕 : formal_sol R L.U} (h : L.accepts R 𝓕) :
 ∀ (x ∈ L.U), (L.loop h 1 x).average = L.g 𝓕 x :=
λ x x_in,
(classical.some_spec $ exists_loops L.hU L.is_compact_K L.hKU h.open h.connected h.smooth_g
                             h.smooth_b h.mem h.rel h.hull).avg x x_in

lemma loop_K (L : step_landscape E) {𝓕 : formal_sol R L.U} (h : L.accepts R 𝓕) :
  ∀ᶠ x in 𝓝ˢ L.K, ∀ t s, L.loop h t x s = L.b 𝓕 x :=
(classical.some_spec $ exists_loops L.hU L.is_compact_K L.hKU h.open h.connected h.smooth_g
                             h.smooth_b h.mem h.rel h.hull).rel_K

variables (L : step_landscape E)

-- Cut-off function which needs to satisfies the next three lemmas
def ρ (L : step_landscape E) : E → ℝ :=
sorry

lemma ρ_smooth (L : step_landscape E) : 𝒞 ∞ L.ρ :=
sorry

lemma ρ_le (L : step_landscape E) (x : E) : |L.ρ x| ≤ 1 :=
sorry

lemma hρ₀ (L : step_landscape E) : ∀ᶠ x near L.K₀, L.ρ x = 1 :=
sorry

lemma hρ₁ (L : step_landscape E) : closure {x | L.ρ x ≠ 0} ⊆ L.K₁ :=
sorry

lemma hρ_compl_K₁ (L : step_landscape E) {x : E} : x ∉ L.K₁ → L.ρ x = 0 :=
sorry

lemma hρ_compl_U (L : step_landscape E) {x : E} : x ∉ L.U → L.ρ x = 0 :=
λ hx, hρ_compl_K₁ _ (λ hx', hx $ L.hK₁U hx')

/--
Homotopy of formal solutions obtained by corrugation in the direction of `p : dual_pair' E`
in some landscape to improve a formal solution `𝓕` from being `L.E'`-holonomic to
`L.E' ⊔ span {p.v}`-holonomic near `L.K₀`.
-/
def improve_step (𝓕 : formal_sol R L.U) (N : ℝ) : htpy_jet_sec L.U F :=
if h : L.accepts R 𝓕
then
  { f := λ t x, 𝓕.f x + (smooth_step t*L.ρ x) • corrugation L.π N (L.loop h t) x,
    f_diff := sorry,
    φ := λ t x , L.p.update (𝓕.φ x) (L.loop h (t*L.ρ x) x $ N * L.π x) +
                 (smooth_step t*L.ρ x) • (corrugation.remainder L.p.π N (L.loop h 1) x),
    φ_diff := sorry }
else
  𝓕.to_jet_sec.const_htpy

variables {𝓕 : formal_sol R L.U}

/-
The next three lemmas are three versions of saying that if L doesn't accept 𝓕 then
the improved section will be the constant homotopy with value 𝓕.
-/

lemma improve_step_rel {N t : ℝ} {x} (H : L.accepts R 𝓕 → L.improve_step 𝓕 N t x = 𝓕 x) :
  L.improve_step 𝓕 N t x = 𝓕 x :=
begin
  by_cases h : L.accepts R 𝓕,
  { exact H h },
  rw [improve_step, dif_neg h],
  refl
end

lemma improve_step_rel' {N t : ℝ} (H : L.accepts R 𝓕 → L.improve_step 𝓕 N t = 𝓕) :
  L.improve_step 𝓕 N t = 𝓕 :=
begin
  by_cases h : L.accepts R 𝓕,
  { exact H h },
  rw [improve_step, dif_neg h],
  ext x; refl
end

lemma improve_step_rel'' {N : ℝ} {a : filter E}
  (H : L.accepts R 𝓕 → ∀ᶠ x in a, ∀ t, L.improve_step 𝓕 N t x = 𝓕 x) :
  ∀ᶠ x in a, ∀ t, L.improve_step 𝓕 N t x = 𝓕 x :=
begin
  by_cases h : L.accepts R 𝓕,
  { exact H h },
  { apply eventually_of_forall (λ x, _),
    rw [improve_step, dif_neg h],
    intro t,
    refl }
end

@[simp]
lemma improve_step_apply (h : L.accepts R 𝓕) (N : ℝ) (t : ℝ) (x : E) :
  L.improve_step 𝓕 N t x = (𝓕.f x + (smooth_step t*L.ρ x) • corrugation L.π N (L.loop h t) x,
  L.p.update (𝓕.φ x) (L.loop h (t*L.ρ x) x $ N * L.π x) +
                 (smooth_step t*L.ρ x) • (corrugation.remainder L.p.π N (L.loop h 1) x)) :=
by { simp [improve_step, h], refl }

variable {L}

@[simp]
lemma improve_step_apply_f (h : L.accepts R 𝓕) (N : ℝ) (t : ℝ) (x : E) :
  (L.improve_step 𝓕 N t).f x = 𝓕.f x + (smooth_step t*L.ρ x) • corrugation L.π N (L.loop h t) x :=
by { simp [improve_step, h], refl }

@[simp]
lemma improve_step_apply_φ (h : L.accepts R 𝓕) (N : ℝ) (t : ℝ) (x : E) :
  (L.improve_step 𝓕 N t).φ x = L.p.update (𝓕.φ x) (L.loop h (t*L.ρ x) x $ N * L.π x) +
                 (smooth_step t*L.ρ x) • (corrugation.remainder L.p.π N (L.loop h 1) x) :=
by { simp [improve_step, h], refl }

@[simp]
lemma improve_step_of_support (h : L.accepts R 𝓕) (N : ℝ) (t : ℝ) {x : E}
  (H : ∀ t, x ∉ loop.support (L.loop h t)) :
  L.improve_step 𝓕 N t x = 𝓕 x :=
begin
  have : ∀ t s, L.loop h t x s = 𝓕.φ x L.v,
      { intros t s,
        rw loop.is_const_of_not_mem_support (H t) s 0,
        apply L.loop_s_zero_eq h x },
  refine L.improve_step_rel (λ h, _),
  rw L.improve_step_apply h,
  by_cases x_in : x ∈ L.U,
  { rw [corrugation_eq_zero _ _ _ (H t),
        remainder_eq_zero _ _ (L.loop_C1 h x x_in 1) (H 1)],
    simp only [formal_sol.to_jet_sec_eq_coe, smul_zero, add_zero, this],
    erw L.p.update_self,
    refl },
    { simp only [L.hρ_compl_U x_in, formal_sol.to_jet_sec_eq_coe, mul_zero, zero_smul, add_zero],
      rw L.loop_t_zero_eq h x,
      erw L.p.update_self,
      refl, }
end

variables (L) (𝓕) (N : ℝ)

lemma improve_step_rel_t_eq_0 : L.improve_step 𝓕 N 0 = 𝓕 :=
begin
  refine L.improve_step_rel' (λ h, _),
  ext x,
  { rw improve_step_apply_f h,
    simp [L.loop_t_zero_is_const h x] },
  { ext x,
    rw improve_step_apply_φ h,
    simp only [formal_sol.to_jet_sec_eq_coe, zero_mul, smooth_step.zero, zero_smul, add_zero],
    erw L.update_zero h, refl }
end

lemma improve_step_rel_compl_K₁ {x} (hx : x ∉ L.K₁) (t) : L.improve_step 𝓕 N t x = 𝓕 x :=
begin
  refine L.improve_step_rel (λ h, _),
  rw L.improve_step_apply h,
  rw L.hρ_compl_K₁ hx,
  simp only [formal_sol.to_jet_sec_eq_coe, mul_zero, zero_smul, add_zero],
  erw L.update_zero h,
  refl
end

lemma improve_step_rel_K : ∀ᶠ x near L.K, ∀ t, L.improve_step 𝓕 N t x = 𝓕 x :=
begin
  refine L.improve_step_rel'' (λ h, _),
  have : ∀ᶠ x near L.K, ∀ t, x ∉ loop.support (L.loop h t),
  { apply (L.loop_K h).eventually_nhds_set.mono,
    intros x hx t,
    apply loop.not_mem_support,
    apply hx.mono,
    intros y hy,
    exact loop.is_const_of_eq (hy t) },
  apply this.mono,
  intros x hx t,
  exact improve_step_of_support _ _ _ hx
end

lemma improve_step_rel_C : ∀ᶠ x near L.C, ∀ t, L.improve_step 𝓕 N t x = 𝓕 x :=
begin
  refine L.improve_step_rel'' (λ h, _),
  have := L.hK₁.is_closed.nhds_set_le_sup L.C,
  apply eventually.filter_mono this, clear this,
  rw eventually_sup,
  split,
  { have : ∀ᶠ x near L.K, corrugation.remainder L.p.π N (L.loop h 1) x = 0,
    {
      sorry },
    rw inter_comm,
    --have := remainder_eq_zero,
    apply ((L.loop_K h).and this).mono,
    rintros x ⟨hx, hx'⟩ t,
    rw [L.improve_step_apply, hx'],

    sorry },
  { rw eventually_principal,
    intro x,
    exact L.improve_step_rel_compl_K₁ 𝓕 N }
end


lemma improve_step_c0_close {ε : ℝ} (ε_pos : 0 < ε) :
  ∀ᶠ N in at_top, ∀ x t, ∥L.improve_step 𝓕 N t x - 𝓕 x∥ ≤ ε :=
begin


  sorry
end

lemma improve_step_hol
  (h_op : R.is_open_over L.U)
  (h_part_hol : ∀ᶠ x near L.K₀, 𝓕.is_part_holonomic_at L.E' x)
  (h_short : ∀ x ∈ L.U, 𝓕.is_short_at L.p x)
  (h_hol : ∀ᶠ x near L.C, 𝓕.is_holonomic_at x) :
  ∀ N, ∀ᶠ x near L.K₀, (L.improve_step 𝓕 N 1).is_part_holonomic_at (L.E' ⊔ L.p.span_v) x :=
-- use is_part_holonomic_at.sup
sorry


lemma improve_step_sol
  (h_op : R.is_open_over L.U)
  (h_part_hol : ∀ᶠ x near L.K₀, 𝓕.is_part_holonomic_at L.E' x)
  (h_short : ∀ x ∈ L.U, 𝓕.is_short_at L.p x)
  (h_hol : ∀ᶠ x near L.C, 𝓕.is_holonomic_at x) :
  ∀ᶠ N in at_top, ∀ t, (L.improve_step 𝓕 N t).is_formal_sol R :=
begin
  have h : L.accepts R 𝓕, from ⟨h_op, h_part_hol, h_short, h_hol⟩,
  set γ := L.loop h,
  have cst  : ∀ x ∉ L.K₁, ∀ t, (γ t x).is_const,
  {
    sorry },
  have le_zero : ∀ x t, t ≤ 0 → γ t x = γ 0 x,
  {
    sorry },
  have ge_one : ∀ x t, t ≥ 1 → γ t x = γ 1 x,
  {
    sorry },
  have γ_cpt : is_compact (loop.support $ γ 1),
  {
    sorry },
  have γ_cont : continuous ↿(λ t x, γ t x),
  {
    sorry },
  have γ_C1 : 𝒞 1 ↿(γ 1),
  {
    sorry },
  set K := {q : one_jet E F | q.1 ∈ L.K₁ ∧ q.2.1 = 𝓕.f q.1 ∧
                                       ∃ t s, q.2.2 = L.p.update (𝓕.φ q.1) (L.loop h t q.1 s)},
  have K_cpt : is_compact K,
  {
    sorry },
  have K_sub : K ⊆ R ∩ L.U ×ˢ univ,
  {
    sorry },
  obtain ⟨ε, ε_pos : 0 < ε, hε : metric.thickening ε K ⊆ R⟩ :=
    h_op.exists_thickening K_cpt K_sub,

  apply ((corrugation.c0_small' L.π L.hK₁ cst le_zero ge_one γ_cont ε_pos).and $
         remainder_c0_small L.π γ_cpt γ_C1 ε_pos).mono,
  rintros N ⟨H, H'⟩ t x x_in,
  by_cases hxK₁ : x ∈ L.K₁,
  { apply hε,
    rw metric.mem_thickening_iff,
    refine ⟨(x, 𝓕.f x, L.p.update (𝓕.φ x) $ L.loop h (t*L.ρ x) x $ N * L.π x), _, _⟩,
    { simp [K, hxK₁],
      use [t * L.ρ x, N * L.π x] },
    { simp only [h, improve_step_apply_f, formal_sol.to_jet_sec_eq_coe, improve_step_apply_φ],
      rw [prod.dist_eq, max_lt_iff, prod.dist_eq, max_lt_iff],
      refine ⟨by simp [ε_pos], _, _⟩ ; dsimp only ; rw dist_add',
      { calc ∥(smooth_step t * L.ρ x) • corrugation L.π N (L.loop _ t) x∥ =
        |smooth_step t| * |L.ρ x| * ∥corrugation L.π N (L.loop _ t) x∥ : by
           rw [norm_smul, real.norm_eq_abs, abs_mul]
           ... ≤ ∥corrugation L.π N (L.loop _ t) x∥ : mul_le_of_le_one_left (norm_nonneg _)
                                                         (mul_le_one (smooth_step.abs_le t)
                                                          (abs_nonneg _) (L.ρ_le x))
          ... < _ : H _ _ },
      { calc ∥(smooth_step t * L.ρ x) • corrugation.remainder (L.p.π) N (γ 1) x∥ =
        |smooth_step t| * |L.ρ x| * ∥corrugation.remainder (L.p.π) N (γ 1) x∥ : by
          rw [norm_smul, real.norm_eq_abs, abs_mul]
        ... ≤ ∥corrugation.remainder (L.p.π) N (γ 1) x∥ : mul_le_of_le_one_left (norm_nonneg _)
                                                         (mul_le_one (smooth_step.abs_le t)
                                                          (abs_nonneg _) (L.ρ_le x))
        ... < ε : H' x } } },
  { rw [show ((L.improve_step 𝓕 N) t).f x = 𝓕.f x,
          from congr_arg prod.fst $ L.improve_step_rel_compl_K₁ 𝓕 N hxK₁ t,
        show ((L.improve_step 𝓕 N) t).φ x = 𝓕.φ x,
          from congr_arg prod.snd $ L.improve_step_rel_compl_K₁ 𝓕 N hxK₁ t],
    exact 𝓕.is_sol _ x_in }
end

end step_landscape

end improve_step


section improve
/-!
## Full improvement

This section proves lem:h_principle_open_ample_loc.
-/

open finite_dimensional submodule

variables {E}
.

/--
Homotopy of formal solutions obtained by successive corrugations in some landscape `L` to improve a
formal solution `𝓕` until it becomes holonomic near `L.K₀`.
-/
lemma rel_loc.formal_sol.improve {R : rel_loc E F} {L : landscape E} {𝓕 : formal_sol R L.U} {ε : ℝ}
  (ε_pos : 0 < ε) (h_op : R.is_open_over L.U) (h_ample : R.is_ample)
  (h_hol :∀ᶠ x near L.C, 𝓕.is_holonomic_at x) :
  ∃ H : htpy_jet_sec L.U F,
    (H 0 = 𝓕) ∧
    (∀ᶠ x near L.C, ∀ t, H t x = 𝓕 x ) ∧
    (∀ x, x ∉ L.K₁ → ∀ t, H t x = 𝓕 x) ∧
    (∀ x t, ∥H t x - 𝓕 x∥ ≤ ε) ∧
    (∀ t, (H t).is_formal_sol R) ∧
    (∀ᶠ x near L.K₀, (H 1).is_holonomic_at x) :=
begin
  let n := finrank ℝ E,
  let e := fin_basis ℝ E,
  let E' := e.flag,
  suffices : ∀ k : fin (n + 1), ∀ δ: ℝ, 0 < δ → ∃ H : htpy_jet_sec L.U F,
    (H 0 = 𝓕) ∧
    (∀ᶠ x near L.C, ∀ t, H t x = 𝓕 x ) ∧
    (∀ x, x ∉ L.K₁ → ∀ t, H t x = 𝓕 x) ∧
    (∀ x t, ∥H t x - 𝓕 x∥ ≤ δ) ∧
    (∀ t, (H t).is_formal_sol R) ∧
    (∀ᶠ x near L.K₀, (H 1).is_part_holonomic_at (E' k) x),
  { simpa only [show E' (fin.last n) = ⊤, from e.flag_last, is_part_holonomic_top] using
      this (fin.last n) ε ε_pos },
  clear ε_pos ε,
  intro k,
  apply fin.induction_on k ; clear k,
  { intros δ δ_pos,
    use 𝓕.to_jet_sec.const_htpy,
    simp [show E' 0 = ⊥, from e.flag_zero, δ_pos.le] },
  { rintros k HH δ δ_pos,
    rcases HH (δ/2) (half_pos δ_pos) with ⟨H, hH₀, hHC, hHK₁, hHc0, hH_sol, hH_hol⟩, clear HH,
    let S : step_landscape E :=
    { E' := E' k,
      p := e.dual_pair' k,
      hEp := by simp only [E', basis.dual_pair', linear_map.ker_to_continuous_linear_map,
                            e.flag_le_ker_dual],
      ..L},
    set H₁ : formal_sol R L.U := (hH_sol 1).formal_sol,
    have h_span : S.E' ⊔ S.p.span_v = E' k.succ := e.flag_span_succ k,
    have acc : S.accepts R H₁ :=
    { h_op := h_op,
      hK₀ := begin
        apply hH_hol.mono,
        intros x hx,
        dsimp [S],
        convert hx,
        rw [← fin.coe_eq_cast_succ, coe_coe]
      end,
      h_short := λ x _, h_ample.is_short_at_jet_sec H₁ S.p x,
      hC := begin
        apply h_hol.congr (formal_sol.is_holonomic_at_congr _ _ _),
        apply hHC.mono,
        tauto,
      end  },
    have hH₁_K₀ : ∀ᶠ (x : E) near S.to_landscape.K₀, H₁.is_part_holonomic_at S.E' x,
    { apply hH_hol.mono,
      intros x hx,
      apply hx.mono,
      apply e.flag_mono,
      rw fin.coe_eq_cast_succ },
    have hH₁_short : ∀ (x : E), x ∈ S.to_landscape.U → H₁.is_short_at S.p x,
    { intros,
      apply h_ample.is_short_at },
    have hH₁_rel_C : ∀ᶠ (x : E) near S.C, H₁ x = 𝓕 x,
    { apply hHC.mono,
      intros x hx,
      apply hx },
    have hH₁_C : ∀ᶠ (x : E) near S.to_landscape.C, H₁.is_holonomic_at x,
    { apply h_hol.congr (formal_sol.is_holonomic_at_congr _ _ _),
      exact (h_hol.and hH₁_rel_C).mono (λ x hx, hx.2.symm) },
    have hH₁_K₁ : ∀ x ∉ L.K₁, H₁ x = 𝓕 x,
    { intros x hx,
      apply hHK₁ x hx },
    obtain ⟨N, hN_close, hN_sol⟩ :=
      ((S.improve_step_c0_close H₁ $ half_pos δ_pos).and
      (S.improve_step_sol H₁ h_op hH₁_K₀ hH₁_short hH₁_C)).exists,
    refine ⟨H.comp (S.improve_step H₁ N), _, _, _, _, _, _⟩,
    { simp only [hH₀, htpy_jet_sec.comp_of_le, one_div, inv_nonneg, zero_le_bit0, zero_le_one,
                 mul_zero, smooth_step.zero], }, -- t = 0
    { -- rel C
      apply (hHC.and $ hH₁_rel_C.and $ S.improve_step_rel_C H₁ N).mono,
      rintros x ⟨hx, hx', hx''⟩ t,
      by_cases ht : t ≤ 1/2,
      { simp only [ht, hx, htpy_jet_sec.comp_of_le]},
      { simp only [ht, hx', hx'', htpy_jet_sec.comp_of_not_le, not_false_iff]} },
    { -- rel K₁
      intros x hx t,
      by_cases ht : t ≤ 1/2,
      { simp only [ht, hx, hHK₁, htpy_jet_sec.comp_of_le, not_false_iff]},
      { simp only [ht, hx, hH₁_K₁, S.improve_step_rel_compl_K₁, htpy_jet_sec.comp_of_not_le,
                   not_false_iff] } },
    { -- C⁰-close
      intros x t,
      by_cases ht : t ≤ 1/2,
      { apply le_trans _ (half_le_self δ_pos.le),
        simp only [ht, hHc0, htpy_jet_sec.comp_of_le]},
      { simp only [ht, htpy_jet_sec.comp_of_not_le, not_false_iff],
        rw ← add_halves δ,
        exact norm_sub_le_add_of_le (hN_close _ _) (hHc0 _ _) } },
    { -- formal solution
      intros t,
      by_cases ht : t ≤ 1/2,
      { simp only [ht, hH_sol, htpy_jet_sec.comp_of_le]},
      { simp only [ht, hN_sol, htpy_jet_sec.comp_of_not_le, not_false_iff] } },
    {  -- part-hol E' (k + 1)
      rw [← h_span, htpy_jet_sec.comp_1],
      apply S.improve_step_hol H₁ h_op,
      { -- part-hol E'
        simpa only [← fin.coe_eq_cast_succ] using hH_hol },
      { -- short
        intros,
        apply h_ample.is_short_at },
      { -- hol near C
        apply h_hol.congr (formal_sol.is_holonomic_at_congr _ _ _),
        apply hHC.mono (λ x hx, (hx 1).symm) } } }
end


end improve
