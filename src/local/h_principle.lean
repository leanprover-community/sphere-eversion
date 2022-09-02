import to_mathlib.analysis.normed_group
import to_mathlib.linear_algebra.basis
import to_mathlib.topology.nhds_set
import to_mathlib.analysis.cut_off

import loops.exists

import local.corrugation
import local.relation

/-!
# Local h-principle for open and ample relations

This file proves lem:h_principle_open_ample_loc
-/

noncomputable theory

open_locale unit_interval classical filter topological_space
open filter set rel_loc

variables (E : Type*) [normed_add_comm_group E] [normed_space ℝ E] [finite_dimensional ℝ E]
          {F : Type*} [normed_add_comm_group F] [normed_space ℝ F] [measurable_space F] [borel_space F]
          [finite_dimensional ℝ F]
          {G : Type*} [normed_add_comm_group G] [normed_space ℝ G]

open_locale unit_interval
/--
The setup for local h-principle is two compact subsets `K₀ ⊆ K₁` in `E` with
`K₀ ⊆ interior K₁` and a closed subset `C`.
-/
structure landscape :=
(C K₀ K₁ : set E)
(hC : is_closed C)
(hK₀ : is_compact K₀)
(hK₁ : is_compact K₁)
(h₀₁ : K₀ ⊆ interior K₁)

section improve_step
/-!
## Improvement step

This section proves lem:integration_step.
-/

/--
The setup for a one-step improvement towards a local h-principle is two compact subsets
`K₀ ⊆ K₁` in `E` with `K₀ ⊆ interior K₁` and a closed subset `C`
together with a dual pair `p` and a subspace `E'` of the corresponding hyperplane `ker p.π`.
-/
structure step_landscape extends landscape E :=
(E' : submodule ℝ E)
(p : dual_pair' E)
(hEp : E' ≤ p.π.ker)

variables {E}

open_locale classical

variables (R : rel_loc E F)

namespace step_landscape

/-- A one-step improvement landscape accepts a formal solution if it can improve it. -/
structure accepts (L : step_landscape E) (𝓕 : jet_sec E F) : Prop :=
(h_op : is_open R)
(hK₀ : ∀ᶠ x near L.K₀, 𝓕.is_part_holonomic_at L.E' x)
(h_short : ∀ x, 𝓕.is_short_at R L.p x)
(hC : ∀ᶠ x near L.C, 𝓕.is_holonomic_at x)

/-- The union of all slices of `R` corresponding to `𝓕`. -/
def Ω (L : step_landscape E) (𝓕 : jet_sec E F) : set (E × F) :=
{p | p.2 ∈ 𝓕.slice_at R L.p p.1}
--⋃ x, ({x} : set E) ×ˢ (connected_component_in (𝓕.slice_at R L.p x) $ 𝓕.φ x L.p.v)

def π (L : step_landscape E) : E →L[ℝ] ℝ := L.p.π

def v (L : step_landscape E) : E := L.p.v

def K (L : step_landscape E) : set E := L.K₁ ∩ L.C

def b (L : step_landscape E) (𝓕 : jet_sec E F) : E → F := λ x, 𝓕.φ x L.v

def g (L : step_landscape E) (𝓕 : jet_sec E F) : E → F := λ x, D 𝓕.f x L.v

lemma is_compact_K (L : step_landscape E) : is_compact L.K :=
L.hK₁.inter_right L.hC

variables {R}

lemma accepts.open {L : step_landscape E} {𝓕 : jet_sec E F} (h : L.accepts R 𝓕) :
  is_open (L.Ω R 𝓕) :=
begin
  set ψ : E × F → one_jet E F := λ p, (p.1, 𝓕.f p.1, L.p.update (𝓕.φ p.1) p.2),
  change is_open {p : E × F | ψ p ∈ R},
  apply is_open.preimage _ h.h_op,
  apply continuous_fst.prod_mk (𝓕.f_diff.continuous.fst'.prod_mk _),
  exact L.p.continuous_update 𝓕.φ_diff.continuous.fst' continuous_snd
end

lemma accepts.smooth_b {L : step_landscape E} {𝓕 : jet_sec E F} (h : L.accepts R 𝓕) :
  𝒞 ∞ (L.b 𝓕) :=
(continuous_linear_map.apply ℝ F L.v).cont_diff.comp 𝓕.φ_diff

lemma accepts.smooth_g {L : step_landscape E} {𝓕 : jet_sec E F} (h : L.accepts R 𝓕) :
  𝒞 ∞ (L.g 𝓕) :=
(continuous_linear_map.apply ℝ F L.v).cont_diff.comp (cont_diff_top_iff_fderiv.mp 𝓕.f_diff).2

lemma accepts.rel {L : step_landscape E} {𝓕 : jet_sec E F} (h : L.accepts R 𝓕) :
  ∀ᶠ (x : E) near L.K, (L.g 𝓕) x = (L.b 𝓕) x :=
begin
  apply (h.hC.filter_mono $ monotone_nhds_set (inter_subset_right L.K₁ L.C)).mono,
  intros x hx,
  dsimp [jet_sec.is_holonomic_at] at hx,
  dsimp [step_landscape.g, step_landscape.b],
  rw hx
end

/-- The loop family to use in some landscape to improve a formal solution. -/
def loop (L : step_landscape E) {𝓕 : formal_sol R} (h : L.accepts R 𝓕) :
ℝ → E → loop F :=
classical.some (exists_loops L.is_compact_K h.open h.smooth_g h.smooth_b h.rel h.h_short)

lemma nice (L : step_landscape E) {𝓕 : formal_sol R} (h : L.accepts R 𝓕) :
  nice_loop (L.g ↑𝓕) (L.b ↑𝓕) (Ω R L 𝓕) L.K (L.loop h) :=
classical.some_spec $ exists_loops L.is_compact_K h.open h.smooth_g h.smooth_b h.rel h.h_short

lemma update_zero (L : step_landscape E) {𝓕 : formal_sol R} (h : L.accepts R 𝓕) (x : E) (s : ℝ) :
L.p.update (𝓕.φ x) ((L.loop h 0 x) s) = 𝓕.φ x :=
begin
  rw (L.nice h).t_zero x s,
  exact L.p.update_self _,
end

lemma loop_smooth (L : step_landscape E) {𝓕 : formal_sol R} (h : L.accepts R 𝓕) :
  𝒞 ∞ ↿(L.loop h) :=
(L.nice h).smooth

lemma loop_smooth' (L : step_landscape E) {𝓕 : formal_sol R} (h : L.accepts R 𝓕)
  {t : G → ℝ} (ht : 𝒞 ∞ t) {s : G → ℝ} (hs : 𝒞 ∞ s) {x : G → E} (hx : 𝒞 ∞ x) :
  𝒞 ∞ (λ g, L.loop h (t g) (x g) (s g)) :=
(L.loop_smooth h).comp (ht.prod $ hx.prod hs)

lemma loop_C1 (L : step_landscape E) {𝓕 : formal_sol R} (h : L.accepts R 𝓕) :
∀ t, 𝒞 1 ↿(L.loop h t) :=
λ t, (L.loop_smooth' h cont_diff_const cont_diff_snd cont_diff_fst).of_le le_top

variables (L : step_landscape E)

-- Cut-off function which needs to satisfies the next three lemmas
def ρ (L : step_landscape E) : E → ℝ :=
(exists_cont_diff_one_nhds_of_interior L.hK₀.is_closed L.h₀₁).some

lemma ρ_smooth (L : step_landscape E) : 𝒞 ∞ L.ρ :=
(exists_cont_diff_one_nhds_of_interior L.hK₀.is_closed L.h₀₁).some_spec.1

lemma ρ_mem (L : step_landscape E) (x : E) : L.ρ x ∈ I :=
(exists_cont_diff_one_nhds_of_interior L.hK₀.is_closed L.h₀₁).some_spec.2.2.2 x

lemma ρ_le (L : step_landscape E) (x : E) : |L.ρ x| ≤ 1 :=
begin
  cases L.ρ_mem x with h h',
  rw abs_le,
  refine ⟨_, h'⟩,
  linarith
end

lemma hρ₀ (L : step_landscape E) : ∀ᶠ x near L.K₀, L.ρ x = 1 :=
(exists_cont_diff_one_nhds_of_interior L.hK₀.is_closed L.h₀₁).some_spec.2.1

lemma hρ_compl_K₁ (L : step_landscape E) {x : E} : x ∉ L.K₁ → L.ρ x = 0 :=
(exists_cont_diff_one_nhds_of_interior L.hK₀.is_closed L.h₀₁).some_spec.2.2.1 x

/--
Homotopy of formal solutions obtained by corrugation in the direction of `p : dual_pair' E`
in some landscape to improve a formal solution `𝓕` from being `L.E'`-holonomic to
`L.E' ⊔ span {p.v}`-holonomic near `L.K₀`.
-/
def improve_step {𝓕 : formal_sol R} (h : L.accepts R 𝓕) (N : ℝ) : htpy_jet_sec E F :=
{ f := λ t x, 𝓕.f x + (smooth_step t*L.ρ x) • corrugation L.π N (L.loop h t) x,
  f_diff :=  𝓕.f_diff.snd'.add $
    (smooth_step.smooth.fst'.mul L.ρ_smooth.snd').smul $
    corrugation.cont_diff' N (L.loop_smooth h) cont_diff_snd cont_diff_fst,
  φ := λ t x, L.p.update (𝓕.φ x) (L.loop h (smooth_step t*L.ρ x) x $ N * L.π x) +
                (smooth_step t*L.ρ x) • (corrugation.remainder L.p.π N (L.loop h 1) x),
  φ_diff := begin
    apply cont_diff.add,
    apply L.p.smooth_update,
    apply 𝓕.φ_diff.snd',
    apply L.loop_smooth',
    exact smooth_step.smooth.fst'.mul L.ρ_smooth.snd',
    apply cont_diff_const.mul L.π.cont_diff.snd',
    exact cont_diff_snd,
    apply cont_diff.smul,
    exact smooth_step.smooth.fst'.mul L.ρ_smooth.snd',
    exact remainder.smooth _ _ (L.loop_smooth h) cont_diff_snd cont_diff_const
  end }

variables {L} {𝓕 : formal_sol R} (h : L.accepts R 𝓕) (N : ℝ)

@[simp]
lemma improve_step_apply (t : ℝ) (x : E) :
  L.improve_step h N t x = (𝓕.f x + (smooth_step t*L.ρ x) • corrugation L.π N (L.loop h t) x,
  L.p.update (𝓕.φ x) (L.loop h (smooth_step t*L.ρ x) x $ N * L.π x) +
                 (smooth_step t*L.ρ x) • (corrugation.remainder L.p.π N (L.loop h 1) x)) :=
by { simp [improve_step, h], refl }

@[simp]
lemma improve_step_apply_f (t : ℝ) (x : E) :
  (L.improve_step h N t).f x = 𝓕.f x + (smooth_step t*L.ρ x) • corrugation L.π N (L.loop h t) x :=
rfl

@[simp]
lemma improve_step_apply_φ (t : ℝ) (x : E) :
  (L.improve_step h N t).φ x = L.p.update (𝓕.φ x) (L.loop h (smooth_step t*L.ρ x) x $ N * L.π x) +
                 (smooth_step t*L.ρ x) • (corrugation.remainder L.p.π N (L.loop h 1) x) :=
rfl

@[simp]
lemma improve_step_of_support (t : ℝ) {x : E}
  (H : ∀ t, x ∉ loop.support (L.loop h t)) :
  L.improve_step h N t x = 𝓕 x :=
begin
  have : ∀ t s, L.loop h t x s = 𝓕.φ x L.v,
      { intros t s,
        rw loop.is_const_of_not_mem_support (H t) s 0,
        apply (L.nice h).s_zero x t },
  rw [improve_step_apply h, corrugation_eq_zero _ _ _ _ (H t),
      remainder_eq_zero _ _ (L.loop_C1 h 1) (H 1)],
  simp only [formal_sol.to_jet_sec_eq_coe, smul_zero, add_zero, this],
  erw L.p.update_self,
  refl
end

lemma improve_step_rel_t_eq_0 : L.improve_step h N 0 = 𝓕 :=
begin
  ext x,
  { rw improve_step_apply_f h,
    simp [(L.nice h).t_zero x] },
  { ext x,
    rw improve_step_apply_φ h,
    simp only [formal_sol.to_jet_sec_eq_coe, zero_mul, smooth_step.zero, zero_smul, add_zero],
    erw L.update_zero h, refl }
end

lemma improve_step_rel_compl_K₁ {x} (hx : x ∉ L.K₁) (t) : L.improve_step h N t x = 𝓕 x :=
begin
  rw [improve_step_apply h, L.hρ_compl_K₁ hx],
  simp only [formal_sol.to_jet_sec_eq_coe, mul_zero, zero_smul, add_zero],
  erw L.update_zero h,
  refl
end

lemma improve_step_rel_K : ∀ᶠ x near L.K, ∀ t, L.improve_step h N t x = 𝓕 x :=
begin
  have : ∀ᶠ x near L.K, ∀ t, x ∉ loop.support (L.loop h t),
  { apply (L.nice h).rel_K.eventually_nhds_set.mono,
    intros x hx t,
    apply loop.not_mem_support,
    apply hx.mono,
    intros y hy,
    exact loop.is_const_of_eq (hy t) },
  apply this.mono,
  intros x hx t,
  exact improve_step_of_support _ _ _ hx
end

lemma improve_step_rel_C : ∀ᶠ x near L.C, ∀ t, L.improve_step h N t x = 𝓕 x :=
begin
  apply eventually.filter_mono (L.hK₁.is_closed.nhds_set_le_sup' L.C),
  rw eventually_sup,
  split,
  { apply improve_step_rel_K },
  { rw eventually_principal,
    exact λ x, improve_step_rel_compl_K₁ h N }
end

lemma bu_lt (t : ℝ) (x : E) {v : F} {ε : ℝ} (hv : ∥v∥ < ε) :
  ∥(smooth_step t * L.ρ x) • v∥ < ε :=
calc ∥(smooth_step t * L.ρ x) • v∥ = |smooth_step t| * |L.ρ x| * ∥v∥ : by
             rw [norm_smul, real.norm_eq_abs, abs_mul]
... ≤ ∥v∥ : mul_le_of_le_one_left (norm_nonneg _) (mul_le_one (smooth_step.abs_le t)
                                                          (abs_nonneg _) (L.ρ_le x))
... < ε : hv

lemma improve_step_c0_close {ε : ℝ} (ε_pos : 0 < ε) :
  ∀ᶠ N in at_top, ∀ x t, ∥(L.improve_step h N t).f x - 𝓕.f x∥ ≤ ε :=
begin
  set γ := L.loop h,
  have γ_cont : continuous ↿(λ t x, γ t x) := (L.nice h).smooth.continuous,
  have γ_C1 : 𝒞 1 ↿(γ 1) := ((L.nice h).smooth.comp (cont_diff_prod_mk_right 1)).of_le le_top,
  apply ((corrugation.c0_small_on L.hK₁ (L.nice h).t_le_zero (L.nice h).t_ge_one γ_cont ε_pos).and $
        remainder_c0_small_on L.π L.hK₁ γ_C1 ε_pos).mono,
  rintros N ⟨H, H'⟩ x t,
  by_cases hx : x ∈ L.K₁,
  { rw [improve_step_apply_f h],
    suffices : ∥(smooth_step t * L.ρ x) • corrugation L.π N (L.loop h t) x∥ ≤ ε, by simpa,
    exact (bu_lt _ _ $ H _ hx t).le },
  { rw show (L.improve_step h N t).f x = 𝓕.f x, from congr_arg prod.fst (improve_step_rel_compl_K₁ h N hx t),
    simp [ε_pos.le] }
end

lemma improve_step_part_hol {N : ℝ} (hN : N ≠ 0) :
  ∀ᶠ x near L.K₀, (L.improve_step h N 1).is_part_holonomic_at (L.E' ⊔ L.p.span_v) x :=
begin
  have γ_C1 : 𝒞 1 ↿(L.loop h 1) := ((L.nice h).smooth.comp (cont_diff_prod_mk_right 1)).of_le le_top,
  let 𝓕' : jet_sec E F :=
  { f := λ x, 𝓕.f x + corrugation L.π N (L.loop h 1) x,
    f_diff := 𝓕.f_diff.add
     (corrugation.cont_diff' _ (L.loop_smooth h) cont_diff_id cont_diff_const),
    φ := λ x , L.p.update (𝓕.φ x) (L.loop h 1 x $ N * L.π x) +
               corrugation.remainder L.p.π N (L.loop h 1) x,
    φ_diff := begin
      apply cont_diff.add,
      apply L.p.smooth_update,
      apply 𝓕.φ_diff,
      apply L.loop_smooth',
      apply cont_diff_const,
      apply cont_diff_const.mul L.π.cont_diff,
      exact cont_diff_id,
      exact remainder.smooth _ _ (L.loop_smooth h) cont_diff_id cont_diff_const
    end },
  have H : ∀ᶠ x near L.K₀, L.improve_step h N 1 x = 𝓕' x,
  { apply L.hρ₀.mono,
    intros x hx,
    simp [improve_step_apply h, hx],
    refl },
  have fderiv_𝓕' := λ x, fderiv_corrugated_map N hN γ_C1 (𝓕.f_diff.of_le le_top) L.p ((L.nice h).avg x),
  rw eventually_congr (H.is_part_holonomic_at_congr (L.E' ⊔ L.p.span_v)),
  apply h.hK₀.mono,
  intros x hx,
  apply rel_loc.jet_sec.is_part_holonomic_at.sup,
  { intros u hu,
    have hu_ker := L.hEp hu,
    dsimp [𝓕'],
    erw [fderiv_𝓕', continuous_linear_map.add_apply, L.p.update_ker_pi _ _ hu_ker,
         L.p.update_ker_pi _ _ hu_ker, hx u hu] },
  { intros u hu,
    rcases submodule.mem_span_singleton.mp hu with ⟨l, rfl⟩,
    rw [(D 𝓕'.f x).map_smul, (𝓕'.φ x).map_smul],
    apply congr_arg,
    dsimp [𝓕'],
    erw [fderiv_𝓕', L.p.update_v, continuous_linear_map.add_apply, L.p.update_v],
    refl }
end

lemma improve_step_formal_sol :
  ∀ᶠ N in at_top, ∀ t, (L.improve_step h N t).is_formal_sol R :=
begin
  set γ := L.loop h,
  have γ_cont : continuous ↿(λ t x, γ t x) := (L.nice h).smooth.continuous,
    have γ_C1 : 𝒞 1 ↿(γ 1) := ((L.nice h).smooth.comp (cont_diff_prod_mk_right 1)).of_le le_top,
  set K := (λ p : E × ℝ × ℝ, (p.1, 𝓕.f p.1, L.p.update (𝓕.φ p.1) (L.loop h p.2.1 p.1 p.2.2))) '' (L.K₁ ×ˢ (I ×ˢ I)),
  have K_cpt : is_compact K,
  { refine (L.hK₁.prod (is_compact_Icc.prod is_compact_Icc)).image _,
    refine continuous_fst.prod_mk (𝓕.f_diff.continuous.fst'.prod_mk _ ),
    apply L.p.continuous_update 𝓕.φ_diff.continuous.fst',
    change continuous (↿(L.loop h) ∘ (λ (g : E × ℝ × ℝ), (g.snd.fst, g.fst, g.snd.snd))),
    exact (L.loop_smooth h).continuous.comp₃ continuous_snd.fst continuous_fst continuous_snd.snd },
  have K_sub : K ⊆ R,
  { rintros _ ⟨⟨x, t, s⟩, ⟨x_in, t_in, s_in⟩, rfl⟩,
    exact (L.nice h).mem_Ω x t s },
  obtain ⟨ε, ε_pos, hε⟩ : ∃ ε, 0 < ε ∧ metric.thickening ε K ⊆ R,
    from  K_cpt.exists_thickening_subset_open h.h_op K_sub,

  apply ((corrugation.c0_small_on L.hK₁ (L.nice h).t_le_zero (L.nice h).t_ge_one γ_cont ε_pos).and $
         remainder_c0_small_on L.π L.hK₁ γ_C1 ε_pos).mono,
  rintros N ⟨H, H'⟩ t x,
  by_cases hxK₁ : x ∈ L.K₁,
  { apply hε,
    rw metric.mem_thickening_iff,
    refine ⟨(x, 𝓕.f x, L.p.update (𝓕.φ x) $ L.loop h (smooth_step t*L.ρ x) x $ N * L.π x), _, _⟩,
    { simp only [hxK₁, formal_sol.to_jet_sec_eq_coe, exists_prop, mem_set_of_eq, eq_self_iff_true, true_and, K],
      exact ⟨⟨x, smooth_step t * L.ρ x, int.fract (N * L.π x)⟩,
            ⟨hxK₁, unit_interval.mul_mem (smooth_step.mem t) (L.ρ_mem x),
              unit_interval.fract_mem _⟩, by simp only [loop.fract_eq]⟩ },
    { simp only [h, improve_step_apply_f, formal_sol.to_jet_sec_eq_coe, improve_step_apply_φ],
      rw [prod.dist_eq, max_lt_iff, prod.dist_eq, max_lt_iff],
      refine ⟨by simpa using ε_pos, _, _⟩ ; dsimp only ; rw dist_self_add_left,
      { exact (bu_lt _ _ $ H _ hxK₁ _) },
      { exact (bu_lt _ _ $ H' _ hxK₁) } } },
  { rw [show ((L.improve_step h N) t).f x = 𝓕.f x,
          from congr_arg prod.fst $ improve_step_rel_compl_K₁ h N hxK₁ t,
        show ((L.improve_step h N) t).φ x = 𝓕.φ x,
          from congr_arg prod.snd $ improve_step_rel_compl_K₁ h N hxK₁ t],
    exact 𝓕.is_sol _ }
end

end step_landscape

end improve_step

section improve
/-!
## Full improvement

This section proves lem:h_principle_open_ample_loc.
-/

open finite_dimensional submodule step_landscape

variables {E} {R : rel_loc E F} (h_op : is_open R) (h_ample : R.is_ample)
variables {L : landscape E}
variables {ε : ℝ} (ε_pos : 0 < ε)

include h_op h_ample ε_pos

/--
Homotopy of formal solutions obtained by successive corrugations in some landscape `L` to improve a
formal solution `𝓕` until it becomes holonomic near `L.K₀`.
-/
lemma rel_loc.formal_sol.improve {𝓕 : formal_sol R}
  (h_hol : ∀ᶠ x near L.C, 𝓕.is_holonomic_at x) :
  ∃ H : htpy_jet_sec E F,
    (H 0 = 𝓕) ∧
    (∀ᶠ x near L.C, ∀ t, H t x = 𝓕 x ) ∧
    (∀ x, x ∉ L.K₁ → ∀ t, H t x = 𝓕 x) ∧
    (∀ x t, ∥(H t).f x - 𝓕.f x∥ ≤ ε) ∧
    (∀ t, (H t).is_formal_sol R) ∧
    (∀ᶠ x near L.K₀, (H 1).is_holonomic_at x) :=
begin
  let n := finrank ℝ E,
  let e := fin_basis ℝ E,
  let E' := e.flag,
  suffices : ∀ k : fin (n + 1), ∀ δ > (0 : ℝ), ∃ H : htpy_jet_sec E F,
    (H 0 = 𝓕) ∧
    (∀ᶠ x near L.C, ∀ t, H t x = 𝓕 x ) ∧
    (∀ x, x ∉ L.K₁ → ∀ t, H t x = 𝓕 x) ∧
    (∀ x t, ∥(H t).f x - 𝓕.f x∥ ≤ δ) ∧
    (∀ t, (H t).is_formal_sol R) ∧
    (∀ᶠ x near L.K₀, (H 1).is_part_holonomic_at (E' k) x),
  { simpa only [show E' (fin.last n) = ⊤, from e.flag_last, is_part_holonomic_top] using
      this (fin.last n) ε ε_pos },
  clear ε_pos ε,
  intro k,
  apply fin.induction_on k ; clear k,
  { intros δ δ_pos,
    use 𝓕.to_jet_sec.const_htpy,
    simp [show E' 0 = ⊥, from e.flag_zero, le_of_lt δ_pos] },
  { rintros k HH δ δ_pos,
    rcases HH (δ/2) (half_pos δ_pos) with ⟨H, hH₀, hHC, hHK₁, hHc0, hH_sol, hH_hol⟩, clear HH,
    let S : step_landscape E :=
    { E' := E' k,
      p := e.dual_pair' k,
      hEp := by simpa only [E', basis.dual_pair'] using e.flag_le_ker_dual k,
      ..L},
    set H₁ : formal_sol R := (hH_sol 1).formal_sol,
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
      h_short := λ x, h_ample.is_short_at H₁ S.p x,
      hC := begin
        apply h_hol.congr (formal_sol.is_holonomic_at_congr _ _ _),
        apply hHC.mono,
        tauto,
      end  },
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
    obtain ⟨N, ⟨hN_close, hN_sol⟩, hNneq⟩ :=
      (((improve_step_c0_close acc $ half_pos δ_pos).and
      (improve_step_formal_sol acc)).and $ eventually_ne_at_top (0 :ℝ)).exists,
    have glue : H 1 = S.improve_step acc N 0,
    { rw improve_step_rel_t_eq_0,
      refl  },
    refine ⟨H.comp (S.improve_step acc N) glue, _, _, _, _, _, _⟩,
    { simp only [hH₀, htpy_jet_sec.comp_of_le, one_div, inv_nonneg, zero_le_bit0, zero_le_one,
                 mul_zero, smooth_step.zero], }, -- t = 0
    { -- rel C
      apply (hHC.and $ hH₁_rel_C.and $ improve_step_rel_C acc N).mono,
      rintros x ⟨hx, hx', hx''⟩ t,
      by_cases ht : t ≤ 1/2,
      { simp only [ht, hx, htpy_jet_sec.comp_of_le]},
      { simp only [ht, hx', hx'', htpy_jet_sec.comp_of_not_le, not_false_iff]} },
    { -- rel K₁
      intros x hx t,
      by_cases ht : t ≤ 1/2,
      { simp only [ht, hx, hHK₁, htpy_jet_sec.comp_of_le, not_false_iff]},
      { simp only [ht, hx, hH₁_K₁, improve_step_rel_compl_K₁, htpy_jet_sec.comp_of_not_le,
                   not_false_iff] } },
    { -- C⁰-close
      intros x t,
      by_cases ht : t ≤ 1/2,
      { apply le_trans _ (half_le_self $ le_of_lt δ_pos),
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
      apply improve_step_part_hol acc hNneq } }
end

/- FIXME: the following lemma is a repackaging. A proper fix would be to edit the
previous one... -/

lemma rel_loc.formal_sol.improve_htpy {𝓕 : formal_sol R}
  (h_hol : ∀ᶠ x near L.C, 𝓕.is_holonomic_at x) :
  ∃ H : htpy_formal_sol R,
    (H 0 = 𝓕) ∧
    (∀ᶠ x near L.C, ∀ t, H t x = 𝓕 x ) ∧
    (∀ x, x ∉ L.K₁ → ∀ t, H t x = 𝓕 x) ∧
    (∀ x t, ∥(H t).f x - 𝓕.f x∥ ≤ ε)  ∧
    (∀ᶠ x near L.K₀, (H 1).is_holonomic_at x) :=
begin
  rcases rel_loc.formal_sol.improve h_op h_ample ε_pos h_hol with ⟨H, h₁, h₂, h₃, h₄, h₅, h₆⟩,
  exact⟨{is_sol := h₅, ..H}, h₁, h₂, h₃, h₄, h₆⟩
end


/-- Lemma `lem:improve_htpy_loc` from the blueprint. -/
lemma rel_loc.htpy_formal_sol.improve {𝓕 : htpy_jet_sec E F} {A : set E} (hA : is_closed A)
  (h_sol : ∀ t, (𝓕 t).is_formal_sol R)
  (h_A : ∀ᶠ x near A, (𝓕 0).is_holonomic_at x ∧ ∀ t, 𝓕 t x = 𝓕 0 x)
  (h_C : ∀ᶠ x near L.C, (𝓕 1).is_holonomic_at x) :
  ∃ 𝓕' : htpy_formal_sol R,
  (𝓕' 0 = 𝓕 0) ∧
  (∀ t, (𝓕' t).is_formal_sol R) ∧
  (∀ᶠ x near A, ∀ t, 𝓕' t x = 𝓕 0 x) ∧
  (∀ᶠ x near L.C, ∀ t, 𝓕' t x = 𝓕 t x) ∧
  (∀ x, x ∉ L.K₁ → ∀ t, 𝓕' t x = 𝓕 t x) ∧
  (∀ x t, (∃ t', 𝓕' t x = 𝓕 t' x) ∨ ∥(𝓕' t).f x - (𝓕 1).f x∥ ≤ ε) ∧
  (∀ᶠ x near L.K₀, (𝓕' 1).is_holonomic_at x) :=
begin
  sorry,
end

end improve
