import local.h_principle
-- import global.parametricity_for_free -- remove!?
import interactive_expr

set_option trace.filter_inst_type true

/-!
This is a stop-gap file to prove the parametric local h-principle.
-/
noncomputable theory

open metric finite_dimensional set function rel_loc
open_locale topological_space

section parameter_space

variables
{E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
{F : Type*} [normed_add_comm_group F] [normed_space ℝ F]
{G : Type*} [normed_add_comm_group G] [normed_space ℝ G] -- this will be ℝ in the application
{P : Type*} [normed_add_comm_group P] [normed_space ℝ P]


variables {R : rel_loc E F}

def one_jet_snd : one_jet (P × E) F → one_jet E F :=
λ p, (p.1.2, p.2.1, p.2.2 ∘L fderiv ℝ (λ y, (p.1.1, y)) p.1.2)

lemma continuous_one_jet_snd :
  continuous (one_jet_snd : one_jet (P × E) F → one_jet E F) :=
begin
  sorry
  -- intro x₀,
  -- refine smooth_at.map_left _ _ smooth_at_id,
  -- { exact smooth_at_snd.snd },
  -- have := cont_mdiff_at.mfderiv'''
  --   (λ (x : one_jet_bundle (J.prod I) (P × E) I' E') (y : E), (x.1.1.1, y))
  --   (λ (x : one_jet_bundle (J.prod I) (P × E) I' E'), x.1.1.2)
  --   (smooth_one_jet_bundle_proj.fst.fst.prod_map smooth_id).smooth_at
  --   smooth_one_jet_bundle_proj.fst.snd.smooth_at le_top,
  -- simp_rw [prod.mk.eta],
  -- exact this
end

lemma one_jet_snd_eq (p : one_jet (P × E) F) :
  one_jet_snd p = (p.1.2, p.2.1, p.2.2 ∘L continuous_linear_map.inr ℝ P E) :=
by simp_rw [one_jet_snd]; sorry -- mfderiv_prod_right

variables (P)
/-- The relation `𝓡 ^ P` -/
def rel_loc.relativize (R : rel_loc E F) : rel_loc (P × E) F :=
one_jet_snd ⁻¹' R
variables {P}

lemma rel_loc.mem_relativize (R : rel_loc E F) (w : one_jet (P × E) F) :
 w ∈ R.relativize P ↔ (w.1.2, w.2.1, w.2.2 ∘L continuous_linear_map.inr ℝ P E) ∈ R :=
by simp_rw [rel_loc.relativize, mem_preimage, one_jet_snd_eq]

lemma rel_loc.is_open_relativize (R : rel_loc E F) (h2 : is_open R) :
  is_open (R.relativize P) :=
h2.preimage continuous_one_jet_snd

open_locale pointwise

lemma relativize_slice {σ : one_jet (P × E) F}
  {p : dual_pair' (P × E)}
  (q : dual_pair' E)
  (hpq : p.π.comp (continuous_linear_map.inr ℝ P E) = q.π) :
  (R.relativize P).slice p σ =
  σ.2.2 (p.v - (0, q.v)) +ᵥ R.slice q (one_jet_snd σ) :=
begin
  sorry,
  -- have h2pq : ∀ x : E, p.π ((0 : P), x) = q.π x := λ x, congr_arg (λ f : E →L[ℝ] ℝ, f x) hpq,
  -- ext1 w,
  -- have h1 : (p.update σ.2 w).comp (continuous_linear_map.inr ℝ P E) =
  --   q.update (one_jet_snd σ).2 (-σ.2 (p.v - (0, q.v)) +ᵥ w),
  -- { ext1 x,
  --   simp_rw [continuous_linear_map.comp_apply, continuous_linear_map.inr_apply,
  --     ← continuous_linear_map.map_neg, neg_sub],
  --   obtain ⟨u, hu, t, rfl⟩ := q.decomp x,
  --   have hv : (0, q.v) - p.v ∈ p.π.ker,
  --   { rw [continuous_linear_map.mem_ker, map_sub, p.pairing, h2pq, q.pairing, sub_self] },
  --   have hup : ((0 : P), u) ∈ p.π.ker := (h2pq u).trans hu,
  --   rw [q.update_apply _ hu, ← prod.zero_mk_add_zero_mk, map_add, p.update_ker_pi _ _ hup,
  --     ← prod.smul_zero_mk, map_smul, vadd_eq_add],
  --   nth_rewrite 0 [← sub_add_cancel (0, q.v) p.v],
  --   rw [map_add, p.update_ker_pi _ _ hv, p.update_v],
  --   refl },
  -- have := preimage_vadd_neg (show F, from σ.2 (p.v - (0, q.v)))
  --   (show set F, from (R.slice (one_jet_snd σ) q)),
  -- dsimp only at this,
  -- simp_rw [← this, mem_preimage, mem_slice, mem_relativize],
  -- dsimp only [one_jet_mk_fst, one_jet_mk_snd],
  -- congr'
end

lemma relativize_slice_eq_univ {σ : one_jet (P × E) F}
  {p : dual_pair' (P × E)}
  (hp : p.π.comp (continuous_linear_map.inr ℝ P E) = 0) :
  ((R.relativize P).slice p σ).nonempty ↔
  (R.relativize P).slice p σ = univ :=
begin
  sorry
  -- have h2p : ∀ x : E, p.π ((0 : P), x) = 0 := λ x, congr_arg (λ f : E →L[ℝ] ℝ, f x) hp,
  -- have : ∀ y : F, (p.update σ.2.2 y).comp (continuous_linear_map.inr ℝ P E) =
  --   σ.2.2.comp (continuous_linear_map.inr ℝ P E),
  -- { intro y,
  --   ext1 x,
  --   simp_rw [continuous_linear_map.comp_apply, continuous_linear_map.inr_apply,
  --     p.update_ker_pi _ _ (h2p x)] },
  -- simp_rw [set.nonempty, eq_univ_iff_forall, mem_slice, mem_relativize],
  -- dsimp only [one_jet_mk_fst, one_jet_mk_snd],
  -- simp_rw [this, exists_const, forall_const]
end

variables (P)

lemma rel_loc.ample.relativize (hR : R.is_ample) : (R.relativize P).is_ample :=
begin
  intros p σ,
  let p2 := p.π.comp (continuous_linear_map.inr ℝ P E),
  rcases eq_or_ne p2 0 with h|h,
  { intros w hw,
    rw [(relativize_slice_eq_univ h).mp ⟨w, hw⟩, connected_component_in_univ,
      preconnected_space.connected_component_eq_univ, convex_hull_univ] },
  obtain ⟨u', hu'⟩ := continuous_linear_map.exists_ne_zero h,
  let u := (p2 u')⁻¹ • u',
  let q : dual_pair' E :=
  ⟨p2, u, by rw [p2.map_smul, smul_eq_mul, inv_mul_cancel hu']⟩,
  rw [relativize_slice q rfl],
  exact (hR q _).vadd
end

variables {P}


/-- Turn a family of sections of `J¹(E, E')` parametrized by `P` into a section of `J¹(P × E, E')`.
-/
@[simps]
def family_jet_sec.uncurry (S : family_jet_sec E F P) : jet_sec (P × E) F :=
{ f := λ p, S.f p.1 p.2,
  φ := λ p, fderiv ℝ (λ z : P × E, S.f z.1 p.2) p +
    S.φ p.1 p.2 ∘L fderiv ℝ prod.snd p,
  f_diff := sorry,
  φ_diff := begin
    sorry
    -- refine smooth.one_jet_add _ _,
    -- { intro y,
    --   refine smooth_at_id.one_jet_bundle_mk (S.smooth_bs y) _,
    --   have : smooth_at ((IP.prod I).prod (IP.prod I)) I'
    --     (function.uncurry (λ x z : P × E, S.f z.1 x.2)) (y, y),
    --   { exact S.smooth_bs.comp (smooth_snd.fst.prod_mk smooth_fst.snd) (y, y) },
    --   apply cont_mdiff_at.mfderiv'' (λ x z : P × E, S.f z.1 x.2) this le_top },
    -- { refine smooth.one_jet_comp I (λ p, p.2) S.smooth smooth_snd.one_jet_ext }
  end }

lemma family_jet_sec.uncurry_φ' (S : family_jet_sec E F P) (p : P × E) :
  (S.uncurry).φ p = fderiv ℝ (λ z, S.f z p.2) p.1 ∘L continuous_linear_map.fst ℝ P E +
  S.φ p.1 p.2 ∘L continuous_linear_map.snd ℝ P E :=
begin
  simp_rw [S.uncurry_φ, fderiv_snd],
  congr' 1,
  sorry
  -- convert mfderiv_comp p
  --   ((S.smooth_bs.comp (smooth_id.prod_mk smooth_const)).mdifferentiable p.1)
  --   (smooth_fst.mdifferentiable p),
  -- simp_rw [mfderiv_fst],
end

lemma family_jet_sec.uncurry_mem_relativize (S : family_jet_sec E F P) {s : P}
  {x : E} : ((s, x), S.uncurry (s, x)) ∈ R.relativize P ↔ (x, S s x) ∈ R :=
begin
  sorry
  -- simp_rw [rel_loc.relativize, mem_preimage, one_jet_sec.coe_apply, map_left],
  -- congr',
  -- ext v,
  -- simp_rw [S.uncurry_φ', continuous_linear_map.comp_apply, continuous_linear_map.add_apply,
  --   continuous_linear_map.comp_apply, continuous_linear_map.inr_apply,
  --   continuous_linear_map.coe_fst', continuous_linear_map.coe_snd',
  --   continuous_linear_map.map_zero, zero_add, S.coe_φ]
end

lemma is_holonomic_uncurry (S : family_jet_sec E F P) {p : P × E} :
  S.uncurry.is_holonomic_at p ↔ (S p.1).is_holonomic_at p.2 :=
begin
  sorry
  -- simp_rw [one_jet_sec.is_holonomic_at, one_jet_sec.snd_eq, S.uncurry_φ],
  -- rw [show S.uncurry.f = λ x, S.uncurry.f x, from rfl, funext S.uncurry_bs],
  -- simp_rw [mfderiv_prod_eq_add (S.smooth_bs.mdifferentiable _), mfderiv_snd, add_right_inj],
  -- dsimp only,
  -- rw [mfderiv_comp p S.smooth_coe_bs.mdifferentiable_at smooth_snd.mdifferentiable_at, mfderiv_snd,
  --   (show surjective (continuous_linear_map.snd ℝ P E), from prod.snd_surjective)
  --     .clm_comp_injective.eq_iff],
  -- refl
end

def family_formal_sol.uncurry (S : R.family_formal_sol P) : formal_sol (R.relativize P) :=
begin
  refine ⟨S.to_family_jet_sec.uncurry, _⟩,
  rintro ⟨s, x⟩,
  exact S.to_family_jet_sec.uncurry_mem_relativize.mpr (S.is_sol s x)
end

lemma family_formal_sol.uncurry_φ' (S : R.family_formal_sol P) (p : P × E) :
  S.uncurry.φ p = fderiv ℝ (λ z, S.f z p.2) p.1 ∘L continuous_linear_map.fst ℝ P E +
  S.φ p.1 p.2 ∘L continuous_linear_map.snd ℝ P E :=
S.to_family_jet_sec.uncurry_φ' p

def family_jet_sec.curry (S : family_jet_sec (P × E) F G) :
  family_jet_sec E F (G × P) :=
{ f := λ p x, (S p.1).f (p.2, x),
  φ := λ p x, (S p.1).φ (p.2, x) ∘L fderiv ℝ (λ x, (p.2, x)) x,
  f_diff := sorry,
  φ_diff := begin
    sorry
    -- rintro ⟨⟨t, s⟩, x⟩,
    -- refine smooth_at_snd.one_jet_mk (S.smooth_bs.comp smooth_prod_assoc _) _,
    -- have h1 : smooth_at ((J.prod IP).prod I) 𝓘(ℝ, P × E →L[ℝ] F)
    --   (in_coordinates (IP.prod I) I' (λ (p : (G × P) × E), (p.1.2, p.2))
    --     (λ (p : (G × P) × E), (S p.1.1).f (p.1.2, p.2))
    --     (λ (p : (G × P) × E), ((S p.1.1).φ (p.1.2, p.2))) ((t, s), x)) ((t, s), x),
    -- { apply (smooth_at_one_jet.mp $
    --     smooth_at.comp _ (by exact S.smooth (t, (s, x))) (smooth_prod_assoc ((t, s), x))).2.2 },
    -- have h2 : smooth_at ((J.prod IP).prod I) 𝓘(ℝ, E →L[ℝ] P × E)
    --   (in_coordinates I (IP.prod I) prod.snd (λ (p : (G × P) × E), (p.1.2, p.2))
    --     (λ (p : (G × P) × E),
    --       (mfderiv I (IP.prod I) (λ (x : E), (p.1.2, x)) p.snd)) ((t, s), x)) ((t, s), x),
    -- { apply cont_mdiff_at.mfderiv''' (λ (p : (G × P) × E) (x : E), (p.1.2, x)) prod.snd
    --     (smooth_at_fst.fst.snd.prod_mk smooth_at_snd :
    --       smooth_at (((J.prod IP).prod I).prod I) (IP.prod I) _ (((t, s), x), x))
    --     (smooth_at_snd : smooth_at ((J.prod IP).prod I) _ _ _) le_top },
    -- exact h1.clm_comp_in_coordinates (continuous_at_fst.snd.prod continuous_at_snd) h2
  end }

lemma family_jet_sec.curry_bs (S : family_jet_sec (P × E) F G) (p : G × P)
  (x : E) : (S.curry p).f x = (S p.1).f (p.2, x) :=
rfl

lemma family_jet_sec.curry_φ (S : family_jet_sec (P × E) F G) (p : G × P)
  (x : E) : (S.curry p).φ x = (S p.1).φ (p.2, x) ∘L fderiv ℝ (λ x, (p.2, x)) x :=
rfl

lemma family_jet_sec.curry_φ' (S : family_jet_sec (P × E) F G) (p : G × P)
  (x : E) : (S.curry p).φ x = (S p.1).φ (p.2, x) ∘L continuous_linear_map.inr ℝ P E :=
begin
  sorry
  -- rw [S.curry_φ],
  -- congr' 1,
  -- refine ((mdifferentiable_at_const I IP).mfderiv_prod smooth_id.mdifferentiable_at).trans _,
  -- rw [mfderiv_id, mfderiv_const],
  -- refl,
end

-- lemma formal_sol.eq_iff {F₁ F₂ : formal_sol R} {x : E} :
--   F₁ x = F₂ x ↔ F₁.f x = F₂.f x ∧ F₁.φ x = by apply F₂.φ x :=
-- by { simp_rw [prod.ext_iff, formal_sol.fst_eq, heq_iff_eq, prod.ext_iff, eq_self_iff_true,
--   true_and], refl }

lemma family_jet_sec.is_holonomic_at_curry
  (S : family_jet_sec (P × E) F G)
  {t : G} {s : P} {x : E} (hS : (S t).is_holonomic_at (s, x)) :
  (S.curry (t, s)).is_holonomic_at x :=
begin
  sorry
  -- simp_rw [one_jet_sec.is_holonomic_at, (S.curry _).snd_eq, S.curry_φ] at hS ⊢,
  -- dsimp only,
  -- rw [show (S.curry (t, s)).f = λ x, (S.curry (t, s)).f x, from rfl, funext (S.curry_bs _)],
  -- dsimp only,
  -- refine (mfderiv_comp x (S t).smooth_bs.mdifferentiable_at
  --   ((mdifferentiable_at_const I IP).prod_mk smooth_id.mdifferentiable_at)).trans _,
  -- rw [id, hS],
  -- refl,
end

lemma family_jet_sec.curry_mem (S : family_jet_sec (P × E) F G)
  {p : G × P} {x : E} (hR : ((p.2, x), S p.1 (p.2, x)) ∈ R.relativize P) :
  (x, S.curry p x) ∈ R :=
begin
  sorry
  -- simp_rw [rel_loc.relativize, mem_preimage, one_jet_sec.coe_apply,
  --   map_left] at hR ⊢,
  -- convert hR,
  -- ext v,
  -- simp_rw [S.curry_φ']
end


def family_formal_sol.curry (S : family_formal_sol G (R.relativize P)) :
  family_formal_sol (G × P) R :=
⟨S.to_family_jet_sec.curry, λ p x, S.to_family_jet_sec.curry_mem (S.is_sol _ _)⟩

lemma family_formal_sol.curry_φ (S : family_formal_sol G (R.relativize P)) (p : G × P)
  (x : E) : (S.curry p).φ x = (S p.1).φ (p.2, x) ∘L fderiv ℝ (λ x, (p.2, x)) x :=
rfl

lemma family_formal_sol.curry_φ' (S : family_formal_sol G (R.relativize P)) (p : G × P)
  (x : E) : (S.curry p).φ x = (S p.1).φ (p.2, x) ∘L continuous_linear_map.inr ℝ P E :=
S.to_family_jet_sec.curry_φ' p x

lemma curry_eq_iff_eq_uncurry {𝓕 : family_formal_sol G (R.relativize P)}
  {𝓕₀ : R.family_formal_sol P} {t : G} {x : E} {s : P}
  (h : 𝓕 t (s, x) = 𝓕₀.uncurry (s, x)) :
  (𝓕.curry (t, s)) x = 𝓕₀ s x :=
begin
  sorry,
  -- simp_rw [formal_sol.eq_iff] at h ⊢,
  -- refine ⟨h.1, _⟩,
  -- simp_rw [𝓕.curry_φ', h.2, 𝓕₀.uncurry_φ'],
  -- ext v,
  -- simp_rw [continuous_linear_map.comp_apply, continuous_linear_map.add_apply,
  --   continuous_linear_map.comp_apply,
  --   continuous_linear_map.inr_apply, continuous_linear_map.coe_fst',
  --   continuous_linear_map.coe_snd', continuous_linear_map.map_zero, zero_add],
  -- refl
end

-- lemma rel_loc.family_formal_sol.parametric_h_principle
--   (R : rel_loc E F) {C : set (P × E)}
--   (ε : E → ℝ) (h : (R.relativize P).satisfies_h_principle C (λ x, ε x.2)) :
--   R.satisfies_h_principle_with IP C ε :=
-- begin
--   intros 𝓕₀ h𝓕₀,
--   obtain ⟨𝓕, h1𝓕, h2𝓕, h3𝓕, h4𝓕⟩ := h 𝓕₀.uncurry _,
--   swap,
--   { refine h𝓕₀.mono (λ p hp, 𝓕₀.to_family_jet_sec.is_holonomic_uncurry.mpr hp) },
--   refine ⟨𝓕.curry, _, _, _, _⟩,
--   { intros s x, exact curry_eq_iff_eq_uncurry (h1𝓕 (s, x)) },
--   { intros s x, exact 𝓕.to_family_jet_sec.is_holonomic_at_curry (h2𝓕 (s, x)) },
--   { refine h3𝓕.mono _, rintro ⟨s, x⟩ hp t, exact curry_eq_iff_eq_uncurry (hp t) },
--   { intros t s x, exact (h4𝓕 t (s, x)) },
-- end



end parameter_space


section parametric_h_principle


variables {E : Type*} [normed_add_comm_group E] [normed_space ℝ E] [finite_dimensional ℝ E]
          {F : Type*} [normed_add_comm_group F] [normed_space ℝ F] [measurable_space F] [borel_space F]
          [finite_dimensional ℝ F]
          {G : Type*} [normed_add_comm_group G] [normed_space ℝ G]
          {P : Type*} [normed_add_comm_group P] [normed_space ℝ P]

variables [finite_dimensional ℝ E] [finite_dimensional ℝ F]

variables {R : rel_loc E F} (h_op: is_open R) (h_ample: R.is_ample) (L : landscape E)
variables {ε : ℝ} (ε_pos : 0 < ε)

include h_op h_ample ε_pos


lemma rel_loc.family_formal_sol.improve_htpy {𝓕 : family_formal_sol P R}
  (C : set P) (hC : is_closed C)
  (h_hol : ∀ᶠ s near C, ∀ x, (𝓕 s).is_holonomic_at x) :
  ∃ H : family_formal_sol (ℝ × P) R,
    (∀ x, H (0, x) = 𝓕 x)
    -- ∧
    -- (∀ᶠ x near L.C, ∀ t, H t x = 𝓕 x) ∧
    -- (∀ x, x ∉ L.K₁ → ∀ t, H t x = 𝓕 x) ∧
    -- (∀ x t, ∥(H t).f x - 𝓕.f x∥ ≤ ε)  ∧
    -- (∀ᶠ x near L.K₀, (H 1).is_holonomic_at x)
    :=
begin
  sorry
  -- rcases rel_loc.formal_sol.improve h_op h_ample ε_pos h_hol with ⟨H, h₁, h₂, h₃, h₄, h₅, h₆⟩,
  -- exact⟨{is_sol := h₅, ..H}, h₁, h₂, h₃, h₄, h₆⟩
end

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
  let := 𝓕.uncurry,
  have := family_formal_sol.uncurry 𝓕,
  sorry
end

end parametric_h_principle
