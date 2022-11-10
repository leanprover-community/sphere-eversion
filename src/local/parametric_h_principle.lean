import local.h_principle

/-!
In this file we prove the parametric version of the local h-principle.

We will not use this to prove the global version of the h-principle, but we do use this to conclude
the existence of sphere eversion from the local h-principle, which is proven in `local.h_principle`.

The parametric h-principle states the following: Suppose that `R` is a local relation,
`𝓕₀ : P → J¹(E, F)` is a family of formal solutions of `R` that is holonomic near some set
`C ⊆ P × E`, `K ⊆ P × E` is compact and `ε : ℝ`,
then there exists a homotopy `𝓕 : ℝ × P → J¹(E, F)` between `𝓕` and a solution that is holonomic
near `K`, that agrees with `𝓕₀` near `C` and is everywhere `ε`-close to `𝓕₀`
-/

noncomputable theory

open metric finite_dimensional set function rel_loc linear_map (ker)
open_locale topological_space pointwise

section parameter_space

variables
{E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
{F : Type*} [normed_add_comm_group F] [normed_space ℝ F]
-- `G` will be `ℝ` in the proof of the parametric h-principle.
-- It indicates the homotopy variable `t`.
{G : Type*} [normed_add_comm_group G] [normed_space ℝ G]
{P : Type*} [normed_add_comm_group P] [normed_space ℝ P]


variables {R : rel_loc E F}

/-- The projection `J¹(P × E, F) → J¹(E, F)`. -/
def one_jet_snd : one_jet (P × E) F → one_jet E F :=
λ p, (p.1.2, p.2.1, p.2.2 ∘L fderiv ℝ (λ y, (p.1.1, y)) p.1.2)

lemma continuous_one_jet_snd :
  continuous (one_jet_snd : one_jet (P × E) F → one_jet E F) :=
continuous_fst.snd.prod_mk $ continuous_snd.fst.prod_mk $ continuous_snd.snd.clm_comp $
  continuous.fderiv (cont_diff_fst.fst.prod_map cont_diff_id) continuous_fst.snd le_top

lemma one_jet_snd_eq (p : one_jet (P × E) F) :
  one_jet_snd p = (p.1.2, p.2.1, p.2.2 ∘L continuous_linear_map.inr ℝ P E) :=
by simp_rw [one_jet_snd, fderiv_prod_right]

variables (P)
/-- The relation `R.relativize P` (`𝓡 ^ P` in the blueprint) is the relation on `J¹(P × E, F)`
induced by `R`. -/
def rel_loc.relativize (R : rel_loc E F) : rel_loc (P × E) F :=
one_jet_snd ⁻¹' R
variables {P}

lemma rel_loc.mem_relativize (R : rel_loc E F) (w : one_jet (P × E) F) :
 w ∈ R.relativize P ↔ (w.1.2, w.2.1, w.2.2 ∘L continuous_linear_map.inr ℝ P E) ∈ R :=
by simp_rw [rel_loc.relativize, mem_preimage, one_jet_snd_eq]

lemma rel_loc.is_open_relativize (R : rel_loc E F) (h2 : is_open R) :
  is_open (R.relativize P) :=
h2.preimage continuous_one_jet_snd

lemma relativize_slice {σ : one_jet (P × E) F}
  {p : dual_pair (P × E)}
  (q : dual_pair E)
  (hpq : p.π.comp (continuous_linear_map.inr ℝ P E) = q.π) :
  (R.relativize P).slice p σ =
  σ.2.2 (p.v - (0, q.v)) +ᵥ R.slice q (one_jet_snd σ) :=
begin
  have h2pq : ∀ x : E, p.π ((0 : P), x) = q.π x := λ x, congr_arg (λ f : E →L[ℝ] ℝ, f x) hpq,
  ext1 w,
  have h1 : (p.update σ.2.2 w).comp (continuous_linear_map.inr ℝ P E) =
    q.update (one_jet_snd σ).2.2 (-σ.2.2 (p.v - (0, q.v)) +ᵥ w),
  { ext1 x,
    simp_rw [continuous_linear_map.comp_apply, continuous_linear_map.inr_apply,
      ← continuous_linear_map.map_neg, neg_sub],
    obtain ⟨u, hu, t, rfl⟩ := q.decomp x,
    have hv : (0, q.v) - p.v ∈ ker p.π,
    { rw [linear_map.mem_ker, map_sub, p.pairing, h2pq, q.pairing, sub_self] },
    have hup : ((0 : P), u) ∈ ker p.π := (h2pq u).trans hu,
    rw [q.update_apply _ hu, ← prod.zero_mk_add_zero_mk, map_add, p.update_ker_pi _ _ hup,
      ← prod.smul_zero_mk, map_smul, vadd_eq_add],
    nth_rewrite 0 [← sub_add_cancel (0, q.v) p.v],
    rw [map_add, p.update_ker_pi _ _ hv, p.update_v, one_jet_snd_eq],
    refl },
  have := preimage_vadd_neg (show F, from σ.2.2 (p.v - (0, q.v))) (R.slice q (one_jet_snd σ)),
  dsimp only at this,
  simp_rw [← this, mem_preimage, mem_slice, R.mem_relativize, h1],
  refl,
end

lemma relativize_slice_eq_univ {σ : one_jet (P × E) F}
  {p : dual_pair (P × E)}
  (hp : p.π.comp (continuous_linear_map.inr ℝ P E) = 0) :
  ((R.relativize P).slice p σ).nonempty ↔
  (R.relativize P).slice p σ = univ :=
begin
  have h2p : ∀ x : E, p.π ((0 : P), x) = 0 := λ x, congr_arg (λ f : E →L[ℝ] ℝ, f x) hp,
  have : ∀ y : F, (p.update σ.2.2 y).comp (continuous_linear_map.inr ℝ P E) =
    σ.2.2.comp (continuous_linear_map.inr ℝ P E),
  { intro y,
    ext1 x,
    simp_rw [continuous_linear_map.comp_apply, continuous_linear_map.inr_apply,
      p.update_ker_pi _ _ (h2p x)] },
  simp_rw [set.nonempty, eq_univ_iff_forall, mem_slice, R.mem_relativize, this, exists_const,
    forall_const]
end

variables (P)

lemma rel_loc.is_ample.relativize (hR : R.is_ample) : (R.relativize P).is_ample :=
begin
  intros p σ,
  let p2 := p.π.comp (continuous_linear_map.inr ℝ P E),
  rcases eq_or_ne p2 0 with h|h,
  { intros w hw,
    rw [(relativize_slice_eq_univ h).mp ⟨w, hw⟩, connected_component_in_univ,
      preconnected_space.connected_component_eq_univ, convex_hull_univ] },
  obtain ⟨u', hu'⟩ := continuous_linear_map.exists_ne_zero h,
  let u := (p2 u')⁻¹ • u',
  let q : dual_pair E :=
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
  f_diff := S.f_diff,
  φ_diff := begin
    refine (cont_diff.fderiv _ cont_diff_id le_top).add (S.φ_diff.clm_comp _),
    { exact S.f_diff.comp (cont_diff_snd.fst.prod cont_diff_fst.snd) },
    { exact cont_diff.fderiv cont_diff_snd.snd cont_diff_id le_top }
    end }

lemma family_jet_sec.uncurry_φ' (S : family_jet_sec E F P) (p : P × E) :
  (S.uncurry).φ p = fderiv ℝ (λ z, S.f z p.2) p.1 ∘L continuous_linear_map.fst ℝ P E +
  S.φ p.1 p.2 ∘L continuous_linear_map.snd ℝ P E :=
begin
  simp_rw [S.uncurry_φ, fderiv_snd, add_left_inj],
  refine (fderiv_comp p
    ((S.f_diff.comp (cont_diff_id.prod cont_diff_const)).differentiable le_top p.1)
    differentiable_at_fst).trans _,
  rw [fderiv_fst],
  refl,
end

lemma family_jet_sec.uncurry_mem_relativize (S : family_jet_sec E F P) {s : P}
  {x : E} : ((s, x), S.uncurry (s, x)) ∈ R.relativize P ↔ (x, S s x) ∈ R :=
begin
  simp_rw [rel_loc.relativize, mem_preimage, one_jet_snd_eq, jet_sec.coe_apply, S.uncurry_f,
    S.uncurry_φ'],
  congr' 2,
  refine prod.ext rfl (prod.ext rfl _),
  ext v,
  simp_rw [continuous_linear_map.comp_apply, continuous_linear_map.add_apply,
    continuous_linear_map.comp_apply, continuous_linear_map.inr_apply,
    continuous_linear_map.coe_fst', continuous_linear_map.coe_snd',
    continuous_linear_map.map_zero, zero_add],
  refl,
end

lemma family_jet_sec.is_holonomic_at_uncurry (S : family_jet_sec E F P) {p : P × E} :
  S.uncurry.is_holonomic_at p ↔ (S p.1).is_holonomic_at p.2 :=
begin
  simp_rw [jet_sec.is_holonomic_at, S.uncurry_φ],
  rw [show S.uncurry.f = λ x, S.uncurry.f x, from rfl, funext S.uncurry_f,
    show (λ x : P × E, S.f x.1 x.2) = ↿S.f, from rfl],
  simp_rw [fderiv_prod_eq_add (S.f_diff.differentiable le_top _), fderiv_snd],
  refine (add_right_inj _).trans _,
  have := fderiv_comp p ((S p.1).f_diff.cont_diff_at.differentiable_at le_top)
    differentiable_at_snd,
  rw [show D (λ (z : P × E), ↿(S.f) (p.fst, z.snd)) p = _, from this, fderiv_snd,
    (show surjective (continuous_linear_map.snd ℝ P E), from prod.snd_surjective)
      .clm_comp_injective.eq_iff],
  refl
end

/-- Turn a family of formal solutions of `R ⊆ J¹(E, E')` parametrized by `P` into a formal solution
of `R.relativize P`. -/
def rel_loc.family_formal_sol.uncurry (S : R.family_formal_sol P) : formal_sol (R.relativize P) :=
begin
  refine ⟨S.to_family_jet_sec.uncurry, _⟩,
  rintro ⟨s, x⟩,
  exact S.to_family_jet_sec.uncurry_mem_relativize.mpr (S.is_sol s x)
end

lemma rel_loc.family_formal_sol.uncurry_φ' (S : R.family_formal_sol P) (p : P × E) :
  (S.uncurry p).2 = fderiv ℝ (λ z, S.f z p.2) p.1 ∘L continuous_linear_map.fst ℝ P E +
  S.φ p.1 p.2 ∘L continuous_linear_map.snd ℝ P E :=
S.to_family_jet_sec.uncurry_φ' p

/-- Turn a family of sections of `J¹(P × E, F)` parametrized by `G` into a family of sections of
`J¹(E, F)` parametrized by `G × P`. -/
def family_jet_sec.curry (S : family_jet_sec (P × E) F G) :
  family_jet_sec E F (G × P) :=
{ f := λ p x, (S p.1).f (p.2, x),
  φ := λ p x, (S p.1).φ (p.2, x) ∘L fderiv ℝ (λ x, (p.2, x)) x,
  f_diff := S.f_diff.comp (cont_diff_prod_assoc : cont_diff ℝ ⊤ (equiv.prod_assoc G P E)),
  φ_diff := begin
    refine (S.φ_diff.comp (cont_diff_prod_assoc : cont_diff ℝ ⊤ (equiv.prod_assoc G P E))).clm_comp
      _,
    refine cont_diff.fderiv _ cont_diff_snd le_top,
    exact cont_diff_fst.fst.snd.prod cont_diff_snd
  end }

lemma family_jet_sec.curry_f (S : family_jet_sec (P × E) F G) (p : G × P)
  (x : E) : (S.curry p).f x = (S p.1).f (p.2, x) :=
rfl

lemma family_jet_sec.curry_φ (S : family_jet_sec (P × E) F G) (p : G × P)
  (x : E) : (S.curry p).φ x = (S p.1).φ (p.2, x) ∘L fderiv ℝ (λ x, (p.2, x)) x :=
rfl

lemma family_jet_sec.curry_φ' (S : family_jet_sec (P × E) F G) (p : G × P)
  (x : E) : (S.curry p).φ x = (S p.1).φ (p.2, x) ∘L continuous_linear_map.inr ℝ P E :=
begin
  rw [S.curry_φ],
  congr' 1,
  refine ((differentiable_at_const _).fderiv_prod differentiable_at_id).trans _,
  rw [fderiv_id, fderiv_const],
  refl,
end

lemma family_jet_sec.is_holonomic_at_curry
  (S : family_jet_sec (P × E) F G)
  {t : G} {s : P} {x : E} (hS : (S t).is_holonomic_at (s, x)) :
  (S.curry (t, s)).is_holonomic_at x :=
begin
  simp_rw [jet_sec.is_holonomic_at, S.curry_φ] at hS ⊢,
  rw [show (S.curry (t, s)).f = λ x, (S.curry (t, s)).f x, from rfl, funext (S.curry_f _)],
  dsimp only,
  refine (fderiv_comp x ((S t).f_diff.cont_diff_at.differentiable_at le_top)
    ((differentiable_at_const _).prod differentiable_at_id)).trans _,
  rw [id, hS],
  refl,
end

lemma family_jet_sec.curry_mem (S : family_jet_sec (P × E) F G)
  {p : G × P} {x : E} (hR : ((p.2, x), S p.1 (p.2, x)) ∈ R.relativize P) :
  (x, S.curry p x) ∈ R :=
begin
  simp_rw [rel_loc.relativize, mem_preimage, jet_sec.coe_apply, one_jet_snd_eq, S.curry_φ'] at hR ⊢,
  exact hR
end

/-- Turn a family of formal solutions of `R.relativize P` parametrized by `G` into a family of
formal solutions of `R` parametrized by `G × P`. -/
def rel_loc.family_formal_sol.curry (S : family_formal_sol G (R.relativize P)) :
  family_formal_sol (G × P) R :=
⟨S.to_family_jet_sec.curry, λ p x, S.to_family_jet_sec.curry_mem (S.is_sol _ _)⟩

lemma rel_loc.family_formal_sol.curry_φ (S : family_formal_sol G (R.relativize P)) (p : G × P)
  (x : E) : (S.curry p).φ x = (S p.1).φ (p.2, x) ∘L fderiv ℝ (λ x, (p.2, x)) x :=
rfl

lemma rel_loc.family_formal_sol.curry_φ' (S : family_formal_sol G (R.relativize P)) (p : G × P)
  (x : E) : (S.curry p x).2 = (S p.1 (p.2, x)).2 ∘L continuous_linear_map.inr ℝ P E :=
S.to_family_jet_sec.curry_φ' p x

lemma curry_eq_iff_eq_uncurry {𝓕 : family_formal_sol G (R.relativize P)}
  {𝓕₀ : R.family_formal_sol P} {t : G} {x : E} {s : P}
  (h : 𝓕 t (s, x) = 𝓕₀.uncurry (s, x)) :
  (𝓕.curry (t, s)) x = 𝓕₀ s x :=
begin
  simp_rw [prod.ext_iff] at h ⊢,
  refine ⟨h.1, _⟩,
  simp_rw [𝓕.curry_φ', h.2, 𝓕₀.uncurry_φ'],
  ext v,
  simp_rw [continuous_linear_map.comp_apply, continuous_linear_map.add_apply,
    continuous_linear_map.comp_apply,
    continuous_linear_map.inr_apply, continuous_linear_map.coe_fst',
    continuous_linear_map.coe_snd', continuous_linear_map.map_zero, zero_add],
  refl
end

end parameter_space

section parametric_h_principle

variables {E : Type*} [normed_add_comm_group E] [normed_space ℝ E] [finite_dimensional ℝ E]
          {F : Type*} [normed_add_comm_group F] [normed_space ℝ F] [finite_dimensional ℝ F]
          {G : Type*} [normed_add_comm_group G] [normed_space ℝ G]
          {P : Type*} [normed_add_comm_group P] [normed_space ℝ P] [finite_dimensional ℝ P]

variables {R : rel_loc E F} (h_op: is_open R) (h_ample: R.is_ample) (L : landscape E)
include h_op h_ample

/- The local parametric h-principle. -/
lemma rel_loc.family_formal_sol.improve_htpy
  {ε : ℝ} (ε_pos : 0 < ε)
  (C : set (P × E)) (hC : is_closed C) (K : set (P × E)) (hK : is_compact K)
  (𝓕₀ : family_formal_sol P R)
  (h_hol : ∀ᶠ (p : P × E) near C, (𝓕₀ p.1).is_holonomic_at p.2) :
  ∃ 𝓕 : family_formal_sol (ℝ × P) R,
    (∀ s x, 𝓕 (0, s) x = 𝓕₀ s x) ∧
    (∀ᶠ (p : P × E) near C, ∀ t, 𝓕 (t, p.1) p.2 = 𝓕₀ p.1 p.2) ∧
    (∀ s x t, ∥(𝓕 (t, s)).f x - 𝓕₀.f s x∥ ≤ ε)  ∧
    (∀ᶠ (p : P × E) near K, (𝓕 (1, p.1)).is_holonomic_at p.2) :=
begin
  let parametric_landscape : landscape (P × E) :=
  { C := C,
    K₀ := K,
    K₁ := (exists_compact_superset hK).some,
    hC := hC,
    hK₀ := hK,
    hK₁ := (exists_compact_superset hK).some_spec.1,
    h₀₁ := (exists_compact_superset hK).some_spec.2 },
  obtain ⟨𝓕, h₁, -, h₂, -, h₄, h₅⟩ :=
    𝓕₀.uncurry.improve_htpy (R.is_open_relativize h_op) (h_ample.relativize P)
    parametric_landscape ε_pos (h_hol.mono (λ p hp, 𝓕₀.is_holonomic_at_uncurry.mpr hp)),
  have h₁ : ∀ p, 𝓕 0 p = 𝓕₀.uncurry p,
  { intro p, rw h₁.on_set 0 right_mem_Iic, refl },
  refine ⟨𝓕.curry, _, _, _, _⟩,
  { intros s x, exact curry_eq_iff_eq_uncurry (h₁ (s, x)) },
  { refine h₂.mono _, rintro ⟨s, x⟩ hp t, exact curry_eq_iff_eq_uncurry (hp t) },
  { intros s x t, exact (h₄ (s, x) t) },
  { refine h₅.mono _, rintros ⟨s, x⟩ hp, exact 𝓕.to_family_jet_sec.is_holonomic_at_curry hp }
end

open filter
open_locale unit_interval

/--
A corollary of the local parametric h-principle, forgetting the homotopy and `ε`-closeness,
and just stating the existence of a solution that is holonomic near `K`.
Furthermore, we assume that `P = ℝ` and `K` is of the form `compact set × I`.
This is sufficient to prove sphere eversion. -/
lemma rel_loc.htpy_formal_sol.exists_sol (𝓕₀ : R.htpy_formal_sol)
  (C : set (ℝ × E)) (hC : is_closed C) (K : set E) (hK : is_compact K)
  (h_hol : ∀ᶠ (p : ℝ × E) near C, (𝓕₀ p.1).is_holonomic_at p.2) :
  ∃ f : ℝ → E → F,
    (𝒞 ∞ $ uncurry f) ∧
    (∀ p ∈ C, f (p : ℝ × E).1 p.2 = (𝓕₀ p.1).f p.2) ∧
    (∀ x ∈ K, ∀ t ∈ I, (x, f t x, D (f t) x) ∈ R) :=
begin
  obtain ⟨𝓕, h₁, h₂, -, h₄⟩ :=
    𝓕₀.improve_htpy h_op h_ample zero_lt_one C hC (I ×ˢ K) (is_compact_Icc.prod hK) h_hol,
  refine ⟨λ s, (𝓕 (1, s)).f, _, _, _⟩,
  { exact 𝓕.f_diff.comp ((cont_diff_const.prod cont_diff_id).prod_map cont_diff_id) },
  { intros p hp, exact (prod.ext_iff.mp (h₂.nhds_set_forall_mem p hp 1)).1 },
  { intros x hx t ht,
    rw [show D (𝓕 (1, t)).f x = (𝓕 (1, t)).φ x, from
      h₄.nhds_set_forall_mem (t, x) (mk_mem_prod ht hx)],
    exact 𝓕.is_sol (1, t) x },
end

end parametric_h_principle
