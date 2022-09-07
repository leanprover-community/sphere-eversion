import global.relation

noncomputable theory

open set function filter (hiding map_smul) charted_space smooth_manifold_with_corners
open_locale topological_space manifold pointwise

section parameter_space
/-! ## Fundamental definitions -/

variables
{E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
{H : Type*} [topological_space H] {I : model_with_corners ℝ E H}
{M : Type*} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
{E' : Type*} [normed_add_comm_group E'] [normed_space ℝ E']
{H' : Type*} [topological_space H'] {I' : model_with_corners ℝ E' H'}
{M' : Type*} [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M']
{EP : Type*} [normed_add_comm_group EP] [normed_space ℝ EP]
{HP : Type*} [topological_space HP] {IP : model_with_corners ℝ EP HP}
{P : Type*} [topological_space P] [charted_space HP P] [smooth_manifold_with_corners IP P]
{F : Type*} [normed_add_comm_group F] [normed_space ℝ F]
{G : Type*} [topological_space G] {J : model_with_corners ℝ F G}
{N : Type*} [topological_space N] [charted_space G N] [smooth_manifold_with_corners J N]
{EX : Type*} [normed_add_comm_group EX] [normed_space ℝ EX]
{HX : Type*} [topological_space HX] {IX : model_with_corners ℝ EX HX}
-- note: X is a metric space
{X : Type*} [metric_space X] [charted_space HX X] [smooth_manifold_with_corners IX X]
variables {R : rel_mfld I M I' M'}

variables (IP P)

/-- The relation `𝓡 ^ P` -/
def rel_mfld.relativize (R : rel_mfld I M I' M') : rel_mfld (IP.prod I) (P × M) I' M' :=
bundle_snd ⁻¹' R

variables {IP P}

lemma rel_mfld.mem_relativize (R : rel_mfld I M I' M') (w : one_jet_bundle (IP.prod I) (P × M) I' M') :
 w ∈ R.relativize IP P ↔
  (one_jet_bundle.mk w.1.1.2 w.1.2 (w.2.comp (continuous_linear_map.inr ℝ EP E)) :
    one_jet_bundle I M I' M') ∈ R :=
by { simp_rw [rel_mfld.relativize, mem_preimage, bundle_snd_eq], refl }

lemma rel_mfld.is_open_relativize (R : rel_mfld I M I' M') (h2 : is_open R) :
  is_open (R.relativize IP P) :=
h2.preimage smooth_bundle_snd.continuous

lemma relativize_slice {σ : one_jet_bundle (IP.prod I) (P × M) I' M'}
  {p : dual_pair' $ tangent_space (IP.prod I) σ.1.1}
  (q : dual_pair' $ tangent_space I σ.1.1.2)
  (hpq : p.π.comp (continuous_linear_map.inr ℝ EP E) = q.π) :
  (R.relativize IP P).slice σ p =
  σ.2 (p.v - (0, q.v)) +ᵥ R.slice (bundle_snd σ) q :=
begin
  have h2pq : ∀ x : E, p.π ((0 : EP), x) = q.π x := λ x, congr_arg (λ f : E →L[ℝ] ℝ, f x) hpq,
  ext1 w,
  have h1 : (p.update σ.2 w).comp (continuous_linear_map.inr ℝ EP E) =
    q.update (bundle_snd σ).2 (-σ.2 (p.v - (0, q.v)) +ᵥ w),
  { ext1 x,
    simp_rw [continuous_linear_map.comp_apply, continuous_linear_map.inr_apply,
      ← continuous_linear_map.map_neg, neg_sub],
    obtain ⟨u, hu, t, rfl⟩ := q.decomp x,
    have hv : (0, q.v) - p.v ∈ p.π.ker,
    { rw [continuous_linear_map.mem_ker, map_sub, p.pairing, h2pq, q.pairing, sub_self] },
    have hup : ((0 : EP), u) ∈ p.π.ker := (h2pq u).trans hu,
    rw [q.update_apply _ hu, ← prod.zero_mk_add_zero_mk, map_add, p.update_ker_pi _ _ hup,
      ← prod.smul_zero_mk, map_smul, vadd_eq_add],
    nth_rewrite 0 [← sub_add_cancel (0, q.v) p.v],
    rw [map_add, p.update_ker_pi _ _ hv, p.update_v, bundle_snd_eq],
    refl },
  have := preimage_vadd_neg (show E', from σ.2 (p.v - (0, q.v)))
    (show set E', from (R.slice (bundle_snd σ) q)),
  dsimp only at this,
  simp_rw [← this, mem_preimage, mem_slice, R.mem_relativize],
  dsimp only [one_jet_bundle_mk_fst, one_jet_bundle_mk_snd],
  congr'
end

lemma relativize_slice_eq_univ {σ : one_jet_bundle (IP.prod I) (P × M) I' M'}
  {p : dual_pair' $ tangent_space (IP.prod I) σ.1.1}
  (hp : p.π.comp (continuous_linear_map.inr ℝ EP E) = 0) :
  ((R.relativize IP P).slice σ p).nonempty ↔
  (R.relativize IP P).slice σ p = univ :=
begin
  have h2p : ∀ x : E, p.π ((0 : EP), x) = 0 := λ x, congr_arg (λ f : E →L[ℝ] ℝ, f x) hp,
  have : ∀ y : E', (p.update σ.snd y).comp (continuous_linear_map.inr ℝ EP E) =
    σ.snd.comp (continuous_linear_map.inr ℝ EP E),
  { intro y,
    ext1 x,
    simp_rw [continuous_linear_map.comp_apply, continuous_linear_map.inr_apply,
      p.update_ker_pi _ _ (h2p x)] },
  simp_rw [set.nonempty, eq_univ_iff_forall, mem_slice, R.mem_relativize],
  dsimp only [one_jet_bundle_mk_fst, one_jet_bundle_mk_snd],
  simp_rw [this, exists_const, forall_const]
end

variables (IP P)

lemma rel_mfld.ample.relativize (hR : R.ample) : (R.relativize IP P).ample :=
begin
  intros σ p,
  let p2 := p.π.comp (continuous_linear_map.inr ℝ EP E),
  rcases eq_or_ne p2 0 with h|h,
  { intros w hw,
    rw [(relativize_slice_eq_univ h).mp ⟨w, hw⟩, connected_component_in_univ,
      preconnected_space.connected_component_eq_univ, convex_hull_univ] },
  obtain ⟨u', hu'⟩ := continuous_linear_map.exists_ne_zero h,
  let u := (p2 u')⁻¹ • u',
  let q : dual_pair' (tangent_space I σ.1.1.2) :=
  ⟨p2, u, by rw [p2.map_smul, smul_eq_mul, inv_mul_cancel hu']⟩,
  rw [relativize_slice q rfl],
  refine (hR q).vadd,
end

variables {IP P}

lemma family_one_jet_sec.uncurry_mem_relativize (S : family_one_jet_sec I M I' M' IP P) {s : P}
  {x : M} : S.uncurry (s, x) ∈ R.relativize IP P ↔ S s x ∈ R :=
begin
  simp_rw [rel_mfld.relativize, mem_preimage, bundle_snd_eq, one_jet_sec.coe_apply,
    map_left],
  congr',
  ext v,
  simp_rw [S.uncurry_ϕ', continuous_linear_map.comp_apply, continuous_linear_map.add_apply,
    continuous_linear_map.comp_apply, continuous_linear_map.inr_apply,
    continuous_linear_map.coe_fst', continuous_linear_map.coe_snd',
    continuous_linear_map.map_zero, zero_add, S.coe_ϕ]
end

def family_formal_sol.uncurry
  (S : family_formal_sol IP P R) : formal_sol (R.relativize IP P) :=
begin
  refine ⟨S.to_family_one_jet_sec.uncurry, _⟩,
  rintro ⟨s, x⟩,
  exact S.to_family_one_jet_sec.uncurry_mem_relativize.mpr (S.is_sol' s x)
end

lemma family_formal_sol.uncurry_ϕ' (S : family_formal_sol IP P R) (p : P × M) :
  S.uncurry.ϕ p = mfderiv IP I' (λ z, S.bs z p.2) p.1 ∘L continuous_linear_map.fst ℝ EP E +
  S.ϕ p.1 p.2 ∘L continuous_linear_map.snd ℝ EP E :=
S.to_family_one_jet_sec.uncurry_ϕ' p

def family_one_jet_sec.curry (S : family_one_jet_sec (IP.prod I) (P × M) I' M' J N) :
  family_one_jet_sec I M I' M' (J.prod IP) (N × P) :=
{ bs := λ p x, (S p.1).bs (p.2, x),
  ϕ := λ p x, (S p.1).ϕ (p.2, x) ∘L mfderiv I (IP.prod I) (λ x, (p.2, x)) x,
  smooth' := begin
    rintro ⟨⟨t, s⟩, x⟩,
    refine smooth_at_snd.one_jet_bundle_mk (S.smooth_bs.comp smooth_prod_assoc _) _,
    have h1 : smooth_at ((J.prod IP).prod I) 𝓘(ℝ, EP × E →L[ℝ] E')
      (in_coordinates (IP.prod I) I' (λ (p : (N × P) × M), (p.1.2, p.2))
        (λ (p : (N × P) × M), (S p.1.1).bs (p.1.2, p.2))
        (λ (p : (N × P) × M), ((S p.1.1).ϕ (p.1.2, p.2))) ((t, s), x)) ((t, s), x),
    { apply (smooth_at_one_jet_bundle.mp $
        smooth_at.comp _ (by exact S.smooth (t, (s, x))) (smooth_prod_assoc ((t, s), x))).2.2 },
    have h2 : smooth_at ((J.prod IP).prod I) 𝓘(ℝ, E →L[ℝ] EP × E)
      (in_coordinates I (IP.prod I) prod.snd (λ (p : (N × P) × M), (p.1.2, p.2))
        (λ (p : (N × P) × M),
          (mfderiv I (IP.prod I) (λ (x : M), (p.1.2, x)) p.2)) ((t, s), x)) ((t, s), x),
    { apply cont_mdiff_at.mfderiv''' (λ (p : (N × P) × M) (x : M), (p.1.2, x)) prod.snd
        (smooth_at_fst.fst.snd.prod_mk smooth_at_snd :
          smooth_at (((J.prod IP).prod I).prod I) (IP.prod I) _ (((t, s), x), x))
        (smooth_at_snd : smooth_at ((J.prod IP).prod I) _ _ _) le_top },
    exact h1.clm_comp_in_coordinates (continuous_at_fst.snd.prod continuous_at_snd) h2
  end }

lemma family_one_jet_sec.curry_bs (S : family_one_jet_sec (IP.prod I) (P × M) I' M' J N) (p : N × P)
  (x : M) : (S.curry p).bs x = (S p.1).bs (p.2, x) :=
rfl

lemma family_one_jet_sec.curry_ϕ (S : family_one_jet_sec (IP.prod I) (P × M) I' M' J N) (p : N × P)
  (x : M) : (S.curry p).ϕ x = (S p.1).ϕ (p.2, x) ∘L mfderiv I (IP.prod I) (λ x, (p.2, x)) x :=
rfl

lemma family_one_jet_sec.curry_ϕ' (S : family_one_jet_sec (IP.prod I) (P × M) I' M' J N) (p : N × P)
  (x : M) : (S.curry p).ϕ x = (S p.1).ϕ (p.2, x) ∘L continuous_linear_map.inr ℝ EP E :=
begin
  rw [S.curry_ϕ],
  congr' 1,
  refine ((mdifferentiable_at_const I IP).mfderiv_prod smooth_id.mdifferentiable_at).trans _,
  rw [mfderiv_id, mfderiv_const],
  refl,
end

lemma formal_sol.eq_iff {F₁ F₂ : formal_sol R} {x : M} :
  F₁ x = F₂ x ↔ F₁.bs x = F₂.bs x ∧ F₁.ϕ x = by apply F₂.ϕ x :=
by { simp_rw [sigma.ext_iff, formal_sol.fst_eq, heq_iff_eq, prod.ext_iff, eq_self_iff_true,
  true_and], refl }

lemma family_one_jet_sec.is_holonomic_at_curry
  (S : family_one_jet_sec (IP.prod I) (P × M) I' M' J N)
  {t : N} {s : P} {x : M} (hS : (S t).is_holonomic_at (s, x)) :
  (S.curry (t, s)).is_holonomic_at x :=
begin
  simp_rw [one_jet_sec.is_holonomic_at, (S.curry _).snd_eq, S.curry_ϕ] at hS ⊢,
  dsimp only,
  rw [show (S.curry (t, s)).bs = λ x, (S.curry (t, s)).bs x, from rfl, funext (S.curry_bs _)],
  dsimp only,
  refine (mfderiv_comp x (S t).smooth_bs.mdifferentiable_at
    ((mdifferentiable_at_const I IP).prod_mk smooth_id.mdifferentiable_at)).trans _,
  rw [id, hS],
  refl,
end

lemma family_one_jet_sec.curry_mem (S : family_one_jet_sec (IP.prod I) (P × M) I' M' J N)
  {p : N × P} {x : M} (hR : S p.1 (p.2, x) ∈ R.relativize IP P) :
  S.curry p x ∈ R :=
begin
  simp_rw [rel_mfld.relativize, mem_preimage, bundle_snd_eq, one_jet_sec.coe_apply,
    map_left] at hR ⊢,
  convert hR,
  ext v,
  simp_rw [S.curry_ϕ']
end


def family_formal_sol.curry (S : family_formal_sol J N (R.relativize IP P)) :
  family_formal_sol (J.prod IP) (N × P) R :=
⟨S.to_family_one_jet_sec.curry, λ p x, S.to_family_one_jet_sec.curry_mem S.is_sol⟩

lemma family_formal_sol.curry_ϕ (S : family_formal_sol J N (R.relativize IP P)) (p : N × P)
  (x : M) : (S.curry p).ϕ x = (S p.1).ϕ (p.2, x) ∘L mfderiv I (IP.prod I) (λ x, (p.2, x)) x :=
rfl

lemma family_formal_sol.curry_ϕ' (S : family_formal_sol J N (R.relativize IP P)) (p : N × P)
  (x : M) : (S.curry p).ϕ x = (S p.1).ϕ (p.2, x) ∘L continuous_linear_map.inr ℝ EP E :=
S.to_family_one_jet_sec.curry_ϕ' p x

lemma curry_eq_iff_eq_uncurry {𝓕 : family_formal_sol J N (R.relativize IP P)}
  {𝓕₀ : family_formal_sol IP P R} {t : N} {x : M} {s : P}
  (h : 𝓕 t (s, x) = 𝓕₀.uncurry (s, x)) :
  (𝓕.curry (t, s)) x = 𝓕₀ s x :=
begin
  simp_rw [formal_sol.eq_iff] at h ⊢,
  refine ⟨h.1, _⟩,
  simp_rw [𝓕.curry_ϕ', h.2, 𝓕₀.uncurry_ϕ'],
  ext v,
  simp_rw [continuous_linear_map.comp_apply, continuous_linear_map.add_apply,
    continuous_linear_map.comp_apply,
    continuous_linear_map.inr_apply, continuous_linear_map.coe_fst',
    continuous_linear_map.coe_snd', continuous_linear_map.map_zero, zero_add],
  refl
end

lemma rel_mfld.satisfies_h_principle.satisfies_h_principle_with
  (R : rel_mfld I M IX X) {C : set (P × M)}
  (ε : M → ℝ) (h : (R.relativize IP P).satisfies_h_principle C (λ x, ε x.2)) :
  R.satisfies_h_principle_with IP C ε :=
begin
  intros 𝓕₀ h𝓕₀,
  obtain ⟨𝓕, h1𝓕, h2𝓕, h3𝓕, h4𝓕⟩ :=
    h 𝓕₀.uncurry (h𝓕₀.mono (λ p hp, 𝓕₀.to_family_one_jet_sec.is_holonomic_uncurry.mpr hp)),
  refine ⟨𝓕.curry, _, _, _, _⟩,
  { intros s x, exact curry_eq_iff_eq_uncurry (h1𝓕 (s, x)) },
  { intros s x, exact 𝓕.to_family_one_jet_sec.is_holonomic_at_curry (h2𝓕 (s, x)) },
  { refine h3𝓕.mono _, rintro ⟨s, x⟩ hp t, exact curry_eq_iff_eq_uncurry (hp t) },
  { intros t s x, exact (h4𝓕 t (s, x)) },
end

end parameter_space
