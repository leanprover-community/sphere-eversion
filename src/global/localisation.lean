import local.h_principle

import global.relation
--import global.localisation_data

import interactive_expr
set_option trace.filter_inst_type true

/-! # Link with the local story

This file bridges the gap between Chapter 2 and Chapter 3. It builds on the
`smooth_embbeding` file but goes all the way to vector spaces (the previous file
is about embedding any manifold into another one).
-/

noncomputable theory

open set function filter (hiding map_smul) charted_space smooth_manifold_with_corners
open_locale topological_space manifold

section loc
/-! ## Localizing relations and 1-jet sections

Now we really bridge the gap all the way to vector spaces.
-/

variables {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
variables {E' : Type*} [normed_add_comm_group E'] [normed_space ℝ E']

/-- For maps between vector spaces, `one_jet_ext` is the obvious thing. -/
@[simp] theorem one_jet_ext_eq_fderiv {f : E → E'} {x : E} :
  one_jet_ext 𝓘(ℝ, E) 𝓘(ℝ, E') f x = ⟨(x, f x), fderiv ℝ f x⟩ :=
by { rw ← mfderiv_eq_fderiv, refl }

/-- Convert a 1-jet section between vector spaces seen as manifold to a 1-jet section
between those vector spaces. -/
def one_jet_sec.loc (F : one_jet_sec 𝓘(ℝ, E) E 𝓘(ℝ, E') E') : jet_sec E E' :=
{ f := F.bs,
  f_diff := F.smooth_bs.cont_diff,
  φ := λ x, (F x).2,
  φ_diff := begin
    rw [cont_diff_iff_cont_diff_at],
    intro x₀,
    have : smooth_at _ _ _ _ := F.smooth x₀,
    simp_rw [smooth_at_one_jet_bundle, in_coordinates, in_coordinates',
      basic_smooth_vector_bundle_core.tangent_space_self_coord_change_at,
      continuous_linear_map.one_def, continuous_linear_map.comp_id, continuous_linear_map.id_comp]
      at this,
      exact this.2.2.cont_diff_at,
  end }

lemma one_jet_sec.loc_hol_at_iff (F : one_jet_sec 𝓘(ℝ, E) E 𝓘(ℝ, E') E') (x : E) :
F.loc.is_holonomic_at x ↔ F.is_holonomic_at x :=
begin
  dsimp only [one_jet_sec.is_holonomic_at],
  rw mfderiv_eq_fderiv,
  exact iff.rfl
end

/-- Turns a relation between `E` and `E'` seen as manifolds into a relation between them
seen as vector spaces. One annoying bit is `equiv.prod_assoc E E' $ E →L[ℝ] E'` that is needed
to reassociate a product of types. -/
def rel_mfld.rel_loc (R : rel_mfld 𝓘(ℝ, E) E 𝓘(ℝ, E') E') : rel_loc E E' :=
(homeomorph.prod_assoc _ _ _).symm ⁻¹'
  ((one_jet_bundle_model_space_homeomorph E 𝓘(ℝ, E) E' 𝓘(ℝ, E')).symm ⁻¹' R)

lemma ample_of_ample (R : rel_mfld 𝓘(ℝ, E) E 𝓘(ℝ, E') E') (hR : R.ample) :
  R.rel_loc.is_ample :=
by { rintro p ⟨x, y, ϕ⟩, exact @hR ⟨(x, y), ϕ⟩ p }

lemma is_open_of_is_open (R : rel_mfld 𝓘(ℝ, E) E 𝓘(ℝ, E') E') (hR : is_open R) :
  is_open R.rel_loc :=
(homeomorph.is_open_preimage _).mpr $ (homeomorph.is_open_preimage _).mpr hR

def htpy_formal_sol.loc {R : rel_mfld 𝓘(ℝ, E) E 𝓘(ℝ, E') E'} (F : htpy_formal_sol R) :
  R.rel_loc.htpy_formal_sol :=
{ f := F.bs,
  f_diff := begin
    rw [← cont_mdiff_iff_cont_diff, ← charted_space_self_prod, model_with_corners_self_prod],
    exact F.smooth_bs,
  end,
  φ := F.ϕ,
  φ_diff := begin
    rw [cont_diff_iff_cont_diff_at],
    intro x,
    have : smooth_at _ _ _ _ := (smooth_at_one_jet_bundle.mp (F.smooth x)).2.2,
    simp_rw [in_coordinates, in_coordinates'_tangent_bundle_core_model_space] at this,
    rwa [← cont_mdiff_at_iff_cont_diff_at, ← charted_space_self_prod, model_with_corners_self_prod]
  end,
  is_sol := λ t x, F.is_sol }

end loc

section unloc
/-! ## Unlocalizing relations and 1-jet sections

-/

variables {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
variables {E' : Type*} [normed_add_comm_group E'] [normed_space ℝ E']

/-- Convert a 1-jet section between vector spaces to a 1-jet section
between those vector spaces seen as manifolds. -/
def jet_sec.unloc (𝓕 : jet_sec E E') : one_jet_sec 𝓘(ℝ, E) E 𝓘(ℝ, E') E' :=
{ bs := 𝓕.f,
  ϕ := λ x, (𝓕 x).2,
  smooth' := begin
    intros a,
    refine smooth_at_one_jet_bundle.mpr _,
    refine ⟨smooth_at_id, 𝓕.f_diff.cont_mdiff a, _⟩,
    dsimp [in_coordinates, in_coordinates', chart_at],
    simp only [range_id, fderiv_within_univ, fderiv_id, continuous_linear_map.id_comp,
      continuous_linear_map.comp_id],
    exact 𝓕.φ_diff.cont_mdiff a,
  end }

lemma jet_sec.unloc_hol_at_iff (𝓕 : jet_sec E E') (x : E) :
𝓕.unloc.is_holonomic_at x ↔ 𝓕.is_holonomic_at x :=
begin
  dsimp only [one_jet_sec.is_holonomic_at],
  rw mfderiv_eq_fderiv,
  exact iff.rfl
end

def htpy_jet_sec.unloc (𝓕 : htpy_jet_sec E E') : htpy_one_jet_sec 𝓘(ℝ, E) E 𝓘(ℝ, E') E' :=
{ bs := λ t, (𝓕 t).f,
  ϕ := λ t x, (𝓕 t x).2,
  smooth' := begin
    intros a,
    refine smooth_at_one_jet_bundle.mpr _,
    refine ⟨smooth_at_snd,
      (𝓕.f_diff.cont_mdiff (a.fst, a.snd)).comp a (smooth_at_fst.prod_mk_space smooth_at_snd), _⟩,
    dsimp [in_coordinates, in_coordinates', chart_at],
    simp only [range_id, fderiv_within_univ, fderiv_id, continuous_linear_map.id_comp,
      continuous_linear_map.comp_id],
    exact (𝓕.φ_diff.cont_mdiff (a.fst, a.snd)).comp a (smooth_at_fst.prod_mk_space smooth_at_snd),
  end }

end unloc

variables
  {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
  {H : Type*} [topological_space H]
  (I : model_with_corners ℝ E H)
  (M : Type*) [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
  {E' : Type*} [normed_add_comm_group E'] [normed_space ℝ E']
  {H' : Type*} [topological_space H']
  (I' : model_with_corners ℝ E' H')
  (M' : Type*) [metric_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M']

variables {R : rel_mfld I M I' M'}

/-- A pair of charts together with a compact subset of the first vector space. -/
structure chart_pair :=
(φ : open_smooth_embedding 𝓘(ℝ, E) E I M)
(ψ : open_smooth_embedding 𝓘(ℝ, E') E' I' M')
(K₁ : set E)
(hK₁ : is_compact K₁)

variables  (p : chart_pair I M I' M') {I M I' M'}

/-- A pair of chart accepts `F : htpy_formal_sol R` if the base map of
`F` sends the first chart into the second one. -/
def chart_pair.accepts (F : htpy_formal_sol R) := ∀ t, range ((F t).bs ∘ p.φ) ⊆ range p.ψ

variable {p}

lemma chart_pair.accepts.image_subset {F : htpy_formal_sol R} (h : p.accepts F) (t : ℝ) :
  (F t).bs '' range (p.φ) ⊆ range p.ψ :=
begin
  rw ← range_comp, exact (h t)
end

variable (p)

def htpy_formal_sol.localize (F : htpy_formal_sol R) (hF : p.accepts F) :
  (R.localize p.φ p.ψ).rel_loc.htpy_formal_sol :=
(F.localize' p.φ p.ψ hF).loc

lemma htpy_formal_sol.is_holonomic_localize (F : htpy_formal_sol R) (hF : p.accepts F)
  (x t) (hx : (F t).is_holonomic_at (p.φ x)) : (F.localize p hF t).is_holonomic_at x :=
(one_jet_sec.loc_hol_at_iff _ _).mpr $
  (is_holonomic_at_localize_iff (F t).to_one_jet_sec p.φ p.ψ (hF t) x).mpr hx

lemma htpy_formal_sol.localize_eq_of_eq (F : htpy_formal_sol R) (hF : p.accepts F)
  {t x} (h : F t (p.φ x) = F 0 (p.φ x)) :
  F.localize p hF t x = F.localize p hF 0 x :=
begin
  change (p.ψ.inv_fun (F t (p.φ x)).1.2,
    ((p.ψ.fderiv (p.ψ.inv_fun (F t (p.φ x)).1.2)).symm :
      tangent_space I' (p.ψ (p.ψ.inv_fun (F t (p.φ x)).1.2)) →L[ℝ]
    tangent_space 𝓘(ℝ, E') (p.ψ.inv_fun (F t ((p.φ) x)).1.2)) ∘L (F t (p.φ x)).2 ∘L _) = _,
  rw [h],
  refl,
end

lemma htpy_formal_sol.localize_eq_of_eq' (F : htpy_formal_sol R) (hF : p.accepts F)
  {t t'} (h : F t = F t') :
  F.localize p hF t = F.localize p hF t' :=
begin
  ext x,
  change p.ψ.inv_fun (F t (p.φ x)).1.2 = _,
  rw [h],
  refl,
  ext1 x,
  change ((p.ψ.fderiv (p.ψ.inv_fun (F t (p.φ x)).1.2)).symm :
      tangent_space I' (p.ψ (p.ψ.inv_fun (F t (p.φ x)).1.2)) →L[ℝ]
    tangent_space 𝓘(ℝ, E') (p.ψ.inv_fun (F t ((p.φ) x)).1.2)) ∘L (F t (p.φ x)).2 ∘L _ = _,
  rw [h],
  refl
end

variables (F : htpy_formal_sol R)
  (𝓕 : (R.localize p.φ p.ψ).rel_loc.htpy_formal_sol)

structure chart_pair.compat : Prop :=
(hF : p.accepts F)
(hFF : ∀ t, ∀ x ∉ p.K₁, 𝓕 t x = F.localize p hF t x)

def rel_loc.htpy_formal_sol.unloc : htpy_formal_sol (rel_mfld.localize p.φ p.ψ R) :=
{ is_sol' := 𝓕.is_sol,
  ..𝓕.to_htpy_jet_sec.unloc}

lemma rel_loc.htpy_formal_sol.unloc_congr {𝓕 𝓕' : (R.localize p.φ p.ψ).rel_loc.htpy_formal_sol}
  {t t' x} (h : 𝓕 t x = 𝓕' t' x) : 𝓕.unloc p t x = 𝓕'.unloc p t' x :=
begin
  ext1,
  refl,
  change (𝓕 t x).1 = (𝓕' t' x).1,
  rw h,
  change (𝓕 t x).2 = (𝓕' t' x).2,
  rw h
end

@[simp]
lemma htpy_formal_sol.transfer_unloc_localize (hF : p.accepts F) (t : ℝ) (x : E) :
  p.φ.transfer p.ψ ((F.localize p hF).unloc p t x) = F t (p.φ x) :=
transfer_localize (F t).to_one_jet_sec p.φ p.ψ (hF t) x

open_locale classical
variables [t2_space M]

def chart_pair.update (F : htpy_formal_sol R)
  (𝓕 : (R.localize p.φ p.ψ).rel_loc.htpy_formal_sol)
   : htpy_formal_sol R :=
if h : p.compat F 𝓕 then p.φ.update_htpy_formal_sol p.ψ F (𝓕.unloc p) p.hK₁
  (λ t x (hx : x ∉ p.K₁), begin
  rw [← F.transfer_unloc_localize p h.1, rel_loc.htpy_formal_sol.unloc_congr p (h.hFF t x hx).symm],
  refl
  end) else F

lemma chart_pair.update_eq_self (F : htpy_formal_sol R)
  (𝓕 : (R.localize p.φ p.ψ).rel_loc.htpy_formal_sol) {t m}
  (hm : ∀ hF : p.accepts F, ∀ x ∈ p.K₁, m = p.φ x → 𝓕 t x = F.localize p hF t x) :
  p.update F 𝓕 t m = F t m :=
begin
  rw [chart_pair.update],
  split_ifs,
  { refine (p.φ.htpy_Jupdate_apply _ _ _ _ _).trans _,
    rw [open_smooth_embedding.update],
    split_ifs with h',
    { obtain ⟨x, rfl⟩ := h',
      rw [one_jet_bundle.embedding_to_fun, p.φ.left_inv],
      have : (𝓕 t).unloc x = (F t).localize p.φ p.ψ (h.hF t) x,
      { have : 𝓕 t x = F.localize p h.hF t x,
        { by_cases h'' : x ∈ p.K₁,
          { exact hm h.hF x h'' rfl },
          { exact h.hFF t x h'' } },
        rw [prod.ext_iff] at this,
        ext1, refl, exact this.1, dsimp only, exact this.2 },
      change p.φ.transfer p.ψ ((𝓕 t).unloc x) = F t (p.φ x),
      rw [this, transfer_localize],
      refl },
    refl },
  refl,
end

lemma chart_pair.update_eq_of_not_mem (F : htpy_formal_sol R)
  (𝓕 : (R.localize p.φ p.ψ).rel_loc.htpy_formal_sol) {t} {m} (hm : m ∉ p.φ '' p.K₁) :
  p.update F 𝓕 t m = F t m :=
chart_pair.update_eq_self p F 𝓕 $
  by { rintro hF x hx rfl, exfalso, exact hm (mem_image_of_mem _ hx) }

lemma chart_pair.update_eq_of_eq (F : htpy_formal_sol R)
  (𝓕 : (R.localize p.φ p.ψ).rel_loc.htpy_formal_sol) {t x}
   (htx : ∀ hF : p.accepts F, 𝓕 t x = F.localize p hF t x) :
  p.update F 𝓕 t (p.φ x) = F t (p.φ x) :=
chart_pair.update_eq_self p F 𝓕 $
  by { intros hF y hy hyx, obtain rfl := p.φ.injective hyx, exact htx hF }

lemma chart_pair.update_eq_of_eq' (F : htpy_formal_sol R)
  (𝓕 : (R.localize p.φ p.ψ).rel_loc.htpy_formal_sol) (h𝓕 : p.compat F 𝓕) {t t' x}
  (h : 𝓕 t x = F.localize p h𝓕.1 t' x) :
  p.update F 𝓕 t (p.φ x) = F t' (p.φ x) :=
begin
  dsimp only [chart_pair.update],
  split_ifs,
  simp only [open_smooth_embedding.update_htpy_formal_sol_apply_image],
  rw [rel_loc.htpy_formal_sol.unloc_congr p , htpy_formal_sol.transfer_unloc_localize _ _ h𝓕.1],
  exact h
end

lemma chart_pair.update_eq_of_forall (F : htpy_formal_sol R)
  (𝓕 : (R.localize p.φ p.ψ).rel_loc.htpy_formal_sol) {t}
  (heq : ∀ hF : p.accepts F, 𝓕 t = F.localize p hF t) :
  p.update F 𝓕 t = F t :=
formal_sol.coe_inj $ λ m, chart_pair.update_eq_self p F 𝓕 $
    by { rintro hF y hy rfl, by rw heq hF }


lemma chart_pair.update_is_holonomic_at_iff {F : htpy_formal_sol R}
  {𝓕 : (R.localize p.φ p.ψ).rel_loc.htpy_formal_sol} {t e}
  (h : p.compat F 𝓕) : (p.update F 𝓕 t).is_holonomic_at (p.φ e) ↔ (𝓕 t).is_holonomic_at e :=
sorry

lemma chart_pair.update_is_holonomic_at_iff' {F : htpy_formal_sol R}
  {𝓕 : (R.localize p.φ p.ψ).rel_loc.htpy_formal_sol} {t x} (hx : x ∉ p.φ '' p.K₁)
  (h : p.compat F 𝓕) : (p.update F 𝓕 t).is_holonomic_at x ↔ (F t).is_holonomic_at x :=
sorry

lemma chart_pair.dist_update [finite_dimensional ℝ E'] {δ : M → ℝ} (hδ_pos : ∀ x, 0 < δ x)
  (hδ_cont : continuous δ) {F : htpy_formal_sol R} (hF : p.accepts F) :
  ∃ η > (0 : ℝ),
    ∀ {𝓕 : (R.localize p.φ p.ψ).rel_loc.htpy_formal_sol}, ∀ hF𝓕 : p.compat F 𝓕,
    ∀ (e ∈ p.K₁) (t ∈ (Icc 0 1 : set ℝ)), ∥(𝓕 t).f e - (F.localize p hF𝓕.1 1).f e∥ < η →
    dist (((p.update F 𝓕) t).bs $ p.φ e) ((F 1).bs $ p.φ e) < δ (p.φ e) :=
begin
  let bsF := (λ t m, (F t).bs m),
  have : ∀ 𝓕 : (R.localize p.φ p.ψ).rel_loc.htpy_formal_sol, p.compat F 𝓕 → ∀ t e,
    (p.update F 𝓕 t).bs (p.φ e) = p.φ.update p.ψ (bsF t) (λ e, (𝓕.unloc p t).bs e) (p.φ e),
  { -- TODO: this proof needs more lemmas
    intros 𝓕 h𝓕 t e,
    change (p.update F 𝓕 t (p.φ e)).1.2 = p.φ.update p.ψ (bsF t) (λ e, (𝓕.unloc p t).bs e) (p.φ e),
    simp only [open_smooth_embedding.update_apply_embedding],
    dsimp only [chart_pair.update],
    rw [dif_pos h𝓕, open_smooth_embedding.update_htpy_formal_sol_apply],
    dsimp only,
    simp only [open_smooth_embedding.update_apply_embedding, one_jet_bundle.embedding_to_fun, open_smooth_embedding.transfer_fst_snd],
    refl },
  rcases p.φ.dist_update' p.ψ p.hK₁ is_compact_Icc (λ t m, (F t).bs m) F.smooth_bs.continuous
    hF.image_subset hδ_pos hδ_cont with ⟨η, η_pos, hη⟩,
  refine ⟨η, η_pos, _⟩,
  intros 𝓕 H e he t ht het,
  simp only [this 𝓕 H], -- clear this,
  rw ← dist_eq_norm at het,
  exact hη (λ t e, (𝓕.unloc p t).bs e) 1 ⟨zero_le_one, le_rfl⟩ t ht e he het,
end
