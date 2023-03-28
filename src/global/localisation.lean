import local.ample_relation
import global.relation

set_option trace.filter_inst_type true

/-! # Link with the local story

This file bridges the gap between Chapter 2 and Chapter 3. It builds on the
`smooth_embbeding` file but goes all the way to vector spaces (the previous file
is about embedding any manifold into another one).
-/

noncomputable theory

open set function filter (hiding map_smul) charted_space smooth_manifold_with_corners
open_locale topology manifold

section loc
/-! ## Localizing relations and 1-jet sections

Now we really bridge the gap all the way to vector spaces.
-/

variables {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
variables {E' : Type*} [normed_add_comm_group E'] [normed_space ℝ E']

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
    simp_rw [smooth_at_one_jet_bundle, in_coordinates_core, in_coordinates_core',
      tangent_bundle_core_index_at, tangent_bundle.coord_change_at_self,
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
    simp_rw [in_coordinates_core_model_space],
    exact 𝓕.φ_diff.cont_mdiff a
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
    dsimp [in_coordinates_core, in_coordinates_core', chart_at],
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

variable (p)

def formal_sol.localize (F : formal_sol R) (hF : range (F.bs ∘ p.φ) ⊆ range p.ψ) :
  (R.localize p.φ p.ψ).rel_loc.formal_sol :=
{ is_sol := λ x, (F.localize_mem_iff p.φ p.ψ hF).mpr (F.is_sol _),
  ..(F.localize p.φ p.ψ hF).loc }

lemma formal_sol.is_holonomic_localize (F : formal_sol R) (hF : range (F.bs ∘ p.φ) ⊆ range p.ψ)
  (x) (hx : F.is_holonomic_at (p.φ x)) : (F.localize p hF).is_holonomic_at x :=
(one_jet_sec.loc_hol_at_iff _ _).mpr $
  (is_holonomic_at_localize_iff F.to_one_jet_sec p.φ p.ψ hF x).mpr hx

variables (F : htpy_formal_sol R)
  (𝓕 : (R.localize p.φ p.ψ).rel_loc.htpy_formal_sol)

structure chart_pair.compat' (F : formal_sol R)
  (𝓕 : (R.localize p.φ p.ψ).rel_loc.htpy_formal_sol) : Prop :=
(hF : range (F.bs ∘ p.φ) ⊆ range p.ψ)
(hFF : ∀ x ∉ p.K₁, ∀ t, 𝓕 t x = F.localize p hF x)


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

lemma rel_loc.htpy_formal_sol.unloc_congr_const {𝓕 : (R.localize p.φ p.ψ).rel_loc.htpy_formal_sol}
  {𝓕' : (R.localize p.φ p.ψ).rel_loc.formal_sol}
  {t x} (h : 𝓕 t x = 𝓕' x) : 𝓕.unloc p t x = 𝓕'.unloc x :=
begin
  ext1,
  refl,
  change (𝓕 t x).1 = (𝓕' x).1,
  rw h,
  change (𝓕 t x).2 = (𝓕' x).2,
  rw h
end

lemma rel_loc.htpy_formal_sol.unloc_congr' {𝓕 𝓕' : (R.localize p.φ p.ψ).rel_loc.htpy_formal_sol}
  {t t'} (h : 𝓕 t = 𝓕' t') : 𝓕.unloc p t = 𝓕'.unloc p t' :=
begin
  apply formal_sol.coe_inj,
  intro x,
  apply rel_loc.htpy_formal_sol.unloc_congr,
  rw h,
end

@[simp]
lemma formal_sol.transfer_unloc_localize (F : formal_sol R)
  (hF : range (F.bs ∘ p.φ) ⊆ range p.ψ) (x : E) :
  p.φ.transfer p.ψ ((F.localize p hF).unloc x) = F (p.φ x) :=
transfer_localize F.to_one_jet_sec p.φ p.ψ hF x

open_locale classical
variables [t2_space M]

def chart_pair.mk_htpy (F : formal_sol R)
  (𝓕 : (R.localize p.φ p.ψ).rel_loc.htpy_formal_sol)
   : htpy_formal_sol R :=
if h : p.compat' F 𝓕 then p.φ.update_formal_sol p.ψ F (𝓕.unloc p) p.hK₁
  (λ t x (hx : x ∉ p.K₁), begin
  rw [← F.transfer_unloc_localize p h.1, rel_loc.htpy_formal_sol.unloc_congr_const p (h.hFF x hx t)],
  refl,
  end) else F.const_htpy

lemma chart_pair.mk_htpy_congr (F : formal_sol R)
  {𝓕 : (R.localize p.φ p.ψ).rel_loc.htpy_formal_sol} {t t' : ℝ} (h : 𝓕 t = 𝓕 t') :
  p.mk_htpy F 𝓕 t = p.mk_htpy F 𝓕 t' :=
begin
  unfold chart_pair.mk_htpy,
  by_cases hF : p.compat' F 𝓕,
  { simp only [dif_pos hF],
    apply formal_sol.coe_inj,
    intro x,
    rw [p.φ.update_formal_sol_apply, p.φ.update_formal_sol_apply,
        rel_loc.htpy_formal_sol.unloc_congr' p h] },
  { simp only [dif_neg hF], refl },
end

lemma chart_pair.mk_htpy_eq_self (F : formal_sol R)
  (𝓕 : (R.localize p.φ p.ψ).rel_loc.htpy_formal_sol) {t m}
  (hm : ∀ hF : range (F.bs ∘ p.φ) ⊆ range p.ψ, ∀ x ∈ p.K₁, m = p.φ x → 𝓕 t x = F.localize p hF x) :
  p.mk_htpy F 𝓕 t m = F m :=
begin
  rw [chart_pair.mk_htpy],
  split_ifs,
  { refine (p.φ.Jupdate_apply _ _ _ _ _).trans _,
    rw [open_smooth_embedding.update],
    split_ifs with h',
    { obtain ⟨x, rfl⟩ := h',
      rw [one_jet_bundle.embedding_to_fun, p.φ.left_inv],
      have : (𝓕 t).unloc x = F.to_one_jet_sec.localize p.φ p.ψ h.hF x,
      { have : 𝓕 t x = F.localize p h.hF x,
        { by_cases h'' : x ∈ p.K₁,
          { exact hm h.hF x h'' rfl },
          { exact h.hFF x h'' t } },
        rw [prod.ext_iff] at this,
        ext1, refl, exact this.1, dsimp only, exact this.2 },
      change p.φ.transfer p.ψ ((𝓕 t).unloc x) = F (p.φ x),
      rw [this, transfer_localize],
      refl },
    refl },
  refl,
end

lemma chart_pair.mk_htpy_eq_of_not_mem (F : formal_sol R)
  (𝓕 : (R.localize p.φ p.ψ).rel_loc.htpy_formal_sol) {t} {m} (hm : m ∉ p.φ '' p.K₁) :
  p.mk_htpy F 𝓕 t m = F m :=
chart_pair.mk_htpy_eq_self p F 𝓕 $
  by { rintro hF x hx rfl, exfalso, exact hm (mem_image_of_mem _ hx) }

lemma chart_pair.mk_htpy_eq_of_eq (F : formal_sol R)
  (𝓕 : (R.localize p.φ p.ψ).rel_loc.htpy_formal_sol) (h𝓕 : p.compat' F 𝓕) {t x}
  (h : 𝓕 t x = F.localize p h𝓕.1 x) :
  p.mk_htpy F 𝓕 t (p.φ x) = F (p.φ x) :=
begin
  dsimp only [chart_pair.mk_htpy],
  split_ifs,
  simp only [open_smooth_embedding.update_formal_sol_apply_image],
  rw [rel_loc.htpy_formal_sol.unloc_congr_const p, formal_sol.transfer_unloc_localize p F h𝓕.1 x],
  exact h,
end

lemma chart_pair.mk_htpy_eq_of_forall {F : formal_sol R}
  {𝓕 : (R.localize p.φ p.ψ).rel_loc.htpy_formal_sol} (h𝓕 : p.compat' F 𝓕) {t}
  (h : 𝓕 t = F.localize p h𝓕.1) :
  p.mk_htpy F 𝓕 t = F :=
formal_sol.coe_inj $ λ m, chart_pair.mk_htpy_eq_self p F 𝓕 $
    by { rintro hF y hy rfl, by { rw h, refl } }

lemma chart_pair.mk_htpy_localize {F : formal_sol R}
  {𝓕 : (R.localize p.φ p.ψ).rel_loc.htpy_formal_sol} {t e}
  (h : p.compat' F 𝓕) (rg : range ((p.mk_htpy F 𝓕 t).bs ∘ p.φ) ⊆ range p.ψ) :
  (p.mk_htpy F 𝓕 t).to_one_jet_sec.localize p.φ p.ψ rg e = (𝓕 t).unloc e :=
begin
  simp_rw [chart_pair.mk_htpy, dif_pos h] at rg ⊢,
  exact p.φ.Jupdate_localize p.ψ _ _ t rg e
end

lemma chart_pair.mk_htpy_is_holonomic_at_iff {F : formal_sol R}
  {𝓕 : (R.localize p.φ p.ψ).rel_loc.htpy_formal_sol} (h : p.compat' F 𝓕) {t e} :
  (p.mk_htpy F 𝓕 t).is_holonomic_at (p.φ e) ↔ (𝓕 t).is_holonomic_at e :=
begin
  have rg : range ((p.mk_htpy F 𝓕 t).bs ∘ p.φ) ⊆ range p.ψ,
  { rintros - ⟨e, rfl⟩,
    dsimp only [chart_pair.mk_htpy],
    simp only [dif_pos h],
    rw p.φ.update_formal_sol_bs p.ψ p.hK₁,
    simp only [comp_app, open_smooth_embedding.update_apply_embedding, mem_range_self] },
  rw [← is_holonomic_at_localize_iff _ p.φ p.ψ rg e,
      ← jet_sec.unloc_hol_at_iff],
  exact one_jet_sec.is_holonomic_at_congr (eventually_of_forall $ λ e, p.mk_htpy_localize h rg)
end

lemma chart_pair.dist_update' [finite_dimensional ℝ E'] {δ : M → ℝ} (hδ_pos : ∀ x, 0 < δ x)
  (hδ_cont : continuous δ) {F : formal_sol R} (hF : range (F.bs ∘ p.φ) ⊆ range p.ψ) :
  ∃ η > (0 : ℝ),
    ∀ {𝓕 : (R.localize p.φ p.ψ).rel_loc.htpy_formal_sol}, ∀ hF𝓕 : p.compat' F 𝓕,
    ∀ (e ∈ p.K₁) (t ∈ (Icc 0 1 : set ℝ)), ‖(𝓕 t).f e - (F.localize p hF).f e‖ < η →
    dist (((p.mk_htpy F 𝓕) t).bs $ p.φ e) (F.bs $ p.φ e) < δ (p.φ e) :=
begin
  let bsF := (λ m, F.bs m),
  have : ∀ 𝓕 : (R.localize p.φ p.ψ).rel_loc.htpy_formal_sol, p.compat' F 𝓕 → ∀ t e,
    (p.mk_htpy F 𝓕 t).bs (p.φ e) = p.φ.update p.ψ bsF (λ e, (𝓕.unloc p t).bs e) (p.φ e),
  { -- TODO: this proof needs more lemmas
    intros 𝓕 h𝓕 t e,
    change (p.mk_htpy F 𝓕 t (p.φ e)).1.2 = p.φ.update p.ψ bsF (λ e, (𝓕.unloc p t).bs e) (p.φ e),
    simp only [open_smooth_embedding.update_apply_embedding],
    dsimp only [chart_pair.mk_htpy],
    rw [dif_pos h𝓕, open_smooth_embedding.update_formal_sol_apply],
    dsimp only,
    simp_rw [open_smooth_embedding.update_apply_embedding, one_jet_bundle.embedding_to_fun,
      open_smooth_embedding.transfer_fst_snd],
    refl },
  rcases p.φ.dist_update p.ψ p.hK₁ (is_compact_Icc : is_compact (Icc 0 1 : set ℝ)) (λ t m, F.bs m)
    (F.smooth_bs.continuous.comp continuous_snd) (λ t, (range_comp bsF p.φ) ▸ hF) hδ_pos hδ_cont
    with ⟨η, η_pos, hη⟩,
  refine ⟨η, η_pos, _⟩,
  intros 𝓕 H e he t ht het,
  simp only [this 𝓕 H], clear this,
  rw ← dist_eq_norm at het,
  exact hη (λ t e, (𝓕.unloc p t).bs e) 1 ⟨zero_le_one, le_rfl⟩ t ht e he het
end
