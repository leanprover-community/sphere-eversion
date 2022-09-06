import local.h_principle

import global.relation
import global.localisation_data

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
def one_jet_sec.loc (F : one_jet_sec 𝓘(ℝ, E) E 𝓘(ℝ, E') E') : rel_loc.jet_sec E E' :=
{ f := F.bs,
  f_diff := F.smooth_bs.cont_diff,
  φ := λ x, (F x).2,
  φ_diff := begin
    rw [cont_diff_iff_cont_diff_at],
    intro x₀,
    have : smooth_at _ _ _ _ := F.smooth x₀,
    simp_rw [smooth_at_one_jet_bundle, in_coordinates, in_coordinates',
      basic_smooth_vector_bundle_core.tangent_space_self_coord_change_at,
      continuous_linear_map.comp_id, continuous_linear_map.id_comp]
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

namespace localisation_data

variables
  {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
  {H : Type*} [topological_space H]
  {I : model_with_corners ℝ E H}
  {M : Type*} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
  {E' : Type*} [normed_add_comm_group E'] [normed_space ℝ E']
  {H' : Type*} [topological_space H']
  {I' : model_with_corners ℝ E' H'}
  {M' : Type*} [metric_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M']

variables {f : M → M'} {R : rel_mfld I M I' M'}

variables (L : localisation_data I I' f) (F : formal_sol R) (i : L.ι)
  (hFL : range (F.bs ∘ (L.φ i)) ⊆ range (L.ψj i))

def loc_rel (R : rel_mfld I M I' M') : rel_loc E E' :=
(R.localize (L.φ i) (L.ψj i)).rel_loc

lemma is_open_loc_rel (h : is_open R) : is_open (L.loc_rel i R) :=
is_open_of_is_open _ $ h.preimage $ one_jet_bundle.continuous_transfer _ _

lemma is_ample (h : R.ample) : (L.loc_rel i R).is_ample :=
ample_of_ample _ (h.localize _ _)

def landscape [finite_dimensional ℝ E] {A : set M} (hA : is_closed A)
  (n : ℕ) : landscape E :=
{ C := (L.φ n) ⁻¹' (A ∪ ⋃ i < L.index n, (L.φ i) '' metric.closed_ball 0 1), -- CHECK this is correct
  K₀ := metric.closed_ball 0 1,
  K₁ := metric.closed_ball 0 2,
  hC := sorry,
  hK₀ := is_compact_closed_ball 0 1,
  hK₁ := is_compact_closed_ball 0 2,
  h₀₁ := sorry }

/-
FIXME: the next definition in progress should probably use
`transfer F.to_one_jet_sec (L.ψj i) (L.φ i) hFL` instead of going back to
`one_jet_sec.localize`
-/

/-- Turn a global formal solution into a local one using some localisation data. -/
def loc_formal_sol {F : formal_sol R}
  {i : L.ι} (hFL : range (F.bs ∘ (L.φ i)) ⊆ range (L.ψj i)) :
  rel_loc.formal_sol (R.localize (L.φ i) (L.ψj i)).rel_loc :=
{ is_sol := sorry,
  ..(F.localize (L.φ i) (L.ψj i) hFL).loc }

/-- Turn a global homotopy of formal solutions into a local one using some localisation data. -/
def loc_htpy_formal_sol {𝓕 : htpy_formal_sol R}
  {i : L.ι} (h𝓕L : ∀ t, range ((𝓕 t).bs ∘ (L.φ i)) ⊆ range (L.ψj i)) :
  (L.loc_rel i R).htpy_formal_sol :=
sorry

def Id := open_smooth_embedding.id 𝓘(ℝ, ℝ) ℝ

def update_htpy_jet_sec (F : htpy_one_jet_sec I M I' M') (𝓕 : htpy_jet_sec E E') :
  htpy_one_jet_sec I M I' M' :=
{ bs := curry $ (Id.prod (L.φ i)).update (L.ψj i) (uncurry F.bs) (uncurry 𝓕.f),
  ϕ := λ t m, sorry,
  smooth' := sorry }

section
variable (hF :  range (F.bs ∘ (L.φ i)) ⊆ range (L.ψj i))

#check L.loc_formal_sol hF
#check (L.φ i).update_formal_sol (L.ψj i) F
#check (L.φ i).update (L.ψj i) F.bs
#check (L.φ i).Jupdate (L.ψj i) F.to_one_jet_sec

end

def unloc_htpy_jet_sec (i : L.ι) (𝓕 : htpy_jet_sec E E') : htpy_one_jet_sec I M I' M' :=
/- htpy_one_jet_sec.unlocalize (L.ψj i) (L.φ i)
{ bs := λ t e, 𝓕.f t e,
  ϕ := λ t e, 𝓕.φ t e,
  smooth' := sorry } -/sorry

/-- Turn a local homotopy of formal solutions into a global one using some localisation data. -/
def unloc_htpy_formal_sol (i : L.ι) (𝓕 : (L.loc_rel i R).htpy_formal_sol) : htpy_formal_sol R :=
{ is_sol' := sorry,
  ..L.unloc_htpy_jet_sec i 𝓕.to_htpy_jet_sec }

lemma unloc_loc {i : L.ι} {𝓕 : (L.loc_rel i R).htpy_formal_sol} {F₀ : formal_sol R}
  (hF₀ :  range (F₀.bs ∘ (L.φ i)) ⊆ range (L.ψj i)) (h : 𝓕 0 = L.loc_formal_sol hF₀) :
  L.unloc_htpy_formal_sol i 𝓕 0 = F₀ :=
sorry

lemma foobar {i : L.ι} {𝓕 : (L.loc_rel i R).htpy_formal_sol} {F₀ : formal_sol R}
  (hF₀ :  range (F₀.bs ∘ (L.φ i)) ⊆ range (L.ψj i)) {A : set M} {C : set E}
  (hAC : (L.φ i) ⁻¹' A ⊆ C)
  (h : ∀ᶠ x near C, ∀ (t : ℝ), 𝓕 t x = L.loc_formal_sol hF₀ x) :
  ∀ (t : ℝ), ∀ᶠ (x : M) near A, L.unloc_htpy_formal_sol i 𝓕 t x = F₀ x :=
sorry

lemma barbaz {i : L.ι} {𝓕 : (L.loc_rel i R).htpy_formal_sol} {F₀ : formal_sol R}
  (hF₀ :  range (F₀.bs ∘ (L.φ i)) ⊆ range (L.ψj i)) {A : set M} {C : set E}
  (hAC : (L.φ i) ⁻¹' A ⊆ C)
  (h : ∀ᶠ x near C, (𝓕 1).is_holonomic_at x) :
  ∀ᶠ (x : M) near A, (L.unloc_htpy_formal_sol i 𝓕 1).is_holonomic_at x :=
sorry

lemma barbaz' {i : L.ι} {𝓕 : (L.loc_rel i R).htpy_formal_sol} {F₀ : formal_sol R}
  (hF₀ :  range (F₀.bs ∘ (L.φ i)) ⊆ range (L.ψj i)) {A : set M} {C : set E}
  (hAC : (L.φ i) ⁻¹' A ⊆ C)
  (h : ∀ᶠ x near C, (𝓕 1).is_holonomic_at x) :
  ∀ x ∈ A, (L.unloc_htpy_formal_sol i 𝓕 1).is_holonomic_at x :=
(barbaz L hF₀ hAC h).nhds_set_forall_mem

end localisation_data
