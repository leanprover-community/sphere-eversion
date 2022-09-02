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
  f_diff := sorry,
  φ := λ x, (F x).2,
  φ_diff := sorry }

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
(equiv.prod_assoc _ _ _) '' ((one_jet_bundle_model_space_homeomorph E 𝓘(ℝ, E) E' 𝓘(ℝ, E')) '' R)

lemma ample_of_ample (R : rel_mfld 𝓘(ℝ, E) E 𝓘(ℝ, E') E') (hR : R.ample) :
  R.rel_loc.is_ample :=
sorry

lemma is_open_of_is_open (R : rel_mfld 𝓘(ℝ, E) E 𝓘(ℝ, E') E') (hR : is_open R) :
  is_open R.rel_loc :=
sorry

end loc

section localisation_data
variables
  {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
  {H : Type*} [topological_space H]
  {I : model_with_corners ℝ E H}
  {M : Type*} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
  {E' : Type*} [normed_add_comm_group E'] [normed_space ℝ E']
  {H' : Type*} [topological_space H']
  {I' : model_with_corners ℝ E' H'}
  {M' : Type*} [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M']

/-
structure localisation_data (f : M → M') :=
(ι' : Type*)
(N : ℕ)
(φ : index_type N → open_smooth_embedding 𝓘(𝕜, E) E I M)
(ψ : ι' → open_smooth_embedding 𝓘(𝕜, E') E' I' M')
(j : index_type N → ι')
(h₁ : (⋃ i, (φ i) '' (ball (0:E) 1)) = univ)
(h₂ : (⋃ i', (ψ i') '' (ball (0:E') 1)) = univ)
(h₃ : ∀ i, range (f ∘ (φ i)) ⊆ (ψ (j i)) '' (ball (0:E') 1))
(h₄ : locally_finite $ λ i', range (ψ i'))
(lf_φ : locally_finite $ λ i, range (φ i))
-/


variables {f : M → M'} {R : rel_mfld I M I' M'}

variables (L : localisation_data I I' f) (F : formal_sol R) (i : L.ι)
  (hFL : range (F.bs ∘ (L.φ i)) ⊆ range (L.ψj i))

def localisation_data.loc_rel (R : rel_mfld I M I' M') : _ :=
(R.localize (L.ψj i) (L.φ i)).rel_loc

lemma localisation_data.is_open_loc_rel (h : is_open R) : is_open (L.loc_rel i R) :=
sorry

lemma localisation_data.is_ample (h : R.ample) : (L.loc_rel i R).is_ample :=
sorry

def localisation_data.landscape [finite_dimensional ℝ E] {A : set M} (hA : is_closed A)
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
def localisation_data.loc_formal_sol (L : localisation_data I I' f) {F : formal_sol R}
  {i : L.ι} (hFL : range (F.bs ∘ (L.φ i)) ⊆ range (L.ψj i)) :
  rel_loc.formal_sol (R.localize (L.ψj i) (L.φ i)).rel_loc :=
{ is_sol := sorry,
  ..(F.to_one_jet_sec.localize (L.ψj i) (L.φ i) hFL).loc }

/-- Turn a global homotopy of formal solutions into a local one using some localisation data. -/
def localisation_data.loc_htpy_formal_sol (L : localisation_data I I' f) {F : htpy_formal_sol R}
  {i : L.ι} (hFL : ∀ t, range ((F t).bs ∘ (L.φ i)) ⊆ range (L.ψj i)) :
  (L.loc_rel i R).htpy_formal_sol :=
sorry

/-
FIXME: There is a mismatch because the global story has a bundled `htpy_formal_sol` and
the local one hasn't. The local story only has `htpy_jet_sec` and `is_formal_sol`.
-/

/-
FIXME: the next definition probably misses side conditions.
-/

/-- Turn a local homotopy of formal solutions into a global one using some localisation data. -/
def localisation_data.unloc_htpy_formal_sol (L : localisation_data I I' f) (i : L.ι)
  (F : (L.loc_rel i R).htpy_formal_sol) :
  htpy_formal_sol R :=
sorry

end localisation_data
