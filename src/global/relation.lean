import local.relation
import global.one_jet_sec
import global.smooth_embedding

noncomputable theory

open set function filter charted_space smooth_manifold_with_corners
open_locale topological_space manifold

/-!
# First order partial differential relations for maps between manifolds

This file contains fundamental definitions about first order partial differential relations
for maps between manifolds and relating them to the local story of first order partial differential
relations for maps between vector spaces.

Given manifolds `M` and `M'` modelled on `I` and `I'`, a first order partial differential relation
for maps from `M` to `M'` is a set in the 1-jet bundle J¹(M, M'), also known as
`one_jet_bundle I M I' M'`.


-/

section defs
/-! ## Fundamental definitions -/

variables
{E : Type*} [normed_group E] [normed_space ℝ E]
{H : Type*} [topological_space H] (I : model_with_corners ℝ E H)
(M : Type*) [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
{E' : Type*} [normed_group E'] [normed_space ℝ E']
{H' : Type*} [topological_space H'] (I' : model_with_corners ℝ E' H')
(M' : Type*) [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M']

local notation `TM` := tangent_space I
local notation `TM'` := tangent_space I'

def rel_mfld := set (one_jet_bundle I M I' M')

instance : has_mem (one_jet_bundle I M I' M') (rel_mfld I M I' M') := set.has_mem

variables {I M I' M'}

/-- A solution to a relation `R`. -/
@[ext] structure sol (R : rel_mfld I M I' M') :=
(f : M → M')
(f_diff : cont_mdiff I I' ⊤ f)
(is_sol : ∀ x, one_jet_ext I I' f x ∈ R)

/-- A formal solution to a local relation `R` over a set `U`. -/
@[ext] structure formal_sol (R : rel_mfld I M I' M') extends one_jet_sec I M I' M' :=
(is_sol' : ∀ x, to_fun x ∈ R)

instance (R : rel_mfld I M I' M') :
  has_coe_to_fun (formal_sol R) (λ S, M → one_jet_bundle I M I' M'):=
⟨λ F, F.to_one_jet_sec.to_fun⟩

lemma formal_sol.is_sol {R : rel_mfld I M I' M'} (F : formal_sol R) : ∀ x, F x ∈ R :=
F.is_sol'

def rel_mfld.slice (R : rel_mfld I M I' M') (σ : one_jet_bundle I M I' M')
  (p : dual_pair' $ TM σ.1.1) : set (TM' σ.1.2) :=
{w | (⟨⟨σ.1.1, σ.1.2⟩, p.update σ.2 w⟩ : one_jet_bundle I M I' M') ∈ R}

def rel_mfld.ample (R : rel_mfld I M I' M') : Prop :=
∀ (σ : one_jet_bundle I M I' M') (p  : dual_pair' $ TM σ.1.1), ample_set (R.slice σ p)

end defs

section smooth_open_embedding
/-! ## Localisation of one jet sections

In order to use the local story of convex integration, we need a way to turn a
one jet section into local ones, then apply the local story to build a homotopy of one jets section
and transfer back to the original manifolds. There is a dissymetry here. First we use
maps from whole vector spaces to open sets in manifold. And also one jet sections are carried
from manifold to vector spaces one at a time, but then the return journey is about a homotopy
of one jet sections.

The global manifolds are called `M` and `N'`. We don't assume the local ones are vector spaces,
there are manifolds `X` and `Y` that will be vector spaces in the next section.

Note: Patrick doesn't know whether we really need to allow different `E`, `H` and `I` for
manifolds `X` and `M` (and for `Y` and `N`). We use maximal generality just in case.
-/
variables
  {EX : Type*} [normed_group EX] [normed_space ℝ EX]
  {HX : Type*} [topological_space HX] {IX : model_with_corners ℝ EX HX}
  {X : Type*} [topological_space X] [charted_space HX X] [smooth_manifold_with_corners IX X]

  {EM : Type*} [normed_group EM] [normed_space ℝ EM]
  {HM : Type*} [topological_space HM] {IM : model_with_corners ℝ EM HM}
  {M : Type*} [topological_space M] [charted_space HM M] [smooth_manifold_with_corners IM M]

  {EY : Type*} [normed_group EY] [normed_space ℝ EY]
  {HY : Type*} [topological_space HY] {IY : model_with_corners ℝ EY HY}
  {Y : Type*} [topological_space Y] [charted_space HY Y] [smooth_manifold_with_corners IY Y]

  {EN : Type*} [normed_group EN] [normed_space ℝ EN]
  {HN : Type*} [topological_space HN] {IN : model_with_corners ℝ EN HN}
  {N : Type*} [topological_space N] [charted_space HN N] [smooth_manifold_with_corners IN N]

  (g : open_smooth_embedding IY Y IN N) (h : open_smooth_embedding IX X IM M)

local notation `TM` := tangent_space IM
local notation `TN` := tangent_space IN
local notation `TX` := tangent_space IX
local notation `TY` := tangent_space IY

/-- Transfer map between one jet bundles induced by open smooth embedding into the source and
targets. -/
def one_jet_bundle.transfer : one_jet_bundle IX X IY Y → one_jet_bundle IM M IN N :=
λ σ, ⟨⟨h σ.1.1, g σ.1.2⟩,
      ((g.fderiv σ.1.2 : TY σ.1.2 →L[ℝ] TN (g σ.1.2)).comp σ.2).comp
        ((h.fderiv σ.1.1).symm : TM (h σ.1.1) →L[ℝ] TX σ.1.1)⟩

lemma one_jet_bundle.continuous_transfer : continuous (one_jet_bundle.transfer g h) :=
sorry

/-- Localize a one-jet section in two open embeddings. -/
def one_jet_sec.localize (F : one_jet_sec IM M IN N) : one_jet_sec IX X IY Y :=
{ to_fun := λ x, ⟨⟨x, g.inv_fun (F $ h x).1.2⟩,
    ((g.fderiv $ g.inv_fun (F $ h x).1.2).symm : TN (g (g.inv_fun (F (h x)).1.2)) →L[ℝ]
      TY (g.inv_fun (F (h x)).1.2)) ∘L ((F $ h x).2 ∘L (h.fderiv x : TX x →L[ℝ] TM (h x)))⟩,
  is_sec' := sorry,
  smooth' := sorry }

/-- Un-localize a homotopy of one-jet sections from two open embeddings. -/
def htpy_one_jet_sec.unlocalize (F : htpy_one_jet_sec IX X  IY Y) : htpy_one_jet_sec IM M IN N :=
{ to_fun := λ t m, ⟨⟨m, g (F t (h.inv_fun m)).1.2⟩,
    (g.fderiv (F t (h.inv_fun m)).1.2).to_continuous_linear_map ∘L
      ((F t $ h.inv_fun m).2 ∘L (h.fderiv $ h.inv_fun m).symm.to_continuous_linear_map)⟩,
  is_sec' := sorry,
  smooth' := sorry }

lemma one_jet_sec.unlocalize_localize (F : one_jet_sec IM M IN N) (G : htpy_one_jet_sec IX X  IY Y)
  (hFG : G 0 = F.localize g h) : G.unlocalize g h 0 = F :=
sorry

lemma localize_mem_iff (F : one_jet_sec IM M IN N) (x : X) (R : rel_mfld IM M IN N) :
  F (h x) ∈ R ↔ F.localize g h x ∈ (one_jet_bundle.transfer g h) ⁻¹' R :=
sorry

lemma localize_ample (R : rel_mfld IM M IN N) (hR : R.ample) :
 rel_mfld.ample ((one_jet_bundle.transfer g h) ⁻¹' R) :=
sorry

end smooth_open_embedding

section loc
/-! ## Link with the local story

Now we really bridge the gap all the way to vector spaces.
-/

variables {E : Type*} [normed_group E] [normed_space ℝ E]
variables {E' : Type*} [normed_group E'] [normed_space ℝ E']

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
