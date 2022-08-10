import local.relation
import global.one_jet_sec
import global.smooth_embedding
import to_mathlib.topology.algebra.module

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

We also define
* `one_jet_ext I I' f`: the 1-jet extension of a map `f : M → M'`


-/

section defs
/-! ## Fundamental definitions -/

variables
{E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
{H : Type*} [topological_space H] (I : model_with_corners ℝ E H)
(M : Type*) [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
{E' : Type*} [normed_add_comm_group E'] [normed_space ℝ E']
{H' : Type*} [topological_space H'] (I' : model_with_corners ℝ E' H')
(M' : Type*) [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M']
{F : Type*} [normed_add_comm_group F] [normed_space ℝ F]
{G : Type*} [topological_space G] (J : model_with_corners ℝ F G)
(N : Type*) [topological_space N] [charted_space G N] [smooth_manifold_with_corners J N]
{F' : Type*} [normed_add_comm_group F'] [normed_space ℝ F']
{G' : Type*} [topological_space G'] (J' : model_with_corners ℝ F' G')
(N' : Type*) [topological_space N'] [charted_space G' N'] [smooth_manifold_with_corners J' N']

local notation `TM` := tangent_space I
local notation `TM'` := tangent_space I'

/-- A first-order differential relation for maps from `M` to `N` is a subset of the 1-jet bundle. -/
def rel_mfld := set (one_jet_bundle I M I' M')

instance : has_mem (one_jet_bundle I M I' M') (rel_mfld I M I' M') := set.has_mem

variables {I M I' M'} {R : rel_mfld I M I' M'}

/-- A solution to a relation `R`. -/
@[ext] structure sol (R : rel_mfld I M I' M') :=
(f : M → M')
(f_diff : cont_mdiff I I' ⊤ f)
(is_sol : ∀ x, one_jet_ext I I' f x ∈ R)

/-- A formal solution to a local relation `R` over a set `U`. -/
@[ext] structure formal_sol (R : rel_mfld I M I' M') extends one_jet_sec I M I' M' :=
(is_sol' : ∀ x : M, to_fun x ∈ R)

instance (R : rel_mfld I M I' M') :
  has_coe_to_fun (formal_sol R) (λ S, M → one_jet_bundle I M I' M') :=
⟨λ F, F.to_one_jet_sec⟩

lemma formal_sol.is_sol (F : formal_sol R) : ∀ x, F x ∈ R :=
F.is_sol'

def rel_mfld.slice (R : rel_mfld I M I' M') (σ : one_jet_bundle I M I' M')
  (p : dual_pair' $ TM σ.1.1) : set (TM' σ.1.2) :=
connected_comp_in {w | (⟨⟨σ.1.1, σ.1.2⟩, p.update σ.2 w⟩ : one_jet_bundle I M I' M') ∈ R} (σ.2 p.v)

def rel_mfld.ample (R : rel_mfld I M I' M') : Prop :=
∀ (σ : one_jet_bundle I M I' M') (p : dual_pair' $ TM σ.1.1), ample_set (R.slice σ p)

/-- A family of formal solutions indexed by manifold `N` is a function from `N` into formal
  solutions in such a way that the function is smooth as a function of all arguments. -/
structure family_formal_sol (R : rel_mfld I M I' M') extends family_one_jet_sec I M I' M' J N :=
(is_sol' : ∀ (t : N) (x : M), to_fun t x ∈ R)

instance : has_coe_to_fun (family_formal_sol J N R) (λ S, N → formal_sol R) :=
⟨λ S t, ⟨S.to_family_one_jet_sec t, S.is_sol' t⟩⟩

namespace family_formal_sol

variables {J N J' N'}

/-- Reindex a family along a smooth function `f`. -/
def reindex (S : family_formal_sol J' N' R) (f : C^∞⟮J, N; J', N'⟯) :
  family_formal_sol J N R :=
⟨S.to_family_one_jet_sec.reindex f, λ t, S.is_sol' (f t)⟩

end family_formal_sol

/-- A homotopy of formal solutions is a family indexed by `ℝ` -/
@[reducible] def htpy_formal_sol (R : rel_mfld I M I' M') := family_formal_sol 𝓘(ℝ, ℝ) ℝ R

/-- A relation `R` satisfies the (non-parametric) h-principle if all its formal solutions are
homotopic to a holonomic one. -/
def rel_mfld.satisfies_h_principle (R : rel_mfld I M I' M') : Prop :=
∀ 𝓕₀ : formal_sol R, ∃ 𝓕 : htpy_formal_sol R, 𝓕 0 = 𝓕₀ ∧ (𝓕 1).to_one_jet_sec.is_holonomic

/-- A relation `R` satisfies the parametric h-principle w.r.t. manifold `N` if for every family of
formal solutions indexed by a manifold with boundary `N` that is holonomic near the boundary `N` is
homotopic to a holonomic one, in such a way that the homotopy is constant near the boundary of `N`.
-/
def rel_mfld.satisfies_h_principle_with (R : rel_mfld I M I' M') : Prop :=
∀ 𝓕₀ : family_formal_sol J N R, (∀ᶠ x in 𝓝ˢ (boundary J N), (𝓕₀ x).to_one_jet_sec.is_holonomic) →
∃ 𝓕 : family_formal_sol (𝓘(ℝ, ℝ).prod J) (ℝ × N) R,
  𝓕.reindex ((cont_mdiff_map.const 0).prod_mk cont_mdiff_map.id) = 𝓕₀ ∧
  (∀ᶠ x in 𝓝ˢ (boundary J N), ∀ t : ℝ, 𝓕 (t, x) = 𝓕₀ x) ∧
  ∀ x, (𝓕 (1, x)).to_one_jet_sec.is_holonomic


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
  {EX : Type*} [normed_add_comm_group EX] [normed_space ℝ EX]
  {HX : Type*} [topological_space HX] {IX : model_with_corners ℝ EX HX}
  {X : Type*} [topological_space X] [charted_space HX X] [smooth_manifold_with_corners IX X]

  {EM : Type*} [normed_add_comm_group EM] [normed_space ℝ EM]
  {HM : Type*} [topological_space HM] {IM : model_with_corners ℝ EM HM}
  {M : Type*} [topological_space M] [charted_space HM M] [smooth_manifold_with_corners IM M]

  {EY : Type*} [normed_add_comm_group EY] [normed_space ℝ EY]
  {HY : Type*} [topological_space HY] {IY : model_with_corners ℝ EY HY}
  {Y : Type*} [topological_space Y] [charted_space HY Y] [smooth_manifold_with_corners IY Y]

  {EN : Type*} [normed_add_comm_group EN] [normed_space ℝ EN]
  {HN : Type*} [topological_space HN] {IN : model_with_corners ℝ EN HN}
  {N : Type*} [topological_space N] [charted_space HN N] [smooth_manifold_with_corners IN N]

  (F : one_jet_sec IM M IN N)
  (g : open_smooth_embedding IY Y IN N) (h : open_smooth_embedding IX X IM M)
  {R : rel_mfld IM M IN N}

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

-- do we need this?
lemma one_jet_bundle.smooth_transfer : smooth ((IX.prod IY).prod 𝓘(ℝ, EX →L[ℝ] EY))
  ((IM.prod IN).prod 𝓘(ℝ, EM →L[ℝ] EN)) (one_jet_bundle.transfer g h) :=
sorry

/-- localize a relation -/
def rel_mfld.localize (R : rel_mfld IM M IN N) : rel_mfld IX X IY Y :=
one_jet_bundle.transfer g h ⁻¹' R

/-- Underlying map of `one_jet_sec.localize`. It maps `x` to `(x, y, (D_y(g))⁻¹ ∘ F_φ(h x) ∘ D_x(h))`
  where `y : M := g⁻¹(F_{bs}(h x))`. -/
@[simps fst_fst fst_snd]
def one_jet_sec.localize_fun : X → one_jet_bundle IX X IY Y :=
λ x, let y := g.inv_fun (F.bs $ h x) in
⟨(x, y), ((g.fderiv y).symm : TN (g y) →L[ℝ] TY y) ∘L
  ((F $ h x).2 ∘L (h.fderiv x : TX x →L[ℝ] TM (h x)))⟩

open basic_smooth_vector_bundle_core
/-- Localize a one-jet section in two open embeddings. -/
@[simps] def one_jet_sec.localize (hF : range (F.bs ∘ h) ⊆ range g) :
  one_jet_sec IX X IY Y :=
{ to_fun := F.localize_fun g h,
  is_sec' := λ x, rfl,
  smooth' := begin
  simp_rw [one_jet_sec.localize_fun, h.fderiv_coe, g.fderiv_symm_coe,
    mfderiv_congr_point (g.right_inv (hF $ mem_range_self _))],
  refine smooth.one_jet_comp IX IN IY IX (λ x', F.bs (h x')) _ _,
  { exact λ x, (g.smooth_at_inv $ hF $ mem_range_self x).one_jet_ext.comp _
      (F.smooth_bs.comp h.smooth_to).cont_mdiff_at },
  exact smooth.one_jet_comp IX IM IN IX h (F.smooth_eta.comp h.smooth_to) h.smooth_to.one_jet_ext
  end }

lemma transfer_localize (hF : range (F.bs ∘ h) ⊆ range g) (x : X) :
  (F.localize g h hF x).transfer g h = F (h x) :=
begin
  rw [one_jet_sec.localize_to_fun, one_jet_sec.localize_fun, one_jet_bundle.transfer],
  ext,
  { simp_rw [F.is_sec] },
  { simp_rw [g.right_inv (hF $ mem_range_self x), one_jet_sec.bs] },
  { apply heq_of_eq, dsimp only, ext v,
    simp_rw [continuous_linear_map.comp_apply, continuous_linear_equiv.coe_coe,
      continuous_linear_equiv.apply_symm_apply] },
end

lemma one_jet_sec.localize_bs (hF : range (F.bs ∘ h) ⊆ range g) :
  (F.localize g h hF).bs = g.inv_fun ∘ F.bs ∘ h :=
rfl

lemma one_jet_sec.localize_mem_iff (hF : range (F.bs ∘ h) ⊆ range g) {x : X} :
  F.localize g h hF x ∈ R.localize g h ↔ F (h x) ∈ R :=
by rw [rel_mfld.localize, mem_preimage, transfer_localize F g h hF]

lemma rel_mfld.ample.localize (hR : R.ample) : (R.localize g h).ample  :=
begin
  rintro x p, --⟨π, v, hπv⟩,
  sorry
end

lemma is_holonomic_at_localize_iff (hF : range (F.bs ∘ h) ⊆ range g) (x : X) :
  (F.localize g h hF).is_holonomic_at x ↔ F.is_holonomic_at (h x)  :=
begin
  have : mfderiv IX IY (g.inv_fun ∘ F.bs ∘ h) x =
    (g.fderiv (g.inv_fun (F.bs (h x)))).symm.to_continuous_linear_map.comp
    ((mfderiv IM IN F.bs (h x)).comp (h.fderiv x).to_continuous_linear_map),
  { have h1 : mdifferentiable_at IN IY g.inv_fun (F.bs (h x)) :=
      (g.smooth_at_inv $ hF $ mem_range_self _).mdifferentiable_at le_top,
    have h2 : mdifferentiable_at IM IN F.bs (h x) :=
      F.smooth_bs.smooth_at.mdifferentiable_at le_top,
    have h3 : mdifferentiable_at IX IM h x :=
      h.smooth_to.smooth_at.mdifferentiable_at le_top,
    rw [mfderiv_comp x h1 (h2.comp x h3), mfderiv_comp x h2 h3,
      ← g.fderiv_symm_coe' (hF $ mem_range_self _)],
    refl, },
  simp_rw [one_jet_sec.is_holonomic_at],
  rw [mfderiv_congr (F.localize_bs g h hF), F.localize_to_fun, this, one_jet_sec.localize_fun],
  simp_rw [← continuous_linear_equiv.coe_def_rev,
    continuous_linear_equiv.cancel_left, continuous_linear_equiv.cancel_right]
end

/-- Underlying map of `htpy_one_jet_sec.unlocalize`. -/
def htpy_one_jet_sec.unlocalize_fun (F : htpy_one_jet_sec IX X IY Y) (t : ℝ) (m : M) :
  one_jet_bundle IM M IN N :=
⟨⟨m, g $ (F t).bs (h.inv_fun m)⟩,
    (g.fderiv $ (F t).bs (h.inv_fun m)).to_continuous_linear_map ∘L
      ((F t $ h.inv_fun m).2 ∘L (h.fderiv $ h.inv_fun m).symm.to_continuous_linear_map)⟩

/-- Un-localize a homotopy of one-jet sections from two open embeddings. -/
-- Note(F): this is only well-defined on `univ × range h`, right?
def htpy_one_jet_sec.unlocalize (F : htpy_one_jet_sec IX X IY Y) : htpy_one_jet_sec IM M IN N :=
{ to_fun := F.unlocalize_fun g h,
  is_sec' := λ x m, rfl,
  smooth' := sorry }

lemma one_jet_sec.unlocalize_localize (G : htpy_one_jet_sec IX X IY Y)
  (hF : range (F.bs ∘ h) ⊆ range g)
  (hFG : G 0 = F.localize g h hF) : G.unlocalize g h 0 = F :=
sorry

/-- Localize a formal solution. -/
def transfer (hF : range (F.bs ∘ h) ⊆ range g) (h2F : ∀ x, F (h x) ∈ R) :
  formal_sol (R.localize g h) :=
⟨F.localize g h hF, λ x, (F.localize_mem_iff g h hF).mpr $ h2F x⟩

end smooth_open_embedding

section loc
/-! ## Link with the local story

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
