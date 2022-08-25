import local.relation
import global.one_jet_sec
import global.smooth_embedding
import to_mathlib.topology.algebra.module

/-!
# First order partial differential relations for maps between manifolds

This file contains fundamental definitions about first order partial differential relations
for maps between manifolds and relating them to the local story of first order partial differential
relations for maps between vector spaces.

Given manifolds `M` and `M'` modelled on `I` and `I'`, a first order partial differential relation
for maps from `M` to `M'` is a set in the 1-jet bundle J¹(M, M'), also known as
`one_jet_bundle I M I' M'`.
-/

noncomputable theory

open set function filter charted_space smooth_manifold_with_corners
open_locale topological_space manifold

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
{EP : Type*} [normed_add_comm_group EP] [normed_space ℝ EP]
{HP : Type*} [topological_space HP] (IP : model_with_corners ℝ EP HP)
{P : Type*} [topological_space P] [charted_space HP P] [smooth_manifold_with_corners IP P]

local notation `TM` := tangent_space I
local notation `TM'` := tangent_space I'

/-- A first-order differential relation for maps from `M` to `N` is a subset of the 1-jet bundle. -/
@[reducible] def rel_mfld := set (one_jet_bundle I M I' M')

variables {I M I' M'} {R : rel_mfld I M I' M'}

/-- A solution to a relation `R`. -/
@[ext] structure sol (R : rel_mfld I M I' M') :=
(f : M → M')
(f_diff : cont_mdiff I I' ⊤ f)
(is_sol : ∀ x, one_jet_ext I I' f x ∈ R)

/-- A formal solution to a local relation `R` over a set `U`. -/
@[ext] structure formal_sol (R : rel_mfld I M I' M') extends
  to_one_jet_sec : one_jet_sec I M I' M' :=
(is_sol' : ∀ x : M, to_one_jet_sec x ∈ R)

instance (R : rel_mfld I M I' M') :
  has_coe_to_fun (formal_sol R) (λ S, M → one_jet_bundle I M I' M') :=
⟨λ F, F.to_one_jet_sec⟩

lemma formal_sol.is_sol (F : formal_sol R) : ∀ x, F x ∈ R :=
F.is_sol'

/-- part of the construction of the slice `R(σ,p)`. -/
def rel_mfld.preslice (R : rel_mfld I M I' M') (σ : one_jet_bundle I M I' M')
  (p : dual_pair' $ TM σ.1.1) : set (TM' σ.1.2) :=
{w : TM' σ.1.2 | one_jet_bundle.mk σ.1.1 σ.1.2 (p.update σ.2 w) ∈ R}

/-- For some reason `rw [mem_set_of_eq]` fails after unfolding `preslice`,
but rewriting with this lemma works. -/
lemma mem_preslice {R : rel_mfld I M I' M'} {σ : one_jet_bundle I M I' M'}
  {p : dual_pair' $ TM σ.1.1} {w : TM' σ.1.2} :
  w ∈ R.preslice σ p ↔ one_jet_bundle.mk σ.1.1 σ.1.2 (p.update σ.2 w) ∈ R :=
iff.rfl

/-- the slice `R(σ,p)`. -/
def rel_mfld.slice (R : rel_mfld I M I' M') (σ : one_jet_bundle I M I' M')
  (p : dual_pair' $ TM σ.1.1) : set (TM' σ.1.2) :=
connected_component_in (R.preslice σ p) (σ.2 p.v)

def rel_mfld.ample (R : rel_mfld I M I' M') : Prop :=
∀ ⦃σ : one_jet_bundle I M I' M'⦄ (p : dual_pair' $ TM σ.1.1), σ ∈ R → ample_set (R.slice σ p)

/-- A family of formal solutions indexed by manifold `N` is a function from `N` into formal
  solutions in such a way that the function is smooth as a function of all arguments. -/
structure family_formal_sol (R : rel_mfld I M I' M') extends
  to_family_one_jet_sec : family_one_jet_sec I M I' M' J N :=
(is_sol' : ∀ (t : N) (x : M), to_family_one_jet_sec t x ∈ R)

instance : has_coe_to_fun (family_formal_sol J N R) (λ S, N → formal_sol R) :=
⟨λ S t, ⟨S.to_family_one_jet_sec t, S.is_sol' t⟩⟩

namespace family_formal_sol

variables {J N J' N' IP P}

/-- Reindex a family along a smooth function `f`. -/
def reindex (S : family_formal_sol J' N' R) (f : C^∞⟮J, N; J', N'⟯) :
  family_formal_sol J N R :=
⟨S.to_family_one_jet_sec.reindex f, λ t, S.is_sol' (f t)⟩

end family_formal_sol

/-- A homotopy of formal solutions is a family indexed by `ℝ` -/
@[reducible] def htpy_formal_sol (R : rel_mfld I M I' M') := family_formal_sol 𝓘(ℝ, ℝ) ℝ R

variables [finite_dimensional ℝ E] [finite_dimensional ℝ E']
[sigma_compact_space M] [sigma_compact_space M'] [t2_space M] [t2_space M']

/-- An arbitrary distance on `J¹(M, M')`. -/
@[reducible] def some_dist : has_dist (one_jet_bundle I M I' M') :=
(@topological_space.metrizable_space_metric _ _ (manifold_with_corners.metrizable_space
  ((I.prod I').prod 𝓘(ℝ, E →L[ℝ] E')) _)).to_pseudo_metric_space.to_has_dist

/-- A relation `R` satisfies the (non-parametric) relative C⁰-dense h-principle w.r.t. a subset
`C` of the domain if for every formal solution `𝓕₀` that is holonomic near `C`
there is a homotopy between `𝓕₀` and a holonomic solution that is constant near `C` and
`ε`-close to `𝓕₀`. -/
def rel_mfld.satisfies_h_principle (R : rel_mfld I M I' M') (C : set M) (ε : M → ℝ) : Prop :=
∀ 𝓕₀ : formal_sol R, (∀ᶠ x in 𝓝ˢ C, 𝓕₀.to_one_jet_sec.is_holonomic_at x) →
∃ 𝓕 : htpy_formal_sol R, 𝓕 0 = 𝓕₀ ∧
  (𝓕 1).to_one_jet_sec.is_holonomic ∧
  (∀ᶠ x in 𝓝ˢ C, ∀ t : ℝ, 𝓕 t x = 𝓕₀ x) ∧
  (∀ (t : ℝ) (x : M), @dist _ some_dist (𝓕 t x) (𝓕₀ x) ≤ ε x)

/-- A relation `R` satisfies the parametric relative C⁰-dense h-principle w.r.t. manifold `P`,
`C₁ ⊆ P`, `C₂ ⊆ M` and `ε : M → ℝ` if for every family of
formal solutions `𝓕₀` indexed by a manifold with boundary `P` that is holonomic near `C₁` and `C₂`,
there is a homotopy `𝓕` between `𝓕₀` and a holonomic solution,
in such a way that `𝓕` is constant near `C₁` and `C₂` and `ε`-close to `𝓕₀`.
Note: `ε`-closeness is measured using an arbitrary distance function obtained from the metrizability
of `J¹(M, M')`. Potentially we prefer to have this w.r.t. an arbitrary compatible metric.
-/
def rel_mfld.satisfies_h_principle_with (R : rel_mfld I M I' M') (C₁ : set P) (C₂ : set M)
  (ε : M → ℝ) : Prop :=
∀ 𝓕₀ : family_formal_sol IP P R, -- given a family of formal solutions with parameters in `P`
(∀ᶠ s in 𝓝ˢ C₁, (𝓕₀ s).to_one_jet_sec.is_holonomic) → -- holonomic near `C₁` of parameter space
(∀ᶠ x in 𝓝ˢ C₂, ∀ s, (𝓕₀ s).to_one_jet_sec.is_holonomic_at x) → -- and near set `C₂` of the domain
∃ 𝓕 : family_formal_sol (𝓘(ℝ, ℝ).prod IP) (ℝ × P) R, -- then there is a homotopy of such families
  (∀ s, 𝓕 (0, s) = 𝓕₀ s) ∧ -- that agrees on `t = 0`
  (∀ᶠ s in 𝓝ˢ C₁, ∀ t : ℝ, 𝓕 (t, s) = 𝓕₀ s) ∧ -- and agrees near `C₁`
  (∀ᶠ x in 𝓝ˢ C₂, ∀ (t : ℝ) (s : P), 𝓕 (t, s) x = 𝓕₀ s x) ∧ -- and agrees near `C₂`
  (∀ s, (𝓕 (1, s)).to_one_jet_sec.is_holonomic) ∧ -- is holonomic everywhere for `t = 1`
  (∀ (t : ℝ) (s : P) (x : M), @dist _ some_dist (𝓕 (t, s) x) (𝓕₀ s x) ≤ ε x) -- and close to `𝓕₀`.


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
@[simps fst_fst fst_snd]
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

open basic_smooth_vector_bundle_core

/-- Localize a one-jet section in two open embeddings.
  It maps `x` to `(x, y, (D_y(g))⁻¹ ∘ F_φ(h x) ∘ D_x(h))` where `y : M := g⁻¹(F_{bs}(h x))`. -/
@[simps] def one_jet_sec.localize (hF : range (F.bs ∘ h) ⊆ range g) :
  one_jet_sec IX X IY Y :=
{ bs := λ x, g.inv_fun (F.bs $ h x),
  ϕ := λ x, let y := g.inv_fun (F.bs $ h x) in
  (↑(g.fderiv y).symm : TN (g y) →L[ℝ] TY y) ∘L ((F $ h x).2 ∘L (h.fderiv x : TX x →L[ℝ] TM (h x))),
  smooth' := begin
    simp_rw [h.fderiv_coe, g.fderiv_symm_coe,
      mfderiv_congr_point (g.right_inv (hF $ mem_range_self _))],
    refine smooth.one_jet_comp IN (λ x', F.bs (h x')) _ _,
    { exact λ x, (g.smooth_at_inv $ hF $ mem_range_self x).one_jet_ext.comp _
        (F.smooth_bs.comp h.smooth_to).cont_mdiff_at },
    apply smooth.one_jet_comp IM h (F.smooth_eta.comp h.smooth_to) h.smooth_to.one_jet_ext
  end }

lemma transfer_localize (hF : range (F.bs ∘ h) ⊆ range g) (x : X) :
  (F.localize g h hF x).transfer g h = F (h x) :=
begin
  rw [one_jet_sec.coe_apply, one_jet_sec.localize_bs, one_jet_sec.localize_ϕ,
    one_jet_bundle.transfer],
  dsimp only,
  ext,
  { refl },
  { simp_rw [g.right_inv (hF $ mem_range_self x), function.comp_apply, F.bs_eq] },
  { apply heq_of_eq, dsimp only, ext v,
    simp_rw [continuous_linear_map.comp_apply, continuous_linear_equiv.coe_coe,
      continuous_linear_equiv.apply_symm_apply] },
end

lemma one_jet_sec.localize_bs_fun (hF : range (F.bs ∘ h) ⊆ range g) :
  (F.localize g h hF).bs = g.inv_fun ∘ F.bs ∘ h :=
rfl

lemma one_jet_sec.localize_mem_iff (hF : range (F.bs ∘ h) ⊆ range g) {x : X} :
  F.localize g h hF x ∈ R.localize g h ↔ F (h x) ∈ R :=
by rw [rel_mfld.localize, mem_preimage, transfer_localize F g h hF]

lemma rel_mfld.ample.localize (hR : R.ample) : (R.localize g h).ample :=
begin
  intros x p hx,
  have : (rel_mfld.localize g h R).slice x p =
    (g.fderiv x.1.2).symm '' R.slice (x.transfer g h) (p.map (h.fderiv x.1.1)),
  { simp_rw [rel_mfld.slice, rel_mfld.localize],
    symmetry,
    refine ((g.fderiv x.1.2).symm.to_homeomorph.image_connected_component_in _).trans _,
    { rw [mem_preslice, dual_pair'.update_self], exact hx },
    simp_rw [continuous_linear_equiv.coe_to_homeomorph,
      continuous_linear_equiv.image_symm_eq_preimage],
    congr' 1,
    { ext v, simp_rw [mem_preimage, mem_preslice, mem_preimage],
      dsimp only [one_jet_bundle.transfer, one_jet_bundle_mk_fst, one_jet_bundle_mk_snd],
      simp_rw [p.map_update_comp_right, ← p.update_comp_left, continuous_linear_equiv.coe_coe,
        one_jet_bundle.mk] },
    { dsimp only [one_jet_bundle.transfer],
      simp_rw [continuous_linear_map.comp_apply, continuous_linear_equiv.coe_coe, p.map_v,
        continuous_linear_equiv.symm_apply_apply] } },
  rw [this],
  exact (hR _ hx).image (g.fderiv x.1.2).symm
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
  rw [mfderiv_congr (F.localize_bs_fun g h hF), one_jet_sec.snd_eq, F.localize_ϕ, this],
  simp_rw [← continuous_linear_equiv.coe_def_rev,
    continuous_linear_equiv.cancel_left, continuous_linear_equiv.cancel_right]
end

/-- Un-localize a homotopy of one-jet sections from two open embeddings. -/
-- Note(F): this is only well-defined on `univ × range h`, right?
def htpy_one_jet_sec.unlocalize (F : htpy_one_jet_sec IX X IY Y) : htpy_one_jet_sec IM M IN N :=
{ bs := λ t m , g $ (F t).bs (h.inv_fun m),
  ϕ := λ t m, (g.fderiv $ (F t).bs (h.inv_fun m)).to_continuous_linear_map ∘L
      ((F t $ h.inv_fun m).2 ∘L (h.fderiv $ h.inv_fun m).symm.to_continuous_linear_map),
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

namespace family_one_jet_sec

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
variables {I M I' M' J N} {R : rel_mfld I M I' M'}

lemma uncurry_mem_iff (S : family_one_jet_sec I M I' M' J N) {t : N} {x : M} :
  S.uncurry (t, x) ∈ (bundle_snd ⁻¹' R : rel_mfld (J.prod I) (N × M) I' M') ↔ S t x ∈ R :=
begin
  simp_rw [mem_preimage],
  sorry
end


end family_one_jet_sec

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
