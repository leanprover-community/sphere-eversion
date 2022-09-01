import local.relation
import global.one_jet_sec
import global.smooth_embedding
import to_mathlib.topology.algebra.module
import interactive_expr
set_option trace.filter_inst_type true

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

open set function filter (hiding map_smul) charted_space smooth_manifold_with_corners
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
(P : Type*) [topological_space P] [charted_space HP P] [smooth_manifold_with_corners IP P]
{EX : Type*} [normed_add_comm_group EX] [normed_space ℝ EX]
{HX : Type*} [topological_space HX] {IX : model_with_corners ℝ EX HX}
-- note: X is a metric space
{X : Type*} [metric_space X] [charted_space HX X] [smooth_manifold_with_corners IX X]

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

namespace formal_sol

@[simp]
lemma coe_mk {S : one_jet_sec I M I' M'} {h : ∀ x, S x ∈ R} {x : M} : formal_sol.mk S h x = S x :=
rfl

@[simp]
lemma to_one_jet_sec_coe (S : formal_sol R) {x : M} : S.to_one_jet_sec x = S x :=
rfl

lemma is_sol (F : formal_sol R) : ∀ x, F x ∈ R :=
F.is_sol'

lemma coe_apply (F : formal_sol R) (x : M) : F x = ⟨(x, F.bs x), (F.ϕ x)⟩ := rfl
lemma fst_eq (F : formal_sol R) (x : M) : (F x).1 = (x, F.bs x) := rfl
lemma snd_eq (F : formal_sol R) (x : M) : (F x).2 = F.ϕ x := rfl
lemma is_sec (F : formal_sol R) (x : M) : (F x).1.1 = x := rfl
lemma bs_eq (F : formal_sol R) (x : M) : F.bs x = (F x).1.2 := rfl

end formal_sol

/-- part of the construction of the slice `R(σ,p)`. -/
def rel_mfld.slice (R : rel_mfld I M I' M') (σ : one_jet_bundle I M I' M')
  (p : dual_pair' $ TM σ.1.1) : set (TM' σ.1.2) :=
{w : TM' σ.1.2 | one_jet_bundle.mk σ.1.1 σ.1.2 (p.update σ.2 w) ∈ R}

/-- For some reason `rw [mem_set_of_eq]` fails after unfolding `slice`,
but rewriting with this lemma works. -/
lemma mem_slice {R : rel_mfld I M I' M'} {σ : one_jet_bundle I M I' M'}
  {p : dual_pair' $ TM σ.1.1} {w : TM' σ.1.2} :
  w ∈ R.slice σ p ↔ one_jet_bundle.mk σ.1.1 σ.1.2 (p.update σ.2 w) ∈ R :=
iff.rfl

@[simp] lemma jet_apply_v_mem_slice
  {R : rel_mfld I M I' M'} {σ : one_jet_bundle I M I' M'} (p : dual_pair' $ TM σ.1.1) :
  σ.2 p.v ∈ R.slice σ p ↔ σ ∈ R :=
by { rcases σ with ⟨⟨m, m'⟩, φ⟩, simp [mem_slice], }

lemma slice_mk_update {R : rel_mfld I M I' M'} {σ : one_jet_bundle I M I' M'}
  {p : dual_pair' $ TM σ.1.1} (x : E') :
  R.slice (one_jet_bundle.mk σ.1.1 σ.1.2 (p.update σ.2 x)) p = (R.slice σ p : set E') :=
begin
  ext1 w,
  dsimp only [mem_slice],
  congr' 3,
  simp_rw [one_jet_bundle_mk_snd, p.update_update],
end

def rel_mfld.ample (R : rel_mfld I M I' M') : Prop :=
∀ ⦃σ : one_jet_bundle I M I' M'⦄ (p : dual_pair' $ TM σ.1.1), ample_set (R.slice σ p)

lemma rel_mfld.ample_iff (R : rel_mfld I M I' M') : R.ample ↔
  ∀ ⦃σ : one_jet_bundle I M I' M'⦄ (p : dual_pair' $ TM σ.1.1), σ ∈ R → ample_set (R.slice σ p) :=
begin
  simp_rw [rel_mfld.ample],
  refine ⟨λ h σ p _, h p, λ h σ p x hx, _⟩,
  have := @h (one_jet_bundle.mk σ.1.1 σ.1.2 (p.update σ.2 x)) p hx,
  rw [slice_mk_update] at this,
  exact this x hx
end

/-- A family of formal solutions indexed by manifold `N` is a function from `N` into formal
  solutions in such a way that the function is smooth as a function of all arguments. -/
@[ext] structure family_formal_sol (R : rel_mfld I M I' M') extends
  to_family_one_jet_sec : family_one_jet_sec I M I' M' J N :=
(is_sol' : ∀ (t : N) (x : M), to_family_one_jet_sec t x ∈ R)

instance : has_coe_to_fun (family_formal_sol J N R) (λ S, N → formal_sol R) :=
⟨λ S t, ⟨S.to_family_one_jet_sec t, S.is_sol' t⟩⟩

namespace family_formal_sol

variables {J N J' N'}

@[simp]
lemma coe_mk {S : family_one_jet_sec I M I' M' J N} {h : ∀ t x, S t x ∈ R} {t : N} {x : M} :
  family_formal_sol.mk S h t x = S t x :=
rfl

lemma coe_mk_to_one_jet_sec {S : family_one_jet_sec I M I' M' J N} {h : ∀ t x, S t x ∈ R} {t : N} :
  (family_formal_sol.mk S h t).to_one_jet_sec = S t :=
rfl

@[simp]
lemma to_family_one_jet_sec_coe (S : family_formal_sol J N R) {t : N} {x : M} :
  S.to_family_one_jet_sec t x = S t x :=
rfl

@[simp]
lemma to_family_one_jet_sec_eq (S : family_formal_sol J N R) {t : N} :
  S.to_family_one_jet_sec t = (S t).to_one_jet_sec :=
rfl

lemma is_sol (S : family_formal_sol J N R) {t : N} {x : M} : S t x ∈ R :=
S.is_sol' t x

/-- Reindex a family along a smooth function `f`. -/
def reindex (S : family_formal_sol J' N' R) (f : C^∞⟮J, N; J', N'⟯) :
  family_formal_sol J N R :=
⟨S.to_family_one_jet_sec.reindex f, λ t, S.is_sol' (f t)⟩

end family_formal_sol

/-- A homotopy of formal solutions is a family indexed by `ℝ` -/
@[reducible] def htpy_formal_sol (R : rel_mfld I M I' M') := family_formal_sol 𝓘(ℝ, ℝ) ℝ R

def formal_sol.const_htpy {R : rel_mfld I M I' M'} (F : formal_sol R) : htpy_formal_sol R :=
{ bs := λ t, F.bs,
  ϕ := λ t, F.ϕ,
  smooth' := sorry,
  is_sol' := λ t, F.is_sol' }

/-- The relation `𝓡 ^ P` -/
def rel_mfld.relativize (R : rel_mfld I M I' M') : rel_mfld (IP.prod I) (P × M) I' M' :=
bundle_snd ⁻¹' R

lemma mem_relativize (R : rel_mfld I M I' M') (w : one_jet_bundle (IP.prod I) (P × M) I' M') :
 w ∈ R.relativize IP P ↔
  (one_jet_bundle.mk w.1.1.2 w.1.2 (w.2.comp (continuous_linear_map.inr ℝ EP E)) :
    one_jet_bundle I M I' M') ∈ R :=
iff.rfl

lemma rel_mfld.is_open_relativize (R : rel_mfld I M I' M') (h2 : is_open R) :
  is_open (R.relativize IP P) :=
h2.preimage smooth_bundle_snd.continuous

variables {P}

/-- A relation `R` satisfies the (non-parametric) relative C⁰-dense h-principle w.r.t. a subset
`C` of the domain if for every formal solution `𝓕₀` that is holonomic near `C`
there is a homotopy between `𝓕₀` and a holonomic solution that is constant near `C` and
`ε`-close to `𝓕₀`. This is a temporary version with a slightly weaker conclusion. -/
def rel_mfld.satisfies_h_principle_weak (R : rel_mfld I M IX X) (C : set M) (ε : M → ℝ) : Prop :=
∀ 𝓕₀ : formal_sol R, (∀ᶠ x in 𝓝ˢ C, 𝓕₀.to_one_jet_sec.is_holonomic_at x) →
∃ 𝓕 : htpy_formal_sol R, (∀ x : M, 𝓕 0 x = 𝓕₀ x) ∧
  (𝓕 1).to_one_jet_sec.is_holonomic ∧
  (∀ x ∈ C, ∀ t : ℝ, 𝓕 t x = 𝓕₀ x) ∧
  (∀ (t : ℝ) (x : M), dist ((𝓕 t).bs x) (𝓕₀.bs x) ≤ ε x)

/-- A relation `R` satisfies the (non-parametric) relative C⁰-dense h-principle w.r.t. a subset
`C` of the domain if for every formal solution `𝓕₀` that is holonomic near `C`
there is a homotopy between `𝓕₀` and a holonomic solution that is constant near `C` and
`ε`-close to `𝓕₀`. -/
def rel_mfld.satisfies_h_principle (R : rel_mfld I M IX X) (C : set M) (ε : M → ℝ) : Prop :=
∀ 𝓕₀ : formal_sol R, (∀ᶠ x in 𝓝ˢ C, 𝓕₀.to_one_jet_sec.is_holonomic_at x) →
∃ 𝓕 : htpy_formal_sol R, (∀ x : M, 𝓕 0 x = 𝓕₀ x) ∧
  (𝓕 1).to_one_jet_sec.is_holonomic ∧
  (∀ᶠ x in 𝓝ˢ C, ∀ t : ℝ, 𝓕 t x = 𝓕₀ x) ∧
  (∀ (t : ℝ) (x : M), dist ((𝓕 t).bs x) (𝓕₀.bs x) ≤ ε x)

lemma rel_mfld.satisfies_h_principle_of_weak {R : rel_mfld I M IX X} {ε : M → ℝ}
  {C : set M} (hC : is_closed C)
  (h : ∀ A : set M, is_closed A → R.satisfies_h_principle_weak A ε)  : R.satisfies_h_principle C ε :=
sorry

/-- A relation `R` satisfies the parametric relative C⁰-dense h-principle w.r.t. manifold `P`,
`C ⊆ P × M` and `ε : M → ℝ` if for every family of
formal solutions `𝓕₀` indexed by a manifold with boundary `P` that is holonomic near `C`,
there is a homotopy `𝓕` between `𝓕₀` and a holonomic solution,
in such a way that `𝓕` is constant near `C` and `ε`-close to `𝓕₀`.
Note: `ε`-closeness is measured using an arbitrary distance function obtained from the metrizability
of `J¹(M, M')`. Potentially we prefer to have this w.r.t. an arbitrary compatible metric.
-/
def rel_mfld.satisfies_h_principle_with (R : rel_mfld I M IX X) (C : set (P × M)) (ε : M → ℝ) :
  Prop :=
∀ 𝓕₀ : family_formal_sol IP P R, -- given a family of formal solutions with parameters in `P`
(∀ᶠ (p : P × M) in 𝓝ˢ C, (𝓕₀ p.1).to_one_jet_sec.is_holonomic_at p.2) → -- holonomic near `C`
∃ 𝓕 : family_formal_sol (𝓘(ℝ, ℝ).prod IP) (ℝ × P) R, -- then there is a homotopy of such families
  (∀ (s : P) (x : M), 𝓕 (0, s) x = 𝓕₀ s x) ∧ -- that agrees on `t = 0`
  (∀ (s : P), (𝓕 (1, s)).to_one_jet_sec.is_holonomic) ∧ -- is holonomic everywhere for `t = 1`
  (∀ᶠ (p : P × M) in 𝓝ˢ C, ∀ t : ℝ, 𝓕 (t, p.1) p.2 = 𝓕₀ p.1 p.2) ∧ -- and agrees near `C`
  (∀ (t : ℝ) (s : P) (x : M), dist ((𝓕 (t, s)).bs x) ((𝓕₀ s).bs x) ≤ ε x) -- and close to `𝓕₀`.


variables {IP}

/-- If a relation satisfies the parametric relative C⁰-dense h-principle wrt some data
then we can forget the homotopy and get a family of solutions from every
family of formal solutions. -/
lemma rel_mfld.satisfies_h_principle_with.bs {R : rel_mfld I M IX X} {C : set (P × M)}
  {ε : M → ℝ} (h : R.satisfies_h_principle_with IP C ε) (𝓕₀ : family_formal_sol IP P R)
  (h2 : ∀ᶠ (p : P × M) in 𝓝ˢ C, (𝓕₀ p.1).to_one_jet_sec.is_holonomic_at p.2) :
  ∃ f : P → M → X,
    (smooth (IP.prod I) IX $ uncurry f) ∧
    (∀ᶠ (p : P × M) in 𝓝ˢ C, f p.1 p.2 = 𝓕₀.bs p.1 p.2) ∧
    (∀ p m, dist (f p m) ((𝓕₀ p).bs m) ≤ ε m) ∧
    (∀ p m, one_jet_ext I IX (f p) m ∈ R) :=
begin
  rcases h 𝓕₀ h2  with ⟨𝓕, h₁, h₂, h₃, h₄⟩,
  refine ⟨λ s, (𝓕 (1, s)).bs, _, _, _, _⟩,
  { have := 𝓕.to_family_one_jet_sec.smooth,
    let j : C^∞⟮IP, P ; 𝓘(ℝ, ℝ).prod IP, ℝ × P⟯ := ⟨λ p, (1, p),
                                                    smooth.prod_mk smooth_const smooth_id⟩,
    rw show uncurry (λ s, (𝓕 (1, s)).bs) = prod.snd ∘ (one_jet_bundle.proj _ _ _ _) ∘
                                            (λ (p : P × M), 𝓕.reindex j p.1 p.2),
    by { ext, refl },
    exact smooth_snd.comp ((basic_smooth_vector_bundle_core.smooth_proj _).comp
                           ((𝓕.reindex j).to_family_one_jet_sec.smooth)) },
  { apply h₃.mono,
    intros x hx,
    simp_rw [one_jet_sec.bs_eq, formal_sol.to_one_jet_sec_coe, hx, family_one_jet_sec.bs_eq,
      𝓕₀.to_family_one_jet_sec_coe] },
  { intros p m,
    apply h₄ },
  { intros p m,
    suffices : one_jet_ext I IX (𝓕 (1, p)).bs m = ((𝓕.to_family_one_jet_sec) (1, p)) m,
    { rw this,
      exact 𝓕.is_sol' (1, p) m },
    exact one_jet_sec.is_holonomic_at_iff.mp (h₂ p m) },
end

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
  intros x p,
  have : (rel_mfld.localize g h R).slice x p =
    (g.fderiv x.1.2).symm '' R.slice (x.transfer g h) (p.map (h.fderiv x.1.1)),
  { ext v,
    simp_rw [rel_mfld.localize, continuous_linear_equiv.image_symm_eq_preimage, mem_preimage,
      mem_slice, mem_preimage],
    dsimp only [one_jet_bundle.transfer, one_jet_bundle_mk_fst, one_jet_bundle_mk_snd],
    simp_rw [p.map_update_comp_right, ← p.update_comp_left, continuous_linear_equiv.coe_coe,
      one_jet_bundle.mk] },
  rw [this],
  exact (hR _).image (g.fderiv x.1.2).symm
end

lemma is_holonomic_at_localize_iff (hF : range (F.bs ∘ h) ⊆ range g) (x : X) :
  (F.localize g h hF).is_holonomic_at x ↔ F.is_holonomic_at (h x)  :=
begin
  have : mfderiv IX IY (g.inv_fun ∘ F.bs ∘ h) x =
    (g.fderiv (g.inv_fun (F.bs (h x)))).symm.to_continuous_linear_map.comp
    ((mfderiv IM IN F.bs (h x)).comp (h.fderiv x).to_continuous_linear_map),
  { have h1 : mdifferentiable_at IN IY g.inv_fun (F.bs (h x)) :=
      (g.smooth_at_inv $ hF $ mem_range_self _).mdifferentiable_at,
    have h2 : mdifferentiable_at IM IN F.bs (h x) := F.smooth_bs.mdifferentiable_at,
    have h3 : mdifferentiable_at IX IM h x := h.smooth_to.mdifferentiable_at,
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

section parameter_space

variables
{E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
{H : Type*} [topological_space H] (I : model_with_corners ℝ E H)
(M : Type*) [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
{E' : Type*} [normed_add_comm_group E'] [normed_space ℝ E']
{H' : Type*} [topological_space H'] (I' : model_with_corners ℝ E' H')
(M' : Type*) [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M']
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
variables {I M I' M'} {R : rel_mfld I M I' M'}

open_locale pointwise

lemma prod.zero_mk_add_zero_mk {M N : Type*} [add_monoid M] [has_add N] (b₁ b₂ : N) :
  ((0 : M), b₁) + (0, b₂) = (0, b₁ + b₂) :=
by rw [prod.mk_add_mk, add_zero]

lemma prod.smul_zero_mk {M α β : Type*} [monoid M] [add_monoid α] [distrib_mul_action M α]
  [has_smul M β] (a : M) (c : β) :
  a • ((0 : α), c) = (0, a • c) :=
by rw [prod.smul_mk, smul_zero]

lemma relativize_slice {σ : one_jet_bundle (IP.prod I) (P × M) I' M'}
  {p : dual_pair' $ tangent_space (IP.prod I) σ.1.1}
  (q : dual_pair' $ tangent_space I σ.1.1.2)
  (hpq : p.π.comp (continuous_linear_map.inr ℝ EP E) = q.π) :
  (rel_mfld.relativize IP P R).slice σ p =
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
    rw [map_add, p.update_ker_pi _ _ hv, p.update_v],
    refl },
  have := preimage_vadd_neg (show E', from σ.2 (p.v - (0, q.v)))
    (show set E', from (R.slice (bundle_snd σ) q)),
  dsimp only at this,
  simp_rw [← this, mem_preimage, mem_slice, mem_relativize],
  dsimp only [one_jet_bundle_mk_fst, one_jet_bundle_mk_snd],
  congr'
end

lemma relativize_slice_eq_univ {σ : one_jet_bundle (IP.prod I) (P × M) I' M'}
  {p : dual_pair' $ tangent_space (IP.prod I) σ.1.1}
  (hp : p.π.comp (continuous_linear_map.inr ℝ EP E) = 0) :
  ((rel_mfld.relativize IP P R).slice σ p).nonempty ↔
  (rel_mfld.relativize IP P R).slice σ p = univ :=
begin
  have h2p : ∀ x : E, p.π ((0 : EP), x) = 0 := λ x, congr_arg (λ f : E →L[ℝ] ℝ, f x) hp,
  have : ∀ y : E', (p.update σ.snd y).comp (continuous_linear_map.inr ℝ EP E) =
    σ.snd.comp (continuous_linear_map.inr ℝ EP E),
  { intro y,
    ext1 x,
    simp_rw [continuous_linear_map.comp_apply, continuous_linear_map.inr_apply,
      p.update_ker_pi _ _ (h2p x)] },
  simp_rw [set.nonempty, eq_univ_iff_forall, mem_slice, mem_relativize],
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
  simp_rw [rel_mfld.relativize, mem_preimage, bundle_snd, one_jet_sec.coe_apply,
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
    sorry
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

lemma family_one_jet_sec.is_holonomic_at_curry (S : family_one_jet_sec (IP.prod I) (P × M) I' M' J N)
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

def family_formal_sol.curry (S : family_formal_sol J N (R.relativize IP P)) :
  family_formal_sol (J.prod IP) (N × P) R :=
⟨S.to_family_one_jet_sec.curry, sorry⟩

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

/-- This might need some additional assumptions or other modifications. -/
lemma rel_mfld.satisfies_h_principle.satisfies_h_principle_with
  (R : rel_mfld I M IX X) {C : set (P × M)}
  (ε : M → ℝ) (h : (R.relativize IP P).satisfies_h_principle C (λ x, ε x.2)) :
  R.satisfies_h_principle_with IP C ε :=
begin
  intros 𝓕₀ h𝓕₀,
  obtain ⟨𝓕, h1𝓕, h2𝓕, h3𝓕, h4𝓕⟩ := h 𝓕₀.uncurry _,
  swap,
  { refine h𝓕₀.mono (λ p hp, 𝓕₀.to_family_one_jet_sec.is_holonomic_uncurry.mpr hp) },
  refine ⟨𝓕.curry, _, _, _, _⟩,
  { intros s x, exact curry_eq_iff_eq_uncurry (h1𝓕 (s, x)) },
  { intros s x, exact 𝓕.to_family_one_jet_sec.is_holonomic_at_curry (h2𝓕 (s, x)) },
  { refine h3𝓕.mono _, rintro ⟨s, x⟩ hp t, exact curry_eq_iff_eq_uncurry (hp t) },
  { intros t s x, exact (h4𝓕 t (s, x)) },
end

end parameter_space

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
