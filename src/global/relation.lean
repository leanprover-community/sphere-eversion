import local.dual_pair
import local.ample_set
import global.one_jet_sec
import global.smooth_embedding
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

lemma coe_inj_iff {S T : formal_sol R} : S = T ↔ ∀ x, S x = T x :=
begin
  split,
  { rintro rfl x, refl },
  { intros h, ext : 3, show (S x).1.2 = (T x).1.2, rw [h],
    apply heq_of_eq, ext1, show (S x).2 = (T x).2, rw [h] }
end

lemma coe_inj {S T : formal_sol R} (h : ∀ x, S x = T x) : S = T :=
coe_inj_iff.mpr h

@[simp] lemma to_one_jet_sec_coe (S : formal_sol R) {x : M} : S.to_one_jet_sec x = S x := rfl

lemma is_sol (F : formal_sol R) : ∀ x, F x ∈ R :=
F.is_sol'

lemma coe_apply (F : formal_sol R) (x : M) : F x = ⟨(x, F.bs x), (F.ϕ x)⟩ := rfl
lemma fst_eq (F : formal_sol R) (x : M) : (F x).1 = (x, F.bs x) := rfl
lemma snd_eq (F : formal_sol R) (x : M) : (F x).2 = F.ϕ x := rfl
lemma is_sec (F : formal_sol R) (x : M) : (F x).1.1 = x := rfl
lemma bs_eq (F : formal_sol R) (x : M) : F.bs x = (F x).1.2 := rfl

end formal_sol

/-! ## Ampleness -/

/-- The slice `R(σ,p)`. -/
def rel_mfld.slice (R : rel_mfld I M I' M') (σ : one_jet_bundle I M I' M')
  (p : dual_pair $ TM σ.1.1) : set (TM' σ.1.2) :=
{w : TM' σ.1.2 | one_jet_bundle.mk σ.1.1 σ.1.2 (p.update σ.2 w) ∈ R}

/-- For some reason `rw [mem_set_of_eq]` fails after unfolding `slice`,
but rewriting with this lemma works. -/
lemma mem_slice {R : rel_mfld I M I' M'} {σ : one_jet_bundle I M I' M'}
  {p : dual_pair $ TM σ.1.1} {w : TM' σ.1.2} :
  w ∈ R.slice σ p ↔ one_jet_bundle.mk σ.1.1 σ.1.2 (p.update σ.2 w) ∈ R :=
iff.rfl

lemma slice_mk_update {R : rel_mfld I M I' M'} {σ : one_jet_bundle I M I' M'}
  {p : dual_pair $ TM σ.1.1} (x : E') :
  R.slice (one_jet_bundle.mk σ.1.1 σ.1.2 (p.update σ.2 x)) p = (R.slice σ p : set E') :=
begin
  ext1 w,
  dsimp only [mem_slice],
  congr' 3,
  simp_rw [one_jet_bundle_mk_snd, p.update_update],
end

/-- A differential relation is ample if all its slices are ample sets. -/
def rel_mfld.ample (R : rel_mfld I M I' M') : Prop :=
∀ ⦃σ : one_jet_bundle I M I' M'⦄ (p : dual_pair $ TM σ.1.1), ample_set (R.slice σ p)

lemma rel_mfld.ample_iff (R : rel_mfld I M I' M') : R.ample ↔
  ∀ ⦃σ : one_jet_bundle I M I' M'⦄ (p : dual_pair $ TM σ.1.1), σ ∈ R → ample_set (R.slice σ p) :=
begin
  simp_rw [rel_mfld.ample],
  refine ⟨λ h σ p _, h p, λ h σ p x hx, _⟩,
  have := @h (one_jet_bundle.mk σ.1.1 σ.1.2 (p.update σ.2 x)) p hx,
  rw [slice_mk_update] at this,
  exact this x hx
end

/-! ## Families of formal solutions. -/

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

/-! ## Homotopies of formal solutions. -/

/-- A homotopy of formal solutions is a family indexed by `ℝ` -/
@[reducible] def htpy_formal_sol (R : rel_mfld I M I' M') := family_formal_sol 𝓘(ℝ, ℝ) ℝ R

/-- The constant homotopy of formal solution associated to a formal solution. -/
def formal_sol.const_htpy (F : formal_sol R) : htpy_formal_sol R :=
{ bs := λ t, F.bs,
  ϕ := λ t, F.ϕ,
  smooth' := F.smooth.comp smooth_snd,
  is_sol' := λ t, F.is_sol }

lemma formal_sol.const_htpy_eq (F : formal_sol R) (t : ℝ) : F.const_htpy t = F :=
by ext : 3 ; refl

variable (R)

/-- The empty homotopy of formal solution associated to any relation whose source manifold
is empty. This is required to avoid a silly nonemptyness assumption in the main theorems. -/
def empty_htpy_formal_sol [is_empty M] : htpy_formal_sol R :=
{ bs := λ t x, (is_empty.false x).elim,
  ϕ :=  λ t x, (is_empty.false x).elim,
  smooth' := λ ⟨t, x⟩, (is_empty.false x).elim,
  is_sol' := λ t x, (is_empty.false x).elim }

/-! ## The h-principle -/

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

lemma rel_mfld.satisfies_h_principle_of_weak
  [finite_dimensional ℝ E] [t2_space M] [sigma_compact_space M]
  {R : rel_mfld I M IX X} {ε : M → ℝ} {C : set M} (hC : is_closed C)
  (h : ∀ A : set M, is_closed A → R.satisfies_h_principle_weak A ε) : R.satisfies_h_principle C ε :=
begin
  haveI := manifold_with_corners.metrizable_space I M,
  letI : metric_space M := topological_space.metrizable_space_metric M,
  intros 𝓕₀ h𝓕₀,
  obtain ⟨C', hCC', hC', h𝓕₀C'⟩ := h𝓕₀.closed_neighborhood hC,
  obtain ⟨𝓕, h1, h2, h3, h4⟩ := h C' hC' 𝓕₀ h𝓕₀C',
  exact ⟨𝓕, h1, h2, eventually_of_mem hCC' h3, h4⟩
end

/-- A relation `R` satisfies the parametric relative C⁰-dense h-principle w.r.t. manifold `P`,
`C ⊆ P × M` and `ε : M → ℝ` if for every family of
formal solutions `𝓕₀` indexed by a manifold with boundary `P` that is holonomic near `C`,
there is a homotopy `𝓕` between `𝓕₀` and a holonomic solution,
in such a way that `𝓕` is constant near `C` and `ε`-close to `𝓕₀`.
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
    exact (𝓕.reindex j).to_family_one_jet_sec.smooth_bs },
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

section open_smooth_embedding
/-! ## Localisation of one jet sections

In order to use the local story of convex integration, we need a way to turn a
one jet section into local ones, then apply the local story to build a homotopy of one jets section
and transfer back to the original manifolds. There is a dissymetry here: we use
maps from whole vector spaces to open sets in manifold.

The global manifolds are called `M` and `N'`. We don't assume the local ones are vector spaces,
there are manifolds `X` and `Y` that will be vector spaces in the next section.
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
  (φ : open_smooth_embedding IX X IM M) (ψ : open_smooth_embedding IY Y IN N)
  {R : rel_mfld IM M IN N}

local notation `TM` := tangent_space IM
local notation `TN` := tangent_space IN
local notation `TX` := tangent_space IX
local notation `TY` := tangent_space IY

local notation `J¹XY` := one_jet_bundle IX X IY Y
local notation `J¹MN` := one_jet_bundle IM M IN N
local notation `IXY` := (IX.prod IY).prod 𝓘(ℝ, EX →L[ℝ] EY)
local notation `IMN` := (IM.prod IN).prod 𝓘(ℝ, EM →L[ℝ] EN)

/-! ## Transfer from J¹(X, Y) to J¹(M, N) and localized relations -/

/-- Transfer map between one jet bundles induced by open smooth embedding into the source and
targets. -/
@[simps fst_fst fst_snd]
def open_smooth_embedding.transfer : one_jet_bundle IX X IY Y → one_jet_bundle IM M IN N :=
one_jet_bundle.map IY IN φ ψ (λ x, (φ.fderiv x).symm)

lemma open_smooth_embedding.smooth_transfer :
  smooth ((IX.prod IY).prod 𝓘(ℝ, EX →L[ℝ] EY))
  ((IM.prod IN).prod 𝓘(ℝ, EM →L[ℝ] EN)) (φ.transfer ψ) :=
begin
  intro x,
  refine smooth_at.one_jet_bundle_map (φ.smooth_to.smooth_at.comp _ smooth_at_snd)
    (ψ.smooth_to.smooth_at.comp _ smooth_at_snd) _ smooth_at_id,
  have := cont_mdiff_at.mfderiv''' (λ x, φ.inv_fun) (λ x : one_jet_bundle IX X IY Y, φ x.1.1)
    ((φ.smooth_at_inv $ _).comp (x, φ x.1.1) smooth_at_snd)
    (φ.smooth_to.smooth_at.comp x (smooth_one_jet_bundle_proj.fst x)) le_top,
  { simp_rw [φ.left_inv] at this, exact this },
  exact mem_range_self _,
end

lemma one_jet_bundle.continuous_transfer : continuous (φ.transfer ψ) :=
(open_smooth_embedding.smooth_transfer _ _).continuous

lemma open_smooth_embedding.range_transfer : range (φ.transfer ψ) =
  one_jet_bundle.proj IM M IN N ⁻¹' (range φ ×ˢ range ψ) :=
begin
  ext σ, split,
  { rintro ⟨σ, rfl⟩, exact mk_mem_prod (mem_range_self _) (mem_range_self _) },
  { rcases σ with ⟨⟨x, y⟩, τ⟩,
    rintro ⟨⟨x, rfl⟩ : x ∈ range φ, ⟨y, rfl⟩ : y ∈ range ψ⟩,
    refine ⟨⟨(x, y), ((ψ.fderiv y).symm : tangent_space IN (ψ y) →L[ℝ] tangent_space IY y) ∘L τ ∘L
      (φ.fderiv x : tangent_space IX x →L[ℝ] tangent_space IM (φ x))⟩, _⟩,
    ext _, { refl }, { refl },
    ext1 v,
    dsimp only [open_smooth_embedding.transfer, one_jet_bundle.map, one_jet_bundle.mk],
    simp_rw [continuous_linear_map.comp_apply, ← ψ.fderiv_coe, continuous_linear_equiv.coe_coe,
      (φ.fderiv x).apply_symm_apply, (ψ.fderiv y).apply_symm_apply] }
end

lemma open_smooth_embedding.is_open_range_transfer : is_open (range (φ.transfer ψ)) :=
begin
  rw [φ.range_transfer ψ],
  exact (φ.is_open_range.prod ψ.is_open_range).preimage (one_jet_bundle_proj_continuous _ _ _ _),
end

/-- localize a relation -/
def rel_mfld.localize (R : rel_mfld IM M IN N) : rel_mfld IX X IY Y :=
φ.transfer ψ ⁻¹' R

/-- Ampleness survives localization -/
lemma rel_mfld.ample.localize (hR : R.ample) : (R.localize φ ψ).ample :=
begin
  intros x p,
  have : (rel_mfld.localize φ ψ R).slice x p =
    (ψ.fderiv x.1.2).symm '' R.slice (φ.transfer ψ x) (p.map (φ.fderiv x.1.1)),
  { ext v,
    simp_rw [rel_mfld.localize, continuous_linear_equiv.image_symm_eq_preimage, mem_preimage,
      mem_slice, mem_preimage],
    dsimp only [open_smooth_embedding.transfer, one_jet_bundle.map, one_jet_bundle_mk_fst,
      one_jet_bundle_mk_snd],
    simp_rw [p.map_update_comp_right, ← p.update_comp_left, one_jet_bundle.mk, ← ψ.fderiv_coe,
      continuous_linear_equiv.coe_coe] },
  rw [this],
  exact (hR _).image (ψ.fderiv x.1.2).symm
end


/-! ## Localized 1-jet sections -/

/-- Localize a one-jet section in two open embeddings.
  It maps `x` to `(x, y, (D_y(g))⁻¹ ∘ F_φ(φ x) ∘ D_x(φ))` where `y : M := g⁻¹(F_{bs}(φ x))`. -/
@[simps] def one_jet_sec.localize (hF : range (F.bs ∘ φ) ⊆ range ψ) :
  one_jet_sec IX X IY Y :=
{ bs := λ x, ψ.inv_fun (F.bs $ φ x),
  ϕ := λ x, let y := ψ.inv_fun (F.bs $ φ x) in
  (↑(ψ.fderiv y).symm : TN (ψ y) →L[ℝ] TY y) ∘L ((F $ φ x).2 ∘L (φ.fderiv x : TX x →L[ℝ] TM (φ x))),
  smooth' := begin
    simp_rw [φ.fderiv_coe, ψ.fderiv_symm_coe,
      mfderiv_congr_point (ψ.right_inv (hF $ mem_range_self _))],
    refine smooth.one_jet_comp IN (λ x', F.bs (φ x')) _ _,
    { exact λ x, (ψ.smooth_at_inv $ hF $ mem_range_self x).one_jet_ext.comp _
        (F.smooth_bs.comp φ.smooth_to).cont_mdiff_at },
    apply smooth.one_jet_comp IM φ (F.smooth_eta.comp φ.smooth_to) φ.smooth_to.one_jet_ext
  end }

lemma transfer_localize (hF : range (F.bs ∘ φ) ⊆ range ψ) (x : X) :
  φ.transfer ψ (F.localize φ ψ hF x) = F (φ x) :=
begin
  rw [one_jet_sec.coe_apply, one_jet_sec.localize_bs, one_jet_sec.localize_ϕ,
    open_smooth_embedding.transfer, one_jet_bundle.map],
  dsimp only [one_jet_bundle.mk],
  ext,
  { refl },
  { simp_rw [ψ.right_inv (hF $ mem_range_self x), function.comp_apply, F.bs_eq] },
  { simp_rw [← ψ.fderiv_coe, continuous_linear_map.comp_apply, continuous_linear_equiv.coe_coe,
      continuous_linear_equiv.apply_symm_apply] },
end

lemma one_jet_sec.localize_bs_fun (hF : range (F.bs ∘ φ) ⊆ range ψ) :
  (F.localize φ ψ hF).bs = ψ.inv_fun ∘ F.bs ∘ φ :=
rfl

lemma one_jet_sec.localize_mem_iff (hF : range (F.bs ∘ φ) ⊆ range ψ) {x : X} :
  F.localize φ ψ hF x ∈ R.localize φ ψ ↔ F (φ x) ∈ R :=
by rw [rel_mfld.localize, mem_preimage, transfer_localize F φ ψ hF]

lemma is_holonomic_at_localize_iff (hF : range (F.bs ∘ φ) ⊆ range ψ) (x : X) :
  (F.localize φ ψ hF).is_holonomic_at x ↔ F.is_holonomic_at (φ x)  :=
begin
  have : mfderiv IX IY (ψ.inv_fun ∘ F.bs ∘ φ) x =
    (ψ.fderiv (ψ.inv_fun (F.bs (φ x)))).symm.to_continuous_linear_map.comp
    ((mfderiv IM IN F.bs (φ x)).comp (φ.fderiv x).to_continuous_linear_map),
  { have h1 : mdifferentiable_at IN IY ψ.inv_fun (F.bs (φ x)) :=
      (ψ.smooth_at_inv $ hF $ mem_range_self _).mdifferentiable_at,
    have h2 : mdifferentiable_at IM IN F.bs (φ x) := F.smooth_bs.mdifferentiable_at,
    have h3 : mdifferentiable_at IX IM φ x := φ.smooth_to.mdifferentiable_at,
    rw [mfderiv_comp x h1 (h2.comp x h3), mfderiv_comp x h2 h3,
      ← ψ.fderiv_symm_coe' (hF $ mem_range_self _)],
    refl, },
  simp_rw [one_jet_sec.is_holonomic_at],
  rw [mfderiv_congr (F.localize_bs_fun φ ψ hF), one_jet_sec.snd_eq, F.localize_ϕ, this],
  simp_rw [continuous_linear_equiv.coe_def_rev,
    continuous_linear_equiv.cancel_left, continuous_linear_equiv.cancel_right]
end

-- We use `localize` in `localisation` for the version that is a `rel_loc.htpy_formal_sol`.
def htpy_formal_sol.localize' (F : htpy_formal_sol R) (hF : ∀ t, range ((F t).bs ∘ φ) ⊆ range ψ) :
  htpy_formal_sol (R.localize φ ψ)  :=
{ bs := λ t, ((F t).to_one_jet_sec.localize φ ψ (hF t)).bs,
  ϕ := λ t, ((F t).to_one_jet_sec.localize φ ψ (hF t)).ϕ,
  smooth' := begin
    dsimp only [one_jet_sec.localize],
    simp_rw [φ.fderiv_coe, ψ.fderiv_symm_coe,
      mfderiv_congr_point (ψ.right_inv (hF _ $ mem_range_self _))],
    have h1 : ∀ {x : ℝ × X}, smooth_at (𝓘(ℝ, ℝ).prod IX) IN (λ x : ℝ × X, F.bs x.1 (φ x.2)) x :=
      λ x, F.smooth_bs.smooth_at.comp x
        (smooth_at_fst.prod_mk (φ.smooth_to.smooth_at.comp _ smooth_at_snd)),
    have h2 : ∀ (x : ℝ × X), smooth_at IN IY ψ.inv_fun (F.bs x.1 (φ x.2)) :=
      λ x, ψ.smooth_at_inv $ hF x.1 $ mem_range_self x.2,
    -- argh
    have h2' : ∀ (x : ℝ × X), smooth_at IN IY ψ.inv_fun (x, F.bs x.1 (φ x.2)).2 :=
      h2,
    refine smooth.one_jet_comp IN (λ z, (F z.1).bs (φ z.2)) (λ x, _) _,
    { refine h1.one_jet_bundle_mk ((h2 x).comp x h1) _,
      apply cont_mdiff_at.mfderiv''' (λ x, ψ.inv_fun) (λ x : ℝ × X, F.bs x.1 (φ x.2))
        ((h2' x).comp _ smooth_at_snd) h1 le_top },
    refine (F.smooth.comp (smooth_id.prod_map φ.smooth_to)).one_jet_comp IM (λ z, φ z.2) _,
    exact φ.smooth_to.one_jet_ext.comp smooth_snd
  end,
  is_sol' := λ t x, ((F t).to_one_jet_sec.localize_mem_iff φ ψ (hF t)).mpr F.is_sol }

/-! ## From embeddings `X ↪ M` and `Y ↪ N` to `J¹(X, Y) ↪ J¹(M, N)` -/

-- very slow to elaborate :-(
@[simps]
def one_jet_bundle.embedding : open_smooth_embedding IXY J¹XY IMN J¹MN :=
{ to_fun := φ.transfer ψ,
  inv_fun := one_jet_bundle.map IN IY φ.inv_fun ψ.inv_fun
    (λ x, (φ.fderiv $ φ.inv_fun x : TX (φ.inv_fun x) →L[ℝ] TM (φ $ φ.inv_fun x))),
  left_inv' := λ σ, begin
    rw [open_smooth_embedding.transfer, one_jet_bundle.map_map
      ψ.smooth_at_inv'.mdifferentiable_at ψ.smooth_to.smooth_at.mdifferentiable_at],
    conv_rhs { rw [← one_jet_bundle.map_id σ] },
    congr' 1,
    { rw [open_smooth_embedding.inv_fun_comp_coe] },
    { rw [open_smooth_embedding.inv_fun_comp_coe] },
    { ext x v, simp_rw [continuous_linear_map.comp_apply],
      convert (φ.fderiv x).symm_apply_apply v,
      simp_rw [φ.left_inv] }
  end,
  is_open_range := φ.is_open_range_transfer ψ,
  smooth_to := φ.smooth_transfer ψ,
  smooth_inv := begin
    rintro _ ⟨x, rfl⟩,
    refine (smooth_at.one_jet_bundle_map _ _ _ smooth_at_id).smooth_within_at,
    { refine ((φ.smooth_at_inv _).comp _ smooth_at_snd), exact mem_range_self _ },
    { refine ((ψ.smooth_at_inv _).comp _ smooth_at_snd), exact mem_range_self _ },
    have := cont_mdiff_at.mfderiv''' (λ x, φ) (λ x : one_jet_bundle IM M IN N, φ.inv_fun x.1.1)
      (φ.smooth_to.smooth_at.comp _ smooth_at_snd)
      ((φ.smooth_at_inv _).comp _ (smooth_one_jet_bundle_proj.fst (φ.transfer ψ x))) le_top,
    { dsimp only [id],
      simp_rw [φ.left_inv] at this,
      refine this.congr_of_eventually_eq _,
      refine filter.eventually_of_mem ((φ.is_open_range_transfer ψ).mem_nhds (mem_range_self _)) _,
      rw [φ.range_transfer ψ],
      rintro ⟨⟨x, y⟩, τ⟩ ⟨⟨x, rfl⟩ : x ∈ range φ, ⟨y, rfl⟩ : y ∈ range ψ⟩,
      simp_rw [in_coordinates, φ.transfer_fst_fst, φ.left_inv],
      refl },
    exact mem_range_self _,
  end }

/-! ## Updating 1-jet sections and formal solutions -/

local notation `JΘ` := φ.update (one_jet_bundle.embedding φ ψ)

variables {K : set X}

namespace open_smooth_embedding

lemma Jupdate_aux (F : one_jet_sec IM M IN N) (G : one_jet_sec IX X IY Y)
  (m : M) : (JΘ F G m).1.1 = m :=
begin
  simp_rw [open_smooth_embedding.update], split_ifs,
  { rcases h with ⟨x, rfl⟩,
    simp_rw [one_jet_bundle.embedding_to_fun, φ.transfer_fst_fst, φ.left_inv, G.fst_eq] },
  { refl }
end

variables [t2_space M]

/-- Update a global homotopy of 1-jet-sections `F` using a local one `G`. -/
def htpy_Jupdate
  (F : htpy_one_jet_sec IM M IN N) (G : htpy_one_jet_sec IX X IY Y)
  (hK : is_compact K)
  (hFG : ∀ t, ∀ x ∉ K, F t (φ x) = (one_jet_bundle.embedding φ ψ) (G t x)) :
  htpy_one_jet_sec IM M IN N :=
begin
  refine family_one_jet_sec.mk' (λ t, JΘ (F t) (G t)) (λ t, (φ.Jupdate_aux ψ (F t) (G t))) _,
  refine φ.smooth_update _ _ _ (hK.image φ.continuous).is_closed _ _ smooth_snd (λ x, hFG x.1),
  { exact F.smooth.comp (smooth_fst.prod_map smooth_id) },
  { exact G.smooth.comp (smooth_fst.prod_map smooth_id) },
end

lemma htpy_Jupdate_apply {F : htpy_one_jet_sec IM M IN N} {G : htpy_one_jet_sec IX X IY Y}
  (hK : is_compact K)
  (hFG : ∀ t, ∀ x ∉ K, F t (φ x) = (one_jet_bundle.embedding φ ψ) (G t x)) (t : ℝ) (m : M) :
  φ.htpy_Jupdate ψ F G hK hFG t m = JΘ (F t) (G t) m :=
by { ext, exact (φ.Jupdate_aux ψ (F t) (G t) m).symm, refl, refl }

lemma htpy_Jupdate_bs (F : htpy_one_jet_sec IM M IN N)
  (G : htpy_one_jet_sec IX X IY Y) (t : ℝ)
  (hK : is_compact K) (hFG : ∀ t, ∀ x ∉ K, F t (φ x) = one_jet_bundle.embedding φ ψ (G t x)) :
  (open_smooth_embedding.htpy_Jupdate φ ψ F G hK hFG t).bs =
  open_smooth_embedding.update φ ψ (F t).bs (G t).bs :=
begin
  classical,
  ext x,
  change (if x ∈ range φ then φ.transfer ψ (G t (φ.inv_fun x)) else F t x).1.2 =
    if x ∈ range φ then _ else _,
  split_ifs ; refl,
end

lemma htpy_Jupdate_localize {F : htpy_one_jet_sec IM M IN N} {G : htpy_one_jet_sec IX X IY Y}
  (hK : is_compact K)
  (hFG : ∀ t, ∀ x ∉ K, F t (φ x) = (one_jet_bundle.embedding φ ψ) (G t x)) (t : ℝ)
  (rg : range ((φ.htpy_Jupdate ψ F G hK hFG t).bs ∘ φ) ⊆ range ψ) (x : X) :
  (φ.htpy_Jupdate ψ F G hK hFG t).localize φ ψ rg x = G t x :=
begin
  have foo : ψ.inv_fun ((φ.htpy_Jupdate ψ F G hK hFG t).bs (φ x)) = (G t).bs x,
  { simp_rw [htpy_Jupdate_bs, open_smooth_embedding.update_apply_embedding,
    open_smooth_embedding.left_inv] },
  ext,
  refl,
  { exact foo },
  { simp_rw [one_jet_sec.snd_eq, one_jet_sec.localize_ϕ],
    rw [foo],
    change (ψ.fderiv ((G t).bs x)).symm ((JΘ (F t) (G t) (φ x)).2 (φ.fderiv x x_1)) =
      ((G t).ϕ x) x_1,
    rw φ.update_apply_embedding,
    change (ψ.fderiv ((G t).bs x)).symm (ψ.fderiv ((G t).bs x) $ (G t).ϕ x $
      (φ.fderiv x).symm $ φ.fderiv x x_1) = ((G t).ϕ x x_1),
    simp_rw [continuous_linear_equiv.symm_apply_apply] },
end

/-- Update a global homotopy of formal solutions `F` using a local one `G`. -/
def update_htpy_formal_sol (F : htpy_formal_sol R)
  (G : htpy_formal_sol (R.localize φ ψ))
  (hK : is_compact K) (hFG : ∀ t, ∀ x ∉ K, F t (φ x) = (one_jet_bundle.embedding φ ψ) (G t x)) :
  htpy_formal_sol R :=
{ to_family_one_jet_sec := φ.htpy_Jupdate ψ F.to_family_one_jet_sec G.to_family_one_jet_sec hK hFG,
  is_sol' := λ t x, begin
    simp_rw [htpy_Jupdate_apply, open_smooth_embedding.update, one_jet_bundle.embedding_to_fun],
    split_ifs,
    { exact G.is_sol },
    { exact F.is_sol }
  end }

lemma update_htpy_formal_sol_apply {F : htpy_formal_sol R}
  {G : htpy_formal_sol (R.localize φ ψ)}
  (hK : is_compact K)
  (hFG : ∀ t, ∀ x ∉ K, F t (φ x) = (one_jet_bundle.embedding φ ψ) (G t x)) (t x) :
  φ.update_htpy_formal_sol ψ F G hK hFG t x = ⟨⟨x, (JΘ (F t) (G t) x).1.2⟩, (JΘ (F t) (G t) x).2⟩ :=
rfl

lemma update_htpy_formal_sol_bs' {F : htpy_formal_sol R}
  {G : htpy_formal_sol (R.localize φ ψ)}
  (hK : is_compact K)
  (hFG : ∀ t, ∀ x ∉ K, F t (φ x) = (one_jet_bundle.embedding φ ψ) (G t x)) (t) :
(φ.update_htpy_formal_sol ψ F G hK hFG t).bs = λ x, (JΘ (F t) (G t) x).1.2 :=
rfl

lemma update_htpy_formal_sol_bs {F : htpy_formal_sol R}
  {G : htpy_formal_sol (R.localize φ ψ)}
  (hK : is_compact K)
  (hFG : ∀ t, ∀ x ∉ K, F t (φ x) = (one_jet_bundle.embedding φ ψ) (G t x)) (t) :
(φ.update_htpy_formal_sol ψ F G hK hFG t).bs = φ.update ψ (F t).bs (G t).bs :=
begin
  rw update_htpy_formal_sol_bs',
  ext x,
  by_cases hx : x ∈ range φ,
  { simp only [hx, update_of_mem_range, one_jet_bundle.embedding_to_fun, transfer_fst_snd],
    refl },
  { rw [update_of_nmem_range, update_of_nmem_range],
    refl,
    exacts [hx, hx] },
end

lemma update_htpy_formal_sol_ϕ {F : htpy_formal_sol R}
  {G : htpy_formal_sol (R.localize φ ψ)}
  (hK : is_compact K)
  (hFG : ∀ t, ∀ x ∉ K, F t (φ x) = (one_jet_bundle.embedding φ ψ) (G t x)) (t) :
(φ.update_htpy_formal_sol ψ F G hK hFG t).ϕ = λ x, (JΘ (F t) (G t) x).2 :=
rfl


@[simp]
lemma update_htpy_formal_sol_apply_of_not_mem {F : htpy_formal_sol R}
  {G : htpy_formal_sol (R.localize φ ψ)}
  (hK : is_compact K) (hFG : ∀ t, ∀ x ∉ K, F t (φ x) = (one_jet_bundle.embedding φ ψ) (G t x)) (t)
  {m} (hx : m ∉ range φ) :
φ.update_htpy_formal_sol ψ F G hK hFG t m = F t m :=
begin
  rw [update_htpy_formal_sol_apply, φ.update_of_nmem_range _ _ _ hx],
  refl
end

@[simp]
lemma update_htpy_formal_sol_apply_of_mem {F : htpy_formal_sol R}
  {G : htpy_formal_sol (R.localize φ ψ)}
  (hK : is_compact K) (hFG : ∀ t, ∀ x ∉ K, F t (φ x) = (one_jet_bundle.embedding φ ψ) (G t x)) (t)
  {m} (hx : m ∈ range φ) :
  φ.update_htpy_formal_sol ψ F G hK hFG t m = φ.transfer ψ (G t $ φ.inv_fun m) :=
begin
  rw [update_htpy_formal_sol_apply, φ.update_of_mem_range _ _ _ hx],
  ext,
  { change m = φ (φ.inv_fun m),
    rw φ.right_inv hx },
  refl,
  refl
end

@[simp]
lemma update_htpy_formal_sol_apply_image {F : htpy_formal_sol R}
  {G : htpy_formal_sol (R.localize φ ψ)}
  (hK : is_compact K) (hFG : ∀ t, ∀ x ∉ K, F t (φ x) = (one_jet_bundle.embedding φ ψ) (G t x)) (t)
  {x} :
φ.update_htpy_formal_sol ψ F G hK hFG t (φ x) = φ.transfer ψ (G t x) :=
begin
 rw [open_smooth_embedding.update_htpy_formal_sol_apply_of_mem, φ.left_inv],
 exact mem_range_self x,
end


end open_smooth_embedding
end open_smooth_embedding
