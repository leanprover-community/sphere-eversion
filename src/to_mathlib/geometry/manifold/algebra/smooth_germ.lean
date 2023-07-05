import order.filter.germ
import geometry.manifold.algebra.smooth_functions

import to_mathlib.topology.germ

noncomputable theory

open filter set
open_locale manifold topological_space big_operators

-- to smooth_functions
section

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
{E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
{E' : Type*} [normed_add_comm_group E'] [normed_space 𝕜 E']
{H : Type*} [topological_space H] {I : model_with_corners 𝕜 E H}
{H' : Type*} [topological_space H'] {I' : model_with_corners 𝕜 E' H'}
{N : Type*} [topological_space N] [charted_space H N]
{E'' : Type*} [normed_add_comm_group E''] [normed_space 𝕜 E'']
{H'' : Type*} [topological_space H''] {I'' : model_with_corners 𝕜 E'' H''}
{N' : Type*} [topological_space N'] [charted_space H'' N']
{G : Type*} [comm_monoid G] [topological_space G] [charted_space H' G] [has_smooth_mul I' G]

@[to_additive]
lemma smooth_map.coe_prod {ι} (f : ι → C^∞⟮I, N; I', G⟯) (s : finset ι) :
  ⇑∏ i in s, f i = ∏ i in s, f i :=
map_prod (smooth_map.coe_fn_monoid_hom : C^∞⟮I, N; I', G⟯ →* N → G) f s

end

section

-- This should be in `order.filter.germ` (and the end of the module docstring of that file
-- should be fixed, it currently refers to things that are in the filter_product file).
instance filter.germ.ordered_comm_ring {α : Type*} (l : filter α) (R : Type*) [ordered_comm_ring R] :
  ordered_comm_ring (germ l R) :=
{ add_le_add_left := begin
    rintros ⟨a⟩ ⟨b⟩ hab ⟨c⟩,
    exact eventually.mono hab (λ x hx, add_le_add_left hx _),
  end,
  zero_le_one :=  eventually_of_forall (λ x, zero_le_one),
  mul_nonneg := begin
    rintros ⟨a⟩ ⟨b⟩ ha hb,
    exact eventually.mono (ha.and hb) (λ x hx, mul_nonneg hx.1 hx.2)
  end,
  ..filter.germ.partial_order,
  ..(by apply_instance : comm_ring (germ l R))}

@[simp, to_additive]
lemma germ.coe_prod {α : Type*} (l : filter α) (R : Type*) [comm_monoid R] {ι} (f : ι → α → R)
  (s : finset ι) : ((∏ i in s, f i : α → R) : germ l R) = ∏ i in s, (f i : germ l R) :=
map_prod (germ.coe_mul_hom l : (α → R) →* germ l R) f s


variables
{E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
{E' : Type*} [normed_add_comm_group E'] [normed_space ℝ E']
{H : Type*} [topological_space H] (I : model_with_corners ℝ E H)
{H' : Type*} [topological_space H'] {I' : model_with_corners ℝ E' H'}
{N : Type*} [topological_space N] [charted_space H N]
{E'' : Type*} [normed_add_comm_group E''] [normed_space ℝ E'']
{H'' : Type*} [topological_space H''] {I'' : model_with_corners ℝ E'' H''}
{N' : Type*} [topological_space N'] [charted_space H'' N']
(F : Type*) [normed_add_comm_group F] [normed_space ℝ F]
(G : Type*) [add_comm_group G] [module ℝ G]

def ring_hom.germ_of_cont_mdiff_map (x : N) : C^∞⟮I, N; 𝓘(ℝ), ℝ⟯ →+* germ (𝓝 x) ℝ :=
ring_hom.comp (germ.coe_ring_hom _) smooth_map.coe_fn_ring_hom

def smooth_germ (x : N) : subring (germ (𝓝 x) ℝ) :=
(ring_hom.germ_of_cont_mdiff_map I x).range

instance (x : N) : has_coe C^∞⟮I, N; 𝓘(ℝ), ℝ⟯ (smooth_germ I x) :=
⟨λ f, ⟨(f : N → ℝ), ⟨f, rfl⟩⟩⟩

@[simp]
lemma smooth_germ.coe_coe (f : C^∞⟮I, N; 𝓘(ℝ), ℝ⟯) (x : N) :
  ((f : smooth_germ I x) : (𝓝 x).germ ℝ) = (f  : (𝓝 x).germ ℝ) := rfl

@[simp]
lemma smooth_germ.coe_sum {ι} (f : ι → C^∞⟮I, N; 𝓘(ℝ), ℝ⟯) (s : finset ι) (x : N) :
  ((∑ i in s, f i : C^∞⟮I, N; 𝓘(ℝ), ℝ⟯) : smooth_germ I x) = ∑ i in s, (f i : smooth_germ I x) :=
map_sum (ring_hom.range_restrict (ring_hom.germ_of_cont_mdiff_map I x)) f s

@[simp]
lemma smooth_germ.coe_eq_coe (f g : C^∞⟮I, N; 𝓘(ℝ), ℝ⟯) {x : N} (h : ∀ᶠ y in 𝓝 x, f y = g y) :
  (f : smooth_germ I x) = (g : smooth_germ I x) :=
begin
  ext,
  apply quotient.sound,
  exact h
end

example (x : N) : module (smooth_germ I x) (germ (𝓝 x) G) :=
by apply_instance

example (x : N) : module (germ (𝓝 x) ℝ) (germ (𝓝 x) F) :=
by apply_instance


-- def linear_map.germ_of_cont_mdiff_map (x : N) :
--   C^∞⟮I, N; 𝓘(ℝ, F), F⟯ →ₛₗ[(germ.coe_ring_hom (𝓝 x) : (N → ℝ) →+* germ (𝓝 x) ℝ).comp (pi.const_ring_hom N ℝ)] germ (𝓝 x) F :=
-- sorry -- linear_map.comp (germ.coe_linear_map _) smooth_map.coe_fn_linear_map

/-
def smooth_germ_vec (x : N) : submodule (smooth_germ I x) (germ (𝓝 x) F) :=
-- linear_map.range (linear_map.germ_of_cont_mdiff_map I F x)
{ carrier := {φ : germ (𝓝 x) F | ∃ f : C^∞⟮I, N; 𝓘(ℝ, F), F⟯, φ = (f : N → F)},
  add_mem' := sorry,
  zero_mem' := sorry,
  smul_mem' := sorry }

instance (x : N) : has_coe C^∞⟮I, N; 𝓘(ℝ, F), F⟯ (smooth_germ_vec I F x) :=
⟨λ f, ⟨(f : N → F), ⟨f, rfl⟩⟩⟩

variables {I F}

@[elab_as_eliminator]
lemma smooth_germ_vec.induction_on {x : N} {P : germ (𝓝 x) F → Prop}
  (h : ∀  f : C^∞⟮I, N; 𝓘(ℝ, F), F⟯, P (f : N → F)) :
  ∀ φ ∈ smooth_germ_vec I F x, P φ :=
begin
  rintros _ ⟨f, rfl⟩,
  apply h
end

@[elab_as_eliminator]
lemma smooth_germ.induction_on {x : N} {P : germ (𝓝 x) ℝ → Prop}
  (h : ∀  f : C^∞⟮I, N; 𝓘(ℝ), ℝ⟯, P (f : N → ℝ)) :
  ∀ φ ∈ smooth_germ I x, P φ :=
begin
  rintros _ ⟨f, rfl⟩,
  apply h
end

-- We may also need versions of the above two lemmas for using the coe_to_sort
-- `∀ φ : smooth_germ I x`, maybe even a tactic, but let's wait to see if they are really needed.

lemma convex_smooth_germ_vec (x : N) : convex (smooth_germ I x)
  (smooth_germ_vec I F x : set $ germ (𝓝 x) F) :=
begin
  refine smooth_germ_vec.induction_on _,
  intros f,
  refine smooth_germ_vec.induction_on _,
  rintros g ⟨_, ⟨b, rfl⟩⟩ ⟨_, ⟨c, rfl⟩⟩ hb hc hbc,
  exact ⟨b • f + c • g, rfl⟩,
end
-/

end


section

variables {ι : Type*}
variables {E : Type*} [normed_add_comm_group E] [normed_space ℝ E] [finite_dimensional ℝ E]
  {H : Type*} [topological_space H] {I : model_with_corners ℝ E H} {M : Type*}
  [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
  [sigma_compact_space M] [t2_space M]

variables {F : Type*} [normed_add_comm_group F] [normed_space ℝ F]
variables {G : Type*} [normed_add_comm_group G] [normed_space ℝ G]
  {HG : Type*} [topological_space HG] (IG : model_with_corners ℝ G HG) {N : Type*}
  [topological_space N] [charted_space HG N] [smooth_manifold_with_corners IG N]

local notation `𝓒` := cont_mdiff I 𝓘(ℝ, F)
local notation `𝓒_on` := cont_mdiff_on I 𝓘(ℝ, F)

def smooth_germ.value_order_ring_hom (x : N) : smooth_germ IG x →+*o ℝ :=
filter.germ.value_order_ring_hom.comp $ subring.ordered_subtype _

def smooth_germ.value_ring_hom (x : N) : smooth_germ IG x →+* ℝ :=
filter.germ.value_ring_hom.comp $ subring.subtype _

lemma smooth_germ.value_order_ring_hom_to_ring_hom (x : N) :
  (smooth_germ.value_order_ring_hom IG x).to_ring_hom  = smooth_germ.value_ring_hom IG x :=
rfl

def filter.germ.valueₛₗ {F} [add_comm_monoid F] [module ℝ F] (x : N) :
  germ (𝓝 x) F →ₛₗ[smooth_germ.value_ring_hom IG x] F :=
{ to_fun := filter.germ.value,
  map_smul' := λ φ ψ,  (φ : germ (𝓝 x) ℝ).value_smul ψ,
  .. filter.germ.value_add_hom }

variable (I)

/-- The predicate selecting germs of `cont_mdiff_at` functions.
TODO: merge with the next def that generalizes target space -/
def filter.germ.cont_mdiff_at {x : M} (φ : germ (𝓝 x) F) (n : ℕ∞) : Prop :=
quotient.lift_on' φ (λ f, cont_mdiff_at I 𝓘(ℝ, F) n f x) (λ f g h, propext begin
  split,
  all_goals { refine λ H, H.congr_of_eventually_eq _ },
  exacts [h.symm, h]
end)

-- currently unused
def filter.germ.cont_mdiff_at' {x : M} (φ : germ (𝓝 x) N) (n : ℕ∞) : Prop :=
quotient.lift_on' φ (λ f, cont_mdiff_at I IG n f x) (λ f g h, propext begin
  split,
  all_goals { refine λ H, H.congr_of_eventually_eq _ },
  exacts [h.symm, h]
end)

-- currently unused
def filter.germ.mfderiv {x : M} (φ : germ (𝓝 x) N) :
  tangent_space I x →L[ℝ] tangent_space IG φ.value :=
@quotient.hrec_on _ (germ_setoid (𝓝 x) N)
  (λ φ : germ (𝓝 x) N, tangent_space I x →L[ℝ] tangent_space IG φ.value) φ (λ f, mfderiv I IG f x)
(λ f g hfg, heq_of_eq (eventually_eq.mfderiv_eq hfg : _))

variable {I}
lemma smooth_germ.cont_mdiff_at {x : M} (φ : smooth_germ I x) {n : ℕ∞} :
  (φ : germ (𝓝 x) ℝ).cont_mdiff_at I n :=
by { rcases φ with ⟨_, g, rfl⟩, apply g.smooth.of_le le_top }

lemma filter.germ.cont_mdiff_at.add {x : M} {φ ψ : germ (𝓝 x) F} {n : ℕ∞}
(hφ : φ.cont_mdiff_at I n) (hψ : ψ.cont_mdiff_at I n) :
  (φ + ψ).cont_mdiff_at I n :=
germ.induction_on φ (λ f hf, germ.induction_on ψ (λ g hg, hf.add hg)) hφ hψ

lemma filter.germ.cont_mdiff_at.smul {x : M} {φ : germ (𝓝 x) ℝ} {ψ : germ (𝓝 x) F} {n : ℕ∞}
  (hφ : φ.cont_mdiff_at I n) (hψ : ψ.cont_mdiff_at I n) : (φ • ψ).cont_mdiff_at I n :=
germ.induction_on φ (λ f hf, germ.induction_on ψ (λ g hg, hf.smul hg)) hφ hψ

lemma filter.germ.cont_mdiff_at.sum {x : M} {ι} {s : finset ι} {n : ℕ∞} {f : ι → germ (𝓝 x) F}
(h : ∀ i ∈ s, (f i).cont_mdiff_at I n) : (∑ i in s, f i).cont_mdiff_at I n :=
begin
  classical,
  induction s using finset.induction_on with φ s hφs hs,
  { rw [finset.sum_empty], exact cont_mdiff_at_const },
  simp only [finset.mem_insert, forall_eq_or_imp] at h,
  rw finset.sum_insert hφs,
  exact h.1.add (hs h.2)
end

end

section

variables {E₁ E₂ E₃ E₄ F : Type*}
variables [normed_add_comm_group E₁] [normed_space ℝ E₁] [finite_dimensional ℝ E₁]
variables [normed_add_comm_group E₂] [normed_space ℝ E₂] [finite_dimensional ℝ E₂]
variables [normed_add_comm_group E₃] [normed_space ℝ E₃] [finite_dimensional ℝ E₃]
variables [normed_add_comm_group E₄] [normed_space ℝ E₄] [finite_dimensional ℝ E₄]
variables [normed_add_comm_group F] [normed_space ℝ F]

variables {H₁ M₁ H₂ M₂ H₃ M₃ H₄ M₄ : Type*}
variables [topological_space H₁] (I₁ : model_with_corners ℝ E₁ H₁)
variables [topological_space M₁] [charted_space H₁ M₁] [smooth_manifold_with_corners I₁ M₁]
variables [sigma_compact_space M₁] [t2_space M₁]
variables [topological_space H₂] (I₂ : model_with_corners ℝ E₂ H₂)
variables [topological_space M₂] [charted_space H₂ M₂] [smooth_manifold_with_corners I₂ M₂]
variables [topological_space H₃] (I₃ : model_with_corners ℝ E₃ H₃)
variables [topological_space M₃] [charted_space H₃ M₃] [smooth_manifold_with_corners I₃ M₃]
variables [topological_space H₄] (I₄ : model_with_corners ℝ E₄ H₄)
variables [topological_space M₄] [charted_space H₄ M₄] [smooth_manifold_with_corners I₄ M₄]

local notation `𝓒` := cont_mdiff (I₁.prod I₂) 𝓘(ℝ, F)
local notation `𝓒_on` := cont_mdiff_on (I₁.prod I₂) 𝓘(ℝ, F)

open_locale filter
open function

/- TODO: generalize the next def? -/
def filter.germ.cont_mdiff_at_prod {x : M₁} (φ : germ (𝓝 x) $ M₂ → F) (n : ℕ∞) : Prop :=
quotient.lift_on' φ (λ f, ∀ y : M₂, cont_mdiff_at (I₁.prod I₂) 𝓘(ℝ, F) n (uncurry f) (x, y))
  (λ f g h, propext begin
  change {x' | f x' = g x'} ∈ 𝓝 x at h,
  split,
  all_goals
  { refine λ H y, (H y).congr_of_eventually_eq _,
    clear H,
    replace h : {x' | f x' = g x'} ×ˢ (univ : set M₂) ∈ (𝓝 x) ×ᶠ (𝓝 y) := prod_mem_prod h univ_mem,
    rw ← nhds_prod_eq at h,
    apply mem_of_superset h,
    rintros ⟨x', y'⟩ ⟨(hx' : f x' = g x'), -⟩,
    simp only [mem_set_of_eq, uncurry_apply_pair],
    apply congr_fun, },
  exacts [hx'.symm, hx']
end)

/- potential generalization of the above
def filter.germ.cont_mdiff_at_comp {x : M₁} (φ : germ (𝓝 x) M₂) (n : ℕ∞)
  (g : M₂ → M₃) (h : M₄ → M₁) : Prop :=
quotient.lift_on' φ (λ f, ∀ y ∈ h⁻¹' {x}, cont_mdiff_at I₄ I₃ n (g ∘ f ∘ h) y) (λ f g h, propext begin
  change {x' | f x' = g x'} ∈ 𝓝 x at h,
  split,
  all_goals
  { refine λ H y, (H y).congr_of_eventually_eq _,
    clear H,
    replace h : {x' | f x' = g x'} ×ˢ (univ : set M₂) ∈ (𝓝 x) ×ᶠ (𝓝 y) := prod_mem_prod h univ_mem,
    rw ← nhds_prod_eq at h,
    apply mem_of_superset h,
    rintros ⟨x', y'⟩ ⟨(hx' : f x' = g x'), -⟩,
    simp only [mem_set_of_eq, uncurry_apply_pair],
    apply congr_fun, },
  exacts [hx'.symm, hx']
end)
-/

variables {I₁ I₂}
lemma filter.germ.cont_mdiff_at_prod.add {x : M₁} {φ ψ : germ (𝓝 x) $ M₂ → F} {n : ℕ∞}
  (hφ : φ.cont_mdiff_at_prod I₁ I₂ n) (hψ : ψ.cont_mdiff_at_prod I₁ I₂ n) :
  (φ + ψ).cont_mdiff_at_prod I₁ I₂ n :=
germ.induction_on φ (λ f hf, germ.induction_on ψ (λ g hg y, (hf y).add (hg y))) hφ hψ

lemma filter.germ.cont_mdiff_at_prod.smul {x : M₁} {φ : germ (𝓝 x) $ M₂ → ℝ}
  {ψ : germ (𝓝 x) $ M₂ → F} {n : ℕ∞}
  (hφ : φ.cont_mdiff_at_prod I₁ I₂ n) (hψ : ψ.cont_mdiff_at_prod I₁ I₂ n) :
  (φ • ψ).cont_mdiff_at_prod I₁ I₂ n :=
germ.induction_on φ (λ f hf, germ.induction_on ψ (λ g hg y, (hf y).smul (hg y))) hφ hψ

lemma filter.germ.cont_mdiff_at.smul_prod {x : M₁} {φ : germ (𝓝 x) ℝ}
  {ψ : germ (𝓝 x) $ M₂ → F} {n : ℕ∞}
  (hφ : φ.cont_mdiff_at I₁ n) (hψ : ψ.cont_mdiff_at_prod I₁ I₂ n) :
  (φ • ψ).cont_mdiff_at_prod I₁ I₂ n :=
germ.induction_on φ (λ f hf, germ.induction_on ψ
  (λ g hg y, cont_mdiff_at.smul (cont_mdiff_at.comp _ hf cont_mdiff_at_fst) (hg y))) hφ hψ

lemma filter.germ.cont_mdiff_at_prod.sum {x : M₁} {ι} {s : finset ι} {n : ℕ∞}
  {f : ι → germ (𝓝 x) (M₂ → F)}
  (h : ∀ i ∈ s, (f i).cont_mdiff_at_prod I₁ I₂ n) : (∑ i in s, f i).cont_mdiff_at_prod I₁ I₂ n :=
begin
  classical,
  induction s using finset.induction_on with φ s hφs hs,
  { rw [finset.sum_empty], intro y, exact cont_mdiff_at_const },
  simp only [finset.mem_insert, forall_eq_or_imp] at h,
  rw finset.sum_insert hφs,
  exact h.1.add (hs h.2)
end

end
