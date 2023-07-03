import order.filter.germ
import geometry.manifold.algebra.smooth_functions

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



instance smooth_germ.module_fun (x : N) : module (smooth_germ I x) (germ (𝓝 x) G) :=
{ one_smul := sorry,
  mul_smul := sorry,
  smul_zero := sorry,
  smul_add := sorry,
  add_smul := sorry,
  zero_smul := sorry,
  ..(@smooth_germ E _ _ H _ I N _ _ x).has_smul }

def smooth_germ_vec (x : N) : submodule (germ (𝓝 x) ℝ) (germ (𝓝 x) F) :=
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
