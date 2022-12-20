import order.filter.germ
import geometry.manifold.algebra.smooth_functions

noncomputable theory

open filter set
open_locale manifold topological_space

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


def smooth_germ (x : N) : subring (germ (𝓝 x) ℝ) :=
{ carrier := set.range (λ f : C^∞⟮I, N; 𝓘(ℝ), ℝ⟯, ((f : N → ℝ) : (germ (𝓝 x) ℝ))),
  mul_mem' := sorry,
  one_mem' := sorry,
  add_mem' := sorry,
  zero_mem' := sorry,
  neg_mem' := sorry }

def smooth_germ_vec (x : N) : submodule (germ (𝓝 x) ℝ) (germ (𝓝 x) F) :=
{ carrier := {φ : germ (𝓝 x) F | ∃ f : C^∞⟮I, N; 𝓘(ℝ, F), F⟯, φ = (f : N → F)},
  add_mem' := sorry,
  zero_mem' := sorry,
  smul_mem' := sorry }

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
