import to_mathlib.topology.vector_bundle.hom
import geometry.manifold.diffeomorph

attribute [ext] topological_fiber_bundle.pretrivialization
attribute [ext] topological_fiber_bundle.trivialization
attribute [ext] topological_vector_bundle.pretrivialization
attribute [ext] topological_vector_bundle.trivialization

open bundle set
open_locale manifold

lemma Exists.const_snd {α : Sort*} {p : Prop} : (∃ x : α, p) → p
| ⟨x, h⟩ := h

-- lemma Exists.snd_fst {α : Sort*} {p : Prop} {q : α → Prop} (h : ∃ x, p ∧ q x) : p :=
-- (exists_imp_exists (λ x, and.left) h).const_snd

namespace set

variables {α β γ δ : Type*} {f : α → β → γ} {s s₁ : set α} {t t₁ : set β} {x : α} {y : β}

lemma prod_eq_prod_iff_of_nonempty (h : (s ×ˢ t : set _).nonempty) :
  s ×ˢ t = s₁ ×ˢ t₁ ↔ s = s₁ ∧ t = t₁ :=
begin
  split,
  { intro heq,
    have h₁ : (s₁ ×ˢ t₁ : set _).nonempty, { rwa [← heq] },
    rw [prod_nonempty_iff] at h h₁,
    rw [← fst_image_prod s h.2, ← fst_image_prod s₁ h₁.2, heq, eq_self_iff_true, true_and,
        ← snd_image_prod h.1 t, ← snd_image_prod h₁.1 t₁, heq] },
  { rintro ⟨rfl, rfl⟩, refl }
end

lemma prod_eq_prod_iff : s ×ˢ t = s₁ ×ˢ t₁ ↔ s = s₁ ∧ t = t₁ ∨ (s = ∅ ∨ t = ∅) ∧
  (s₁ = ∅ ∨ t₁ = ∅) :=
begin
  symmetry,
  cases eq_empty_or_nonempty (s ×ˢ t) with h h,
  { simp_rw [h, @eq_comm _ ∅, prod_eq_empty_iff, prod_eq_empty_iff.mp h, true_and,
      or_iff_right_iff_imp],
    rintro ⟨rfl, rfl⟩, exact prod_eq_empty_iff.mp h },
  rw [prod_eq_prod_iff_of_nonempty h],
  rw [← ne_empty_iff_nonempty, ne.def, prod_eq_empty_iff] at h,
  simp_rw [h, false_and, or_false],
end

-- def mk_image2 (f : α → β → γ) (x : s) (y : t) : image2 f s t :=
-- ⟨f x y, mem_image2_of_mem x.2 y.2⟩

lemma image2.some_prop (z : image2 f s t) : ∃ (y : s × t), f y.1 y.2 = z :=
let ⟨_, ⟨x, y, hx, hy, rfl⟩⟩ := z in ⟨⟨⟨x, hx⟩, ⟨y, hy⟩⟩, rfl⟩

noncomputable def image2.some (f : α → β → γ) (s : set α) (t : set β) (z : image2 f s t) : s × t :=
classical.some (image2.some_prop z)

lemma image2.some_spec (f : α → β → γ) (hx : x ∈ s) (hy : y ∈ t) :
  (λ x : s × t, f x.1 x.2) (image2.some f s t ⟨f x y, mem_image2_of_mem hx hy⟩) = f x y :=
classical.some_spec (image2.some_prop ⟨f x y, mem_image2_of_mem hx hy⟩)

lemma image2.some_spec_fst (f : α → β → γ) (hx : x ∈ s) (hy : y ∈ t) : ∃ y' ∈ t,
  f (image2.some f s t ⟨f x y, mem_image2_of_mem hx hy⟩).1 y' = f x y :=
⟨(image2.some f s t ⟨f x y, mem_image2_of_mem hx hy⟩).2, subtype.mem _, image2.some_spec f hx hy⟩

end set

namespace local_homeomorph

variables {α β γ δ : Type*} [topological_space α] [topological_space β]
variables [topological_space γ] [topological_space δ]

variables (α β)

-- lemma prod_eq {e₁ e₁' : local_homeomorph α β} {e₂ e₂' : local_homeomorph γ δ} :
--   e₁.prod e₂ = e₁'.prod e₂' →
--   (e₁ = e₁' ∨ (e₁.source = ∅ ∧ e₂.source = ∅)) ∧ (e₂ = e₂' ∨ (e₁.source = ∅ ∧ e₂.source = ∅)) :=
-- begin
--   intro h,
--   have := congr_arg (λ e : local_homeomorph _ _, e.source) h,
--   simp_rw [prod_source, set.prod_eq] at this,
-- end

end local_homeomorph

namespace topological_fiber_bundle
namespace trivialization


variables {ι : Type*} {B : Type*} {F : Type*} {Z : Type*} {proj : Z → B}
variables [topological_space B] [topological_space F] [topological_space Z]

lemma to_pretrivialization_injective :
  function.injective (λ e : trivialization F proj, e.to_pretrivialization) :=
by { intros e e', rw [pretrivialization.ext_iff, trivialization.ext_iff,
  ← local_homeomorph.to_local_equiv_injective.eq_iff], exact id }

end trivialization
end topological_fiber_bundle

namespace topological_vector_bundle

variables {R : Type*} {B : Type*} {F : Type*} {E : B → Type*}
variables [nondiscrete_normed_field R] [∀ x, add_comm_monoid (E x)] [∀ x, module R (E x)]
  [normed_group F] [normed_space R F] [topological_space B]
  [topological_space (total_space E)]

namespace trivialization

lemma to_pretrivialization_injective :
  function.injective (λ e : trivialization R F E, e.to_pretrivialization) :=
by { intros e e', rw [pretrivialization.ext_iff, trivialization.ext_iff,
  ← topological_fiber_bundle.trivialization.to_pretrivialization_injective.eq_iff], exact id }

end trivialization

variables {HB : Type*} [topological_space HB]

/-- The chart of the total space by a bundle given by a trivialization along a chart of the base
  space. -/
def chart_at (e : trivialization R F E) (f : local_homeomorph B HB) :
  local_homeomorph (total_space E) (model_prod HB F) :=
e.to_local_homeomorph.trans $ f.prod $ local_homeomorph.refl F

variables (R F E) [∀ x, topological_space (E x)]

/-- The total space of a topological vector bundle forms a charted space.
Currently not an instance, because it creates the metavariable `R`, but it might be fine to change
this. -/
def total_space.to_charted_space [topological_vector_bundle R F E] [charted_space HB B] :
  charted_space (model_prod HB F) (total_space E) :=
{ atlas := image2 chart_at (trivialization_atlas R F E) (atlas HB B),
  chart_at := λ x, chart_at (trivialization_at R F E x.proj) (charted_space.chart_at HB x.proj),
  mem_chart_source := λ x, by simp only [chart_at, trivialization.mem_source,
    mem_base_set_trivialization_at R F E x.proj] with mfld_simps,
  chart_mem_atlas := λ x, mem_image2_of_mem (trivialization_mem_atlas R F E x.proj)
    (chart_mem_atlas HB x.proj) }

end topological_vector_bundle

section charted_space

variables {M H : Type*} [topological_space M] [topological_space H] [charted_space H M]
  (G : structure_groupoid H)

lemma structure_groupoid.subset_maximal_atlas [has_groupoid M G] : atlas H M ⊆ G.maximal_atlas M :=
λ e he e' he', ⟨G.compatible he he', G.compatible he' he⟩

end charted_space


namespace smooth_manifold_with_corners

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {E : Type*} [normed_group E] [normed_space 𝕜 E]
  {H : Type*} [topological_space H] {I : model_with_corners 𝕜 E H}
  {M : Type*} [topological_space M] [charted_space H M]

lemma subset_maximal_atlas [smooth_manifold_with_corners I M] : atlas H M ⊆ maximal_atlas I M :=
structure_groupoid.subset_maximal_atlas _

end smooth_manifold_with_corners

namespace local_equiv

variables {α β γ : Type*}

/-- This might be useful to formulate many "composition of `f` and `g` is given by `h`" notions,
like `coord_change_comp` in various structures. -/
def eq_on_common_source (e e' : local_equiv α β) : Prop :=
∀ x ∈ e.source ∩ e'.source, e x = e' x

end local_equiv

section maps

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{E' : Type*} [normed_group E'] [normed_space 𝕜 E']
{F : Type*} [normed_group F] [normed_space 𝕜 F]
{H : Type*} [topological_space H]
{H' : Type*} [topological_space H']
{G : Type*} [topological_space G]
{G' : Type*} [topological_space G']
{I : model_with_corners 𝕜 E H} {I' : model_with_corners 𝕜 E' H'}
{J : model_with_corners 𝕜 F G} {J' : model_with_corners 𝕜 F G'}

variables {M : Type*} [topological_space M] [charted_space H M]
{M' : Type*} [topological_space M'] [charted_space H' M']
{N : Type*} [topological_space N] [charted_space G N]
{N' : Type*} [topological_space N'] [charted_space G' N']
{n : with_top ℕ}
(f : C^∞⟮I, M; J, N⟯)

namespace cont_mdiff_map

instance : continuous_map_class C^∞⟮I, M; J, N⟯ M N :=
{ coe := coe_fn,
  coe_injective' := coe_inj,
  map_continuous := λ f, f.cont_mdiff_to_fun.continuous }

/-- The first projection of a product, as a smooth map. -/
def fst : C^∞⟮I.prod I', M × M'; I, M⟯ := ⟨prod.fst, cont_mdiff_fst⟩

/-- The second projection of a product, as a smooth map. -/
def snd : C^∞⟮I.prod I', M × M'; I', M'⟯ := ⟨prod.snd, cont_mdiff_snd⟩

end cont_mdiff_map

namespace diffeomorph

instance : continuous_map_class (M ≃ₘ⟮I, J⟯ N) M N :=
{ coe := coe_fn,
  coe_injective' := coe_fn_injective,
  map_continuous := λ f, f.continuous }

end diffeomorph

end maps
