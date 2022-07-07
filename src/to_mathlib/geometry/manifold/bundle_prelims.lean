import geometry.manifold.diffeomorph

attribute [ext] topological_fiber_bundle.pretrivialization
attribute [ext] topological_fiber_bundle.trivialization
attribute [ext] topological_vector_bundle.pretrivialization
attribute [ext] topological_vector_bundle.trivialization

open bundle set function
open_locale manifold

-- lemma Exists.const_snd {α : Sort*} {p : Prop} : (∃ x : α, p) → p
-- | ⟨x, h⟩ := h

-- lemma Exists.snd_fst {α : Sort*} {p : Prop} {q : α → Prop} (h : ∃ x, p ∧ q x) : p :=
-- (exists_imp_exists (λ x, and.left) h).const_snd

/- These lemmas have the wrong name -/
lemma id_comp {α β : Sort*} (f : α → β) : id ∘ f = f := rfl -- function.comp.left_id
lemma comp_id {α β : Sort*} (f : α → β) : f ∘ id = f := rfl -- function.comp.right_id
lemma id_apply {α : Sort*} (x : α) : id x = x := rfl -- id.def

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

lemma image2.some_spec_snd (f : α → β → γ) (hx : x ∈ s) (hy : y ∈ t) : ∃ x' ∈ s,
  f x' (image2.some f s t ⟨f x y, mem_image2_of_mem hx hy⟩).2 = f x y :=
⟨(image2.some f s t ⟨f x y, mem_image2_of_mem hx hy⟩).1, subtype.mem _, image2.some_spec f hx hy⟩

end set

namespace local_homeomorph

variables {α β γ δ : Type*} [topological_space α] [topological_space β]
variables [topological_space γ] [topological_space δ] {e : local_homeomorph α β}

lemma trans_apply {e₁ : local_homeomorph α β} {e₂ : local_homeomorph β γ} {x : α} :
  (e₁ ≫ₕ e₂) x = e₂ (e₁ x) :=
rfl

protected lemma ext_iff {e e' : local_homeomorph α β} : e = e' ↔ (∀ x, e x = e' x) ∧
  (∀ x, e.symm x = e'.symm x) ∧ e.source = e'.source :=
⟨by { rintro rfl, exact ⟨λ x, rfl, λ x, rfl, rfl⟩ }, λ h, e.ext e' h.1 h.2.1 h.2.2⟩

lemma image_source_eq_target (e : local_homeomorph α β) : e '' e.source = e.target :=
e.to_local_equiv.image_source_eq_target

lemma source_subset_preimage_target : e.source ⊆ e ⁻¹' e.target :=
e.maps_to

lemma symm_image_target_eq_source (e : local_homeomorph α β) : e.symm '' e.target = e.source :=
e.symm.image_source_eq_target

lemma target_subset_preimage_source : e.target ⊆ e.symm ⁻¹' e.source :=
e.symm_maps_to

example {α : Type*} (p : Prop) [nonempty α] : (α → p) ↔ p :=
by simp only [forall_const]

example {α β : Type*} (p : β → Prop) [h : nonempty α] : (∀ x : β, id x = x) ↔ ∀ x : β, x = x :=
by simp only [id]

@[simp] lemma forall_forall_const {α β : Type*} (p : β → Prop) [h : nonempty α] :
  (∀ x, α → p x) ↔ ∀ x, p x :=
forall_congr $ λ x, forall_const α -- for some reason simp doesn't like this

lemma prod_eq_prod_of_nonempty {e₁ e₁' : local_homeomorph α β} {e₂ e₂' : local_homeomorph γ δ}
  (h : (e₁.prod e₂).source.nonempty) :
  e₁.prod e₂ = e₁'.prod e₂' ↔ e₁ = e₁' ∧ e₂ = e₂' :=
begin
  obtain ⟨⟨x, y⟩, -⟩ := id h,
  have : nonempty α := ⟨x⟩,
  have : nonempty β  := ⟨e₁ x⟩,
  have : nonempty γ := ⟨y⟩,
  haveI : nonempty δ := ⟨e₂ y⟩,
  simp_rw [local_homeomorph.ext_iff, prod_apply, prod_symm_apply, prod_source, prod.ext_iff,
    set.prod_eq_prod_iff_of_nonempty h,
    forall_and_distrib, prod.forall, forall_const, forall_forall_const, and_assoc, and.left_comm]
end

lemma prod_eq_prod_of_nonempty' {e₁ e₁' : local_homeomorph α β} {e₂ e₂' : local_homeomorph γ δ}
  (h : (e₁'.prod e₂').source.nonempty) :
  e₁.prod e₂ = e₁'.prod e₂' ↔ e₁ = e₁' ∧ e₂ = e₂' :=
by rw [eq_comm, prod_eq_prod_of_nonempty h, eq_comm, @eq_comm _ e₂']

end local_homeomorph

namespace topological_fiber_bundle
namespace trivialization


variables {ι : Type*} {B : Type*} {F : Type*} {Z : Type*} {proj : Z → B}
variables [topological_space B] [topological_space F] [topological_space Z]

lemma to_pretrivialization_injective :
  injective (λ e : trivialization F proj, e.to_pretrivialization) :=
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
  injective (λ e : trivialization R F E, e.to_pretrivialization) :=
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

variable (H)
/-- `achart H x` is the chart at `x`, considered as an element of the atlas. -/
def achart (x : M) : atlas H M := ⟨chart_at H x, chart_mem_atlas H x⟩

lemma achart_def (x : M) : achart H x = ⟨chart_at H x, chart_mem_atlas H x⟩ := rfl
@[simp] lemma coe_achart (x : M) : (achart H x : local_homeomorph M H) = chart_at H x := rfl
@[simp] lemma achart_val (x : M) : (achart H x).1 = chart_at H x := rfl

variable {H}

end charted_space

namespace model_with_corners

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {E : Type*} [normed_group E] [normed_space 𝕜 E]
  {H : Type*} [topological_space H] (I : model_with_corners 𝕜 E H)
  {M : Type*} [topological_space M]

lemma injective : injective I :=
left_inverse.injective I.left_inv

lemma preimage_image (s : set H) : I ⁻¹' (I '' s) = s :=
I.injective.preimage_image s

/-- Given a chart `f` on a manifold with corners, `f.extend` is the extended chart to the model
vector space. -/
@[simp, mfld_simps] def _root_.local_homeomorph.extend (f : local_homeomorph M H) : local_equiv M E :=
f.to_local_equiv ≫ I.to_local_equiv

lemma _root_.local_homeomorph.extend_source {f : local_homeomorph M H} :
  (f.extend I).source = f.source :=
by rw [local_homeomorph.extend, local_equiv.trans_source, I.source_eq, preimage_univ, inter_univ]

end model_with_corners

namespace structure_groupoid.local_invariant_properties

variables {H : Type*} {M : Type*} [topological_space H] [topological_space M] [charted_space H M]
{H' : Type*} {M' : Type*} [topological_space H'] [topological_space M'] [charted_space H' M']

variables {G : structure_groupoid H} {G' : structure_groupoid H'}
{e e' : local_homeomorph M H} {f f' : local_homeomorph M' H'}
{P : (H → H') → set H → H → Prop} {g g' : M → M'} {s t : set M} {x : M}
{Q : (H → H) → set H → H → Prop}
variable (hG : G.local_invariant_prop G' P)
include hG

-- lemma lift_prop_within_at_indep_chart_target [has_groupoid M' G']
--   (hf : f ∈ G'.maximal_atlas M') (xf : g x ∈ f.source) :
--   lift_prop_within_at P g s x ↔
--     /-continuous_within_at g s x ∧-/
--     lift_prop_within_at P (f ∘ g) s x :=
-- begin
--   split,
--   { intro hg,
--     refine ⟨(f.continuous_at _).comp_continuous_within_at hg.1, _⟩,  },
--   { }
-- end

-- lemma lift_prop_within_at_indep_chart_source [has_groupoid M G] [has_groupoid M' G']
--   (he : e ∈ G.maximal_atlas M) (xe : x ∈ e.source)
--   (hf : f ∈ G'.maximal_atlas M') (xf : g x ∈ f.source) :
--   lift_prop_within_at P g s x ↔
--     continuous_within_at g s x ∧ P (f ∘ g ∘ e.symm)
--       (e.target ∩ e.symm ⁻¹' (s ∩ g⁻¹' f.source)) (e x) :=
-- sorry

end structure_groupoid.local_invariant_properties

section smooth_manifold_with_corners
open smooth_manifold_with_corners

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {E : Type*} [normed_group E] [normed_space 𝕜 E]
  {E' : Type*} [normed_group E'] [normed_space 𝕜 E']
  {H : Type*} [topological_space H] {I : model_with_corners 𝕜 E H}
  {H' : Type*} [topological_space H'] {I' : model_with_corners 𝕜 E' H'}
  {M : Type*} [topological_space M] [charted_space H M]
  {M' : Type*} [topological_space M'] [charted_space H' M']
variables {f : M → M'} {m n : with_top ℕ} {s : set M} {x : M}


lemma smooth_manifold_with_corners.subset_maximal_atlas [smooth_manifold_with_corners I M] :
  atlas H M ⊆ maximal_atlas I M :=
structure_groupoid.subset_maximal_atlas _

lemma cont_mdiff_at_iff_target
  [smooth_manifold_with_corners I' M']
  {x : M} :
  cont_mdiff_at I I' n f x ↔
    continuous_at f x ∧ cont_mdiff_at I 𝓘(𝕜, E') n (ext_chart_at I' (f x) ∘ f) x :=
begin
  rw [cont_mdiff_at, cont_mdiff_at, cont_mdiff_within_at_iff_target, continuous_within_at_univ,
    univ_inter],
  sorry -- refl after #15116 ?
end

lemma cont_mdiff_within_at_iff_target_of_mem_source_chart_at
  [smooth_manifold_with_corners I' M']
  {x : M} {y : M'} (hy : f x ∈ (chart_at H' y).source) :
  cont_mdiff_within_at I I' n f s x ↔ continuous_within_at f s x ∧
    cont_mdiff_within_at I 𝓘(𝕜, E') n (ext_chart_at I' y ∘ f) s x :=
begin
  sorry -- easier after #15116
  -- combination of `cont_mdiff_within_at_iff_target` and `cont_mdiff_within_at_iff_of_mem_source`
end

lemma cont_mdiff_at_iff_target_of_mem_source_chart_at
  [smooth_manifold_with_corners I' M']
  {x : M} {y : M'} (hy : f x ∈ (chart_at H' y).source) :
  cont_mdiff_at I I' n f x ↔ continuous_at f x ∧
    cont_mdiff_at I 𝓘(𝕜, E') n (ext_chart_at I' y ∘ f) x :=
begin
  rw [cont_mdiff_at, cont_mdiff_within_at_iff_target_of_mem_source_chart_at hy,
    continuous_within_at_univ, cont_mdiff_at],
  apply_instance
end

variables (I)

lemma cont_diff_on_coord_change [smooth_manifold_with_corners I M]
  {e e' : local_homeomorph M H} (h : e ∈ atlas H M) (h' : e' ∈ atlas H M) :
  cont_diff_on 𝕜 ⊤ (I ∘ (e.symm ≫ₕ e') ∘ I.symm) (I.symm ⁻¹' (e.symm ≫ₕ e').source ∩ range I) :=
(has_groupoid.compatible (cont_diff_groupoid ⊤ I) h h').1

lemma cont_diff_on_coord_change_symm [smooth_manifold_with_corners I M]
  {e e' : local_homeomorph M H} (h : e ∈ atlas H M) (h' : e' ∈ atlas H M) :
  cont_diff_on 𝕜 ⊤ (I ∘ (e.symm ≫ₕ e') ∘ I.symm) (I.symm ⁻¹' (e.symm ≫ₕ e').source ∩ range I) :=
(has_groupoid.compatible (cont_diff_groupoid ⊤ I) h h').1

variables {I} [smooth_manifold_with_corners I M] [smooth_manifold_with_corners I' M']

/-- One can reformulate smoothness within a set at a point as continuity within this set at this
point, and smoothness in any chart containing that point. -/
lemma cont_mdiff_within_at_iff_of_mem_source
  {c : local_homeomorph M H} (hc : c ∈ maximal_atlas I M)
  {d : local_homeomorph M' H'} (hd : d ∈ maximal_atlas I' M')
  (hx : x ∈ c.source) (hy : f x ∈ d.source) :
  cont_mdiff_within_at I I' n f s x ↔ continuous_within_at f s x ∧
    cont_diff_within_at 𝕜 n (d.extend I' ∘ f ∘ (c.extend I).symm)
    ((c.extend I).target ∩ (c.extend I).symm ⁻¹' (s ∩ f ⁻¹' (d.extend I').source))
    (c.extend I x) :=
begin
  refine ((cont_diff_within_at_local_invariant_prop I I' n).lift_prop_within_at_indep_chart
    hc hx hd hy).trans _,
  rw [cont_diff_within_at_prop, iff_eq_eq],
  congr' 2,
  mfld_set_tac
end

/-- One can reformulate smoothness on a set as continuity on this set, and smoothness in two given
charts that contain the set. -/
lemma cont_mdiff_on_iff_of_subset_source
  {c : local_homeomorph M H} (hc : c ∈ maximal_atlas I M)
  {d : local_homeomorph M' H'} (hd : d ∈ maximal_atlas I' M')
  (hs : s ⊆ c.source) (h2s : f '' s ⊆ d.source) :
  cont_mdiff_on I I' n f s ↔ continuous_on f s ∧
    cont_diff_on 𝕜 n (d.extend I' ∘ f ∘ (c.extend I).symm)
    ((c.extend I).target ∩
      (c.extend I).symm ⁻¹' (s ∩ f ⁻¹' (d.extend I').source)) :=
begin -- todo: cleanup
  split,
  { refine λ H, ⟨H.continuous_on, _⟩,
    rintro x' ⟨h1x', h2x', h3x'⟩,
    rw [mem_preimage] at h3x',
    convert ((cont_mdiff_within_at_iff_of_mem_source hc hd _ _).mp (H _ h2x')).2,
    rw [local_equiv.right_inv _ h1x'],
    rw [← local_homeomorph.extend_source I, ← local_equiv.symm_target],
    rw [← local_equiv.symm_source] at h1x',
    apply local_equiv.maps_to _ h1x',
    rwa [local_homeomorph.extend_source] at h3x' },
  { rintro ⟨h1, h2⟩ x' hx',
    refine (cont_mdiff_within_at_iff_of_mem_source hc hd (hs hx') (h2s $ mem_image_of_mem f hx')).mpr
      ⟨h1.continuous_within_at hx', _⟩,
    apply h2,
    simp only [hx', hs hx', h2s (mem_image_of_mem f hx'), local_homeomorph.extend,
      local_equiv.coe_trans, model_with_corners.to_local_equiv_coe, local_homeomorph.coe_coe,
      comp_app, local_equiv.trans_target, model_with_corners.target_eq,
    model_with_corners.to_local_equiv_coe_symm, local_equiv.coe_trans_symm,
    local_homeomorph.coe_coe_symm,
    local_equiv.trans_source, model_with_corners.source_eq, preimage_univ, inter_univ, mem_inter_eq,
    mem_range_self,
    mem_preimage, model_with_corners.left_inv, local_homeomorph.map_source, and_self,
    local_homeomorph.left_inv] }
end

-- rename or remove depending on whether this is useful
lemma cont_mdiff_on_iff_of_subset_source_chart_at {x : M} {y : M'}
  (hs : s ⊆ (chart_at H x).source)
  (h2s : f '' s ⊆ (chart_at H' y).source) :
  cont_mdiff_on I I' n f s ↔ continuous_on f s ∧
    cont_diff_on 𝕜 n (ext_chart_at I' y ∘ f ∘ (ext_chart_at I x).symm)
    ((ext_chart_at I x).target ∩
      (ext_chart_at I x).symm ⁻¹' (s ∩ f ⁻¹' (ext_chart_at I' y).source)) :=
cont_mdiff_on_iff_of_subset_source (structure_groupoid.chart_mem_maximal_atlas _ x)
  (structure_groupoid.chart_mem_maximal_atlas _ y) hs h2s

lemma smooth_on_iff_of_subset_source
  {c : local_homeomorph M H} (hc : c ∈ maximal_atlas I M)
  {d : local_homeomorph M' H'} (hd : d ∈ maximal_atlas I' M')
  (hs : s ⊆ c.source) (h2s : f '' s ⊆ d.source) :
  smooth_on I I' f s ↔ continuous_on f s ∧
    cont_diff_on 𝕜 ⊤ (d.extend I' ∘ f ∘ (c.extend I).symm)
    ((c.extend I).target ∩
      (c.extend I).symm ⁻¹' (s ∩ f ⁻¹' (d.extend I').source)) :=
cont_mdiff_on_iff_of_subset_source hc hd hs h2s

variables {F G F' : Type*}
variables [normed_group F] [normed_group G] [normed_group F']
variables [normed_space 𝕜 F] [normed_space 𝕜 G] [normed_space 𝕜 F']

lemma cont_diff_within_at.comp_cont_mdiff_within_at {g : F → G} {f : M → F} {s : set M} {t : set F}
  {x : M}
  (hg : cont_diff_within_at 𝕜 n g t (f x))
  (hf : cont_mdiff_within_at I 𝓘(𝕜, F) n f s x) (h : s ⊆ f ⁻¹' t) :
  cont_mdiff_within_at I 𝓘(𝕜, G) n (g ∘ f) s x :=
begin
  rw cont_mdiff_within_at_iff'' at *,
  refine ⟨hg.continuous_within_at.comp hf.1 h, _⟩,
  -- simp_rw [written_in_ext_chart_at, ext_chart_model_space_eq_id, local_equiv.refl_coe,
  --   id_comp] at hf ⊢,
  rw [← (ext_chart_at I x).left_inv (mem_ext_chart_source I x)] at hg,
  apply cont_diff_within_at.comp _ (by exact hg) hf.2 _,
  -- rw [@preimage_comp _ _ _ _ f],
  exact (inter_subset_left _ _).trans (preimage_mono h)
end

lemma cont_diff_at.comp_cont_mdiff_at {g : F → G} {f : M → F} {x : M}
  (hg : cont_diff_at 𝕜 n g (f x)) (hf : cont_mdiff_at I 𝓘(𝕜, F) n f x) :
  cont_mdiff_at I 𝓘(𝕜, G) n (g ∘ f) x :=
hg.comp_cont_mdiff_within_at hf subset.rfl

lemma cont_diff.comp_cont_mdiff {g : F → G} {f : M → F}
  (hg : cont_diff 𝕜 n g) (hf : cont_mdiff I 𝓘(𝕜, F) n f) :
  cont_mdiff I 𝓘(𝕜, G) n (g ∘ f) :=
λ x, hg.cont_diff_at.comp_cont_mdiff_at (hf x)

-- lemma cont_mdiff_within_at.clm_comp {g : M → F →L[𝕜] G} {f : M → E →L[𝕜] F} {s : set M} {x : M}
--   (hg : cont_mdiff_within_at I 𝓘(𝕜, F →L[𝕜] G) n g s x)
--   (hf : cont_mdiff_within_at I 𝓘(𝕜, E →L[𝕜] F) n f s x) :
--   cont_mdiff_within_at I 𝓘(𝕜, E →L[𝕜] G) n (λ x, (g x).comp (f x)) s x :=
-- sorry

-- the following proof takes very long in pure term mode
lemma cont_mdiff_at.clm_comp {g : M → F →L[𝕜] G} {f : M → F' →L[𝕜] F} {x : M}
  (hg : cont_mdiff_at I 𝓘(𝕜, F →L[𝕜] G) n g x) (hf : cont_mdiff_at I 𝓘(𝕜, F' →L[𝕜] F) n f x) :
  cont_mdiff_at I 𝓘(𝕜, F' →L[𝕜] G) n (λ x, (g x).comp (f x)) x :=
@cont_diff_at.comp_cont_mdiff_at 𝕜 _ E _ _ H _ I M _ _ n _ ((F →L[𝕜] G) × (F' →L[𝕜] F))
  _ _ _ _ _
  (λ x, continuous_linear_map.comp x.1 x.2) (λ x, (g x, f x)) x
  (by { apply cont_diff.cont_diff_at, apply is_bounded_bilinear_map.cont_diff, exact is_bounded_bilinear_map_comp,  }) (hg.prod_mk_space hf)

lemma cont_mdiff.clm_comp {g : M → F →L[𝕜] G} {f : M → F' →L[𝕜] F}
  (hg : cont_mdiff I 𝓘(𝕜, F →L[𝕜] G) n g) (hf : cont_mdiff I 𝓘(𝕜, F' →L[𝕜] F) n f) :
  cont_mdiff I 𝓘(𝕜, F' →L[𝕜] G) n (λ x, (g x).comp (f x)) :=
λ x, (hg x).clm_comp (hf x)

lemma cont_mdiff.mfderiv' {f : M → M'}
  (hf : cont_mdiff I I' n f) (hmn : m + 1 ≤ n) :
  cont_mdiff_at I 𝓘(𝕜, E →L[𝕜] E') m
  (λ x', ((tangent_bundle_core I' M').coord_change (achart H' (f x')) (achart H' (f x)) $
    chart_at H' (f x') (f x')).comp $
    (mfderiv I I' f x').comp $
    (tangent_bundle_core I M).coord_change (achart H x) (achart H x') $ chart_at H x x') x :=
sorry

end smooth_manifold_with_corners

namespace local_equiv

variables {α β γ : Type*}

/-- This might be useful to formulate many "composition of `f` and `g` is given by `h`" notions,
like `coord_change_comp` in various structures. -/
def eq_on_common_source (e e' : local_equiv α β) : Prop :=
∀ x ∈ e.source ∩ e'.source, e x = e' x

end local_equiv


namespace basic_smooth_vector_bundle_core

variables {𝕜 B B' M VB VB' VM HB HB' HM : Type*}
variables [nondiscrete_normed_field 𝕜]
variables [normed_group VB] [normed_space 𝕜 VB] [normed_group VB'] [normed_space 𝕜 VB']
variables [normed_group VM] [normed_space 𝕜 VM]
variables [topological_space HB] [topological_space HB'] [topological_space HM]
variables {IB : model_with_corners 𝕜 VB HB} {IB' : model_with_corners 𝕜 VB' HB'}
variables {IM : model_with_corners 𝕜 VM HM}
variables {F F' : Type*}
variables [normed_group F] [normed_space 𝕜 F] [normed_group F'] [normed_space 𝕜 F']
variables [topological_space B] [charted_space HB B] [smooth_manifold_with_corners IB B]
variables [topological_space B'] [charted_space HB' B'] [smooth_manifold_with_corners IB' B']
variables [topological_space M] [charted_space HM M] [smooth_manifold_with_corners IM M]
variables (f : C^∞⟮IB', B'; IB, B⟯) -- todo: define cont_mdiff_map_class
variables (Z : basic_smooth_vector_bundle_core IB B F)
variables (Z' : basic_smooth_vector_bundle_core IB B F')

end basic_smooth_vector_bundle_core

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
